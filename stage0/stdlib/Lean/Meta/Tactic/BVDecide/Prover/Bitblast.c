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
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* lean_io_mono_nanos_now();
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
lean_object* lean_io_get_num_heartbeats();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_nativeEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_addAndCompile(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
uint16_t l_Lean_OptionFlags_ofOptions(lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
uint16_t lean_uint16_land(uint16_t, uint16_t);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__2;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "compiler"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "extract_closed"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__3_value),LEAN_SCALAR_PTR_LITERAL(25, 100, 103, 244, 164, 70, 204, 201)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__4_value),LEAN_SCALAR_PTR_LITERAL(157, 223, 55, 216, 54, 195, 10, 164)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__5_value;
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(lean_object* v_opts_1_, lean_object* v_opt_2_){
_start:
{
lean_object* v_name_3_; lean_object* v_defValue_4_; lean_object* v_map_5_; lean_object* v___x_6_; 
v_name_3_ = lean_ctor_get(v_opt_2_, 0);
v_defValue_4_ = lean_ctor_get(v_opt_2_, 1);
v_map_5_ = lean_ctor_get(v_opts_1_, 0);
v___x_6_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_5_, v_name_3_);
if (lean_obj_tag(v___x_6_) == 0)
{
lean_inc(v_defValue_4_);
return v_defValue_4_;
}
else
{
lean_object* v_val_7_; 
v_val_7_ = lean_ctor_get(v___x_6_, 0);
lean_inc(v_val_7_);
lean_dec_ref_known(v___x_6_, 1);
if (lean_obj_tag(v_val_7_) == 3)
{
lean_object* v_v_8_; 
v_v_8_ = lean_ctor_get(v_val_7_, 0);
lean_inc(v_v_8_);
lean_dec_ref_known(v_val_7_, 1);
return v_v_8_;
}
else
{
lean_dec(v_val_7_);
lean_inc(v_defValue_4_);
return v_defValue_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___boxed(lean_object* v_opts_9_, lean_object* v_opt_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_9_, v_opt_10_);
lean_dec_ref(v_opt_10_);
lean_dec_ref(v_opts_9_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(lean_object* v_o_15_, lean_object* v_k_16_, uint8_t v_v_17_){
_start:
{
lean_object* v_map_18_; uint8_t v_hasTrace_19_; lean_object* v___x_21_; uint8_t v_isShared_22_; uint8_t v_isSharedCheck_33_; 
v_map_18_ = lean_ctor_get(v_o_15_, 0);
v_hasTrace_19_ = lean_ctor_get_uint8(v_o_15_, sizeof(void*)*1);
v_isSharedCheck_33_ = !lean_is_exclusive(v_o_15_);
if (v_isSharedCheck_33_ == 0)
{
v___x_21_ = v_o_15_;
v_isShared_22_ = v_isSharedCheck_33_;
goto v_resetjp_20_;
}
else
{
lean_inc(v_map_18_);
lean_dec(v_o_15_);
v___x_21_ = lean_box(0);
v_isShared_22_ = v_isSharedCheck_33_;
goto v_resetjp_20_;
}
v_resetjp_20_:
{
lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_23_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_23_, 0, v_v_17_);
lean_inc(v_k_16_);
v___x_24_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_16_, v___x_23_, v_map_18_);
if (v_hasTrace_19_ == 0)
{
lean_object* v___x_25_; uint8_t v___x_26_; lean_object* v___x_28_; 
v___x_25_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
v___x_26_ = l_Lean_Name_isPrefixOf(v___x_25_, v_k_16_);
lean_dec(v_k_16_);
if (v_isShared_22_ == 0)
{
lean_ctor_set(v___x_21_, 0, v___x_24_);
v___x_28_ = v___x_21_;
goto v_reusejp_27_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v___x_24_);
v___x_28_ = v_reuseFailAlloc_29_;
goto v_reusejp_27_;
}
v_reusejp_27_:
{
lean_ctor_set_uint8(v___x_28_, sizeof(void*)*1, v___x_26_);
return v___x_28_;
}
}
else
{
lean_object* v___x_31_; 
lean_dec(v_k_16_);
if (v_isShared_22_ == 0)
{
lean_ctor_set(v___x_21_, 0, v___x_24_);
v___x_31_ = v___x_21_;
goto v_reusejp_30_;
}
else
{
lean_object* v_reuseFailAlloc_32_; 
v_reuseFailAlloc_32_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_32_, 0, v___x_24_);
lean_ctor_set_uint8(v_reuseFailAlloc_32_, sizeof(void*)*1, v_hasTrace_19_);
v___x_31_ = v_reuseFailAlloc_32_;
goto v_reusejp_30_;
}
v_reusejp_30_:
{
return v___x_31_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___boxed(lean_object* v_o_34_, lean_object* v_k_35_, lean_object* v_v_36_){
_start:
{
uint8_t v_v_boxed_37_; lean_object* v_res_38_; 
v_v_boxed_37_ = lean_unbox(v_v_36_);
v_res_38_ = l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_o_34_, v_k_35_, v_v_boxed_37_);
return v_res_38_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__0(void){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_39_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__1(void){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_40_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__0);
v___x_41_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_41_, 0, v___x_40_);
return v___x_41_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__2(void){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__1);
v___x_43_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_43_, 0, v___x_42_);
lean_ctor_set(v___x_43_, 1, v___x_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(lean_object* v_name_49_, lean_object* v_value_50_, lean_object* v_type_51_, lean_object* v_a_52_, lean_object* v_a_53_){
_start:
{
lean_object* v_toCold_55_; lean_object* v_currRecDepth_56_; lean_object* v_ref_57_; uint8_t v_suppressElabErrors_58_; uint8_t v_isRecordingDeps_59_; lean_object* v_fileName_60_; lean_object* v_fileMap_61_; lean_object* v_options_62_; lean_object* v_currNamespace_63_; lean_object* v_openDecls_64_; lean_object* v_initHeartbeats_65_; lean_object* v_maxHeartbeats_66_; lean_object* v_quotContext_67_; lean_object* v_currMacroScope_68_; lean_object* v_cancelTk_x3f_69_; lean_object* v_inheritedTraceOptions_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; uint8_t v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; uint8_t v___x_78_; uint8_t v___x_79_; uint16_t v___y_81_; lean_object* v___y_82_; lean_object* v_fileName_83_; lean_object* v_fileMap_84_; lean_object* v_currNamespace_85_; lean_object* v_openDecls_86_; lean_object* v_initHeartbeats_87_; lean_object* v_maxHeartbeats_88_; lean_object* v_quotContext_89_; lean_object* v_currMacroScope_90_; lean_object* v_cancelTk_x3f_91_; lean_object* v_inheritedTraceOptions_92_; lean_object* v_currRecDepth_93_; lean_object* v_ref_94_; uint8_t v_suppressElabErrors_95_; uint8_t v_isRecordingDeps_96_; lean_object* v___y_97_; uint16_t v___y_104_; uint8_t v___y_105_; lean_object* v___y_106_; lean_object* v___y_129_; 
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
if (v_isRecordingDeps_59_ == 0)
{
lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_138_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__5));
lean_inc_ref(v_options_62_);
v___x_139_ = l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_62_, v___x_138_, v_isRecordingDeps_59_);
v___y_129_ = v___x_139_;
goto v___jp_128_;
}
else
{
lean_object* v___x_140_; 
lean_inc_ref(v_options_62_);
v___x_140_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_62_);
v___y_129_ = v___x_140_;
goto v___jp_128_;
}
v___jp_80_:
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_98_ = l_Lean_maxRecDepth;
v___x_99_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v___y_82_, v___x_98_);
v___x_100_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_100_, 0, v_fileName_83_);
lean_ctor_set(v___x_100_, 1, v_fileMap_84_);
lean_ctor_set(v___x_100_, 2, v___y_82_);
lean_ctor_set(v___x_100_, 3, v___x_99_);
lean_ctor_set(v___x_100_, 4, v_currNamespace_85_);
lean_ctor_set(v___x_100_, 5, v_openDecls_86_);
lean_ctor_set(v___x_100_, 6, v_initHeartbeats_87_);
lean_ctor_set(v___x_100_, 7, v_maxHeartbeats_88_);
lean_ctor_set(v___x_100_, 8, v_quotContext_89_);
lean_ctor_set(v___x_100_, 9, v_currMacroScope_90_);
lean_ctor_set(v___x_100_, 10, v_cancelTk_x3f_91_);
lean_ctor_set(v___x_100_, 11, v_inheritedTraceOptions_92_);
lean_inc(v_ref_94_);
lean_inc(v_currRecDepth_93_);
v___x_101_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_101_, 0, v___x_100_);
lean_ctor_set(v___x_101_, 1, v_currRecDepth_93_);
lean_ctor_set(v___x_101_, 2, v_ref_94_);
lean_ctor_set_uint16(v___x_101_, sizeof(void*)*3, v___y_81_);
lean_ctor_set_uint8(v___x_101_, sizeof(void*)*3 + 2, v_suppressElabErrors_95_);
lean_ctor_set_uint8(v___x_101_, sizeof(void*)*3 + 3, v_isRecordingDeps_96_);
v___x_102_ = l_Lean_addAndCompile(v___x_77_, v___x_78_, v___x_79_, v___x_101_, v___y_97_);
lean_dec_ref_known(v___x_101_, 3);
return v___x_102_;
}
v___jp_103_:
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
v___x_120_ = l_Lean_Kernel_enableDiag(v_env_108_, v___y_105_);
v___x_121_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__2);
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
v___y_81_ = v___y_104_;
v___y_82_ = v___y_106_;
v_fileName_83_ = v_fileName_60_;
v_fileMap_84_ = v_fileMap_61_;
v_currNamespace_85_ = v_currNamespace_63_;
v_openDecls_86_ = v_openDecls_64_;
v_initHeartbeats_87_ = v_initHeartbeats_65_;
v_maxHeartbeats_88_ = v_maxHeartbeats_66_;
v_quotContext_89_ = v_quotContext_67_;
v_currMacroScope_90_ = v_currMacroScope_68_;
v_cancelTk_x3f_91_ = v_cancelTk_x3f_69_;
v_inheritedTraceOptions_92_ = v_inheritedTraceOptions_70_;
v_currRecDepth_93_ = v_currRecDepth_56_;
v_ref_94_ = v_ref_57_;
v_suppressElabErrors_95_ = v_suppressElabErrors_58_;
v_isRecordingDeps_96_ = v_isRecordingDeps_59_;
v___y_97_ = v_a_53_;
goto v___jp_80_;
}
}
}
v___jp_128_:
{
uint16_t v___x_130_; lean_object* v___x_131_; lean_object* v_env_132_; uint8_t v___x_133_; uint16_t v___x_134_; uint16_t v___x_135_; uint16_t v___x_136_; uint8_t v___x_137_; 
v___x_130_ = l_Lean_OptionFlags_ofOptions(v___y_129_);
v___x_131_ = lean_st_ref_get(v_a_53_);
v_env_132_ = lean_ctor_get(v___x_131_, 0);
lean_inc_ref(v_env_132_);
lean_dec(v___x_131_);
v___x_133_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_132_);
lean_dec_ref(v_env_132_);
v___x_134_ = 512;
v___x_135_ = lean_uint16_land(v___x_130_, v___x_134_);
v___x_136_ = 0;
v___x_137_ = lean_uint16_dec_eq(v___x_135_, v___x_136_);
if (v___x_137_ == 0)
{
if (v___x_133_ == 0)
{
v___y_104_ = v___x_130_;
v___y_105_ = v___x_78_;
v___y_106_ = v___y_129_;
goto v___jp_103_;
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
v___y_81_ = v___x_130_;
v___y_82_ = v___y_129_;
v_fileName_83_ = v_fileName_60_;
v_fileMap_84_ = v_fileMap_61_;
v_currNamespace_85_ = v_currNamespace_63_;
v_openDecls_86_ = v_openDecls_64_;
v_initHeartbeats_87_ = v_initHeartbeats_65_;
v_maxHeartbeats_88_ = v_maxHeartbeats_66_;
v_quotContext_89_ = v_quotContext_67_;
v_currMacroScope_90_ = v_currMacroScope_68_;
v_cancelTk_x3f_91_ = v_cancelTk_x3f_69_;
v_inheritedTraceOptions_92_ = v_inheritedTraceOptions_70_;
v_currRecDepth_93_ = v_currRecDepth_56_;
v_ref_94_ = v_ref_57_;
v_suppressElabErrors_95_ = v_suppressElabErrors_58_;
v_isRecordingDeps_96_ = v_isRecordingDeps_59_;
v___y_97_ = v_a_53_;
goto v___jp_80_;
}
}
else
{
if (v___x_133_ == 0)
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
v___y_81_ = v___x_130_;
v___y_82_ = v___y_129_;
v_fileName_83_ = v_fileName_60_;
v_fileMap_84_ = v_fileMap_61_;
v_currNamespace_85_ = v_currNamespace_63_;
v_openDecls_86_ = v_openDecls_64_;
v_initHeartbeats_87_ = v_initHeartbeats_65_;
v_maxHeartbeats_88_ = v_maxHeartbeats_66_;
v_quotContext_89_ = v_quotContext_67_;
v_currMacroScope_90_ = v_currMacroScope_68_;
v_cancelTk_x3f_91_ = v_cancelTk_x3f_69_;
v_inheritedTraceOptions_92_ = v_inheritedTraceOptions_70_;
v_currRecDepth_93_ = v_currRecDepth_56_;
v_ref_94_ = v_ref_57_;
v_suppressElabErrors_95_ = v_suppressElabErrors_58_;
v_isRecordingDeps_96_ = v_isRecordingDeps_59_;
v___y_97_ = v_a_53_;
goto v___jp_80_;
}
else
{
v___y_104_ = v___x_130_;
v___y_105_ = v___x_79_;
v___y_106_ = v___y_129_;
goto v___jp_103_;
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
lean_object* v___x_159_; lean_object* v_traceState_160_; lean_object* v_traces_161_; lean_object* v___x_162_; lean_object* v_traceState_163_; lean_object* v_env_164_; lean_object* v_nextMacroScope_165_; lean_object* v_ngen_166_; lean_object* v_auxDeclNGen_167_; lean_object* v_cache_168_; lean_object* v_recordedDeps_169_; lean_object* v_messages_170_; lean_object* v_infoState_171_; lean_object* v_snapshotTasks_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_191_; 
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
v_recordedDeps_169_ = lean_ctor_get(v___x_162_, 6);
v_messages_170_ = lean_ctor_get(v___x_162_, 7);
v_infoState_171_ = lean_ctor_get(v___x_162_, 8);
v_snapshotTasks_172_ = lean_ctor_get(v___x_162_, 9);
v_isSharedCheck_191_ = !lean_is_exclusive(v___x_162_);
if (v_isSharedCheck_191_ == 0)
{
v___x_174_ = v___x_162_;
v_isShared_175_ = v_isSharedCheck_191_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_snapshotTasks_172_);
lean_inc(v_infoState_171_);
lean_inc(v_messages_170_);
lean_inc(v_recordedDeps_169_);
lean_inc(v_cache_168_);
lean_inc(v_traceState_163_);
lean_inc(v_auxDeclNGen_167_);
lean_inc(v_ngen_166_);
lean_inc(v_nextMacroScope_165_);
lean_inc(v_env_164_);
lean_dec(v___x_162_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_191_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
uint64_t v_tid_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_189_; 
v_tid_176_ = lean_ctor_get_uint64(v_traceState_163_, sizeof(void*)*1);
v_isSharedCheck_189_ = !lean_is_exclusive(v_traceState_163_);
if (v_isSharedCheck_189_ == 0)
{
lean_object* v_unused_190_; 
v_unused_190_ = lean_ctor_get(v_traceState_163_, 0);
lean_dec(v_unused_190_);
v___x_178_ = v_traceState_163_;
v_isShared_179_ = v_isSharedCheck_189_;
goto v_resetjp_177_;
}
else
{
lean_dec(v_traceState_163_);
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
v_reuseFailAlloc_187_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v_env_164_);
lean_ctor_set(v_reuseFailAlloc_187_, 1, v_nextMacroScope_165_);
lean_ctor_set(v_reuseFailAlloc_187_, 2, v_ngen_166_);
lean_ctor_set(v_reuseFailAlloc_187_, 3, v_auxDeclNGen_167_);
lean_ctor_set(v_reuseFailAlloc_187_, 4, v___x_182_);
lean_ctor_set(v_reuseFailAlloc_187_, 5, v_cache_168_);
lean_ctor_set(v_reuseFailAlloc_187_, 6, v_recordedDeps_169_);
lean_ctor_set(v_reuseFailAlloc_187_, 7, v_messages_170_);
lean_ctor_set(v_reuseFailAlloc_187_, 8, v_infoState_171_);
lean_ctor_set(v_reuseFailAlloc_187_, 9, v_snapshotTasks_172_);
v___x_184_ = v_reuseFailAlloc_187_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_185_ = lean_st_ref_put(v___y_157_, v___x_184_);
v___x_186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_186_, 0, v_traces_161_);
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
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(lean_object* v_opts_207_, lean_object* v_opt_208_){
_start:
{
lean_object* v_name_209_; lean_object* v_defValue_210_; lean_object* v_map_211_; lean_object* v___x_212_; 
v_name_209_ = lean_ctor_get(v_opt_208_, 0);
v_defValue_210_ = lean_ctor_get(v_opt_208_, 1);
v_map_211_ = lean_ctor_get(v_opts_207_, 0);
v___x_212_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_211_, v_name_209_);
if (lean_obj_tag(v___x_212_) == 0)
{
uint8_t v___x_213_; 
v___x_213_ = lean_unbox(v_defValue_210_);
return v___x_213_;
}
else
{
lean_object* v_val_214_; 
v_val_214_ = lean_ctor_get(v___x_212_, 0);
lean_inc(v_val_214_);
lean_dec_ref_known(v___x_212_, 1);
if (lean_obj_tag(v_val_214_) == 1)
{
uint8_t v_v_215_; 
v_v_215_ = lean_ctor_get_uint8(v_val_214_, 0);
lean_dec_ref_known(v_val_214_, 0);
return v_v_215_;
}
else
{
uint8_t v___x_216_; 
lean_dec(v_val_214_);
v___x_216_ = lean_unbox(v_defValue_210_);
return v___x_216_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___boxed(lean_object* v_opts_217_, lean_object* v_opt_218_){
_start:
{
uint8_t v_res_219_; lean_object* v_r_220_; 
v_res_219_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_217_, v_opt_218_);
lean_dec_ref(v_opt_218_);
lean_dec_ref(v_opts_217_);
v_r_220_ = lean_box(v_res_219_);
return v_r_220_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__2(void){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_224_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__1));
v___x_225_ = l_Lean_MessageData_ofFormat(v___x_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0(lean_object* v_x_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_232_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__2);
v___x_233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_233_, 0, v___x_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___boxed(lean_object* v_x_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0(v_x_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_);
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
lean_dec_ref(v_x_234_);
return v_res_240_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___closed__2(void){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_244_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___closed__1));
v___x_245_ = l_Lean_MessageData_ofFormat(v___x_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1(lean_object* v_x_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_252_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___closed__2);
v___x_253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___boxed(lean_object* v_x_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1(v_x_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_);
lean_dec(v___y_258_);
lean_dec_ref(v___y_257_);
lean_dec(v___y_256_);
lean_dec_ref(v___y_255_);
lean_dec_ref(v_x_254_);
return v_res_260_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___closed__2(void){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_264_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___closed__1));
v___x_265_ = l_Lean_MessageData_ofFormat(v___x_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2(lean_object* v_x_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___closed__2);
v___x_273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_273_, 0, v___x_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___boxed(lean_object* v_x_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2(v_x_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_);
lean_dec(v___y_278_);
lean_dec_ref(v___y_277_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
lean_dec_ref(v_x_274_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(lean_object* v_x_281_){
_start:
{
if (lean_obj_tag(v_x_281_) == 0)
{
lean_object* v_a_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_290_; 
v_a_283_ = lean_ctor_get(v_x_281_, 0);
v_isSharedCheck_290_ = !lean_is_exclusive(v_x_281_);
if (v_isSharedCheck_290_ == 0)
{
v___x_285_ = v_x_281_;
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_a_283_);
lean_dec(v_x_281_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_288_; 
if (v_isShared_286_ == 0)
{
lean_ctor_set_tag(v___x_285_, 1);
v___x_288_ = v___x_285_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v_a_283_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
}
}
}
else
{
lean_object* v_a_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_298_; 
v_a_291_ = lean_ctor_get(v_x_281_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v_x_281_);
if (v_isSharedCheck_298_ == 0)
{
v___x_293_ = v_x_281_;
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_a_291_);
lean_dec(v_x_281_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_296_; 
if (v_isShared_294_ == 0)
{
lean_ctor_set_tag(v___x_293_, 0);
v___x_296_ = v___x_293_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_a_291_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg___boxed(lean_object* v_x_299_, lean_object* v___y_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(v_x_299_);
return v_res_301_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4_spec__8(lean_object* v_e_302_){
_start:
{
if (lean_obj_tag(v_e_302_) == 0)
{
uint8_t v___x_303_; 
v___x_303_ = 2;
return v___x_303_;
}
else
{
uint8_t v___x_304_; 
v___x_304_ = 0;
return v___x_304_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4_spec__8___boxed(lean_object* v_e_305_){
_start:
{
uint8_t v_res_306_; lean_object* v_r_307_; 
v_res_306_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4_spec__8(v_e_305_);
lean_dec_ref(v_e_305_);
v_r_307_ = lean_box(v_res_306_);
return v_r_307_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2_spec__3(size_t v_sz_308_, size_t v_i_309_, lean_object* v_bs_310_){
_start:
{
uint8_t v___x_311_; 
v___x_311_ = lean_usize_dec_lt(v_i_309_, v_sz_308_);
if (v___x_311_ == 0)
{
return v_bs_310_;
}
else
{
lean_object* v_v_312_; lean_object* v_msg_313_; lean_object* v___x_314_; lean_object* v_bs_x27_315_; size_t v___x_316_; size_t v___x_317_; lean_object* v___x_318_; 
v_v_312_ = lean_array_uget_borrowed(v_bs_310_, v_i_309_);
v_msg_313_ = lean_ctor_get(v_v_312_, 1);
lean_inc_ref(v_msg_313_);
v___x_314_ = lean_unsigned_to_nat(0u);
v_bs_x27_315_ = lean_array_uset(v_bs_310_, v_i_309_, v___x_314_);
v___x_316_ = ((size_t)1ULL);
v___x_317_ = lean_usize_add(v_i_309_, v___x_316_);
v___x_318_ = lean_array_uset(v_bs_x27_315_, v_i_309_, v_msg_313_);
v_i_309_ = v___x_317_;
v_bs_310_ = v___x_318_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2_spec__3___boxed(lean_object* v_sz_320_, lean_object* v_i_321_, lean_object* v_bs_322_){
_start:
{
size_t v_sz_boxed_323_; size_t v_i_boxed_324_; lean_object* v_res_325_; 
v_sz_boxed_323_ = lean_unbox_usize(v_sz_320_);
lean_dec(v_sz_320_);
v_i_boxed_324_ = lean_unbox_usize(v_i_321_);
lean_dec(v_i_321_);
v_res_325_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2_spec__3(v_sz_boxed_323_, v_i_boxed_324_, v_bs_322_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__6(lean_object* v_msgData_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_){
_start:
{
lean_object* v___x_332_; lean_object* v_env_333_; lean_object* v___x_334_; lean_object* v_toCold_335_; lean_object* v_mctx_336_; lean_object* v_lctx_337_; lean_object* v_options_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_332_ = lean_st_ref_get(v___y_330_);
v_env_333_ = lean_ctor_get(v___x_332_, 0);
lean_inc_ref(v_env_333_);
lean_dec(v___x_332_);
v___x_334_ = lean_st_ref_get(v___y_328_);
v_toCold_335_ = lean_ctor_get(v___y_329_, 0);
v_mctx_336_ = lean_ctor_get(v___x_334_, 0);
lean_inc_ref(v_mctx_336_);
lean_dec(v___x_334_);
v_lctx_337_ = lean_ctor_get(v___y_327_, 2);
v_options_338_ = lean_ctor_get(v_toCold_335_, 2);
lean_inc_ref(v_options_338_);
lean_inc_ref(v_lctx_337_);
v___x_339_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_339_, 0, v_env_333_);
lean_ctor_set(v___x_339_, 1, v_mctx_336_);
lean_ctor_set(v___x_339_, 2, v_lctx_337_);
lean_ctor_set(v___x_339_, 3, v_options_338_);
v___x_340_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
lean_ctor_set(v___x_340_, 1, v_msgData_326_);
v___x_341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_341_, 0, v___x_340_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__6___boxed(lean_object* v_msgData_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__6(v_msgData_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_);
lean_dec(v___y_346_);
lean_dec_ref(v___y_345_);
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2(lean_object* v_oldTraces_349_, lean_object* v_data_350_, lean_object* v_ref_351_, lean_object* v_msg_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_){
_start:
{
lean_object* v_toCold_358_; lean_object* v_currRecDepth_359_; lean_object* v_ref_360_; uint16_t v_optionFlags_361_; uint8_t v_suppressElabErrors_362_; uint8_t v_isRecordingDeps_363_; lean_object* v_ref_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v_traceState_367_; lean_object* v_traces_368_; lean_object* v___x_369_; size_t v_sz_370_; size_t v___x_371_; lean_object* v___x_372_; lean_object* v_msg_373_; lean_object* v___x_374_; lean_object* v_a_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_413_; 
v_toCold_358_ = lean_ctor_get(v___y_355_, 0);
v_currRecDepth_359_ = lean_ctor_get(v___y_355_, 1);
v_ref_360_ = lean_ctor_get(v___y_355_, 2);
v_optionFlags_361_ = lean_ctor_get_uint16(v___y_355_, sizeof(void*)*3);
v_suppressElabErrors_362_ = lean_ctor_get_uint8(v___y_355_, sizeof(void*)*3 + 2);
v_isRecordingDeps_363_ = lean_ctor_get_uint8(v___y_355_, sizeof(void*)*3 + 3);
v_ref_364_ = l_Lean_replaceRef(v_ref_351_, v_ref_360_);
lean_inc(v_currRecDepth_359_);
lean_inc_ref(v_toCold_358_);
v___x_365_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_365_, 0, v_toCold_358_);
lean_ctor_set(v___x_365_, 1, v_currRecDepth_359_);
lean_ctor_set(v___x_365_, 2, v_ref_364_);
lean_ctor_set_uint16(v___x_365_, sizeof(void*)*3, v_optionFlags_361_);
lean_ctor_set_uint8(v___x_365_, sizeof(void*)*3 + 2, v_suppressElabErrors_362_);
lean_ctor_set_uint8(v___x_365_, sizeof(void*)*3 + 3, v_isRecordingDeps_363_);
v___x_366_ = lean_st_ref_get(v___y_356_);
v_traceState_367_ = lean_ctor_get(v___x_366_, 4);
lean_inc_ref(v_traceState_367_);
lean_dec(v___x_366_);
v_traces_368_ = lean_ctor_get(v_traceState_367_, 0);
lean_inc_ref(v_traces_368_);
lean_dec_ref(v_traceState_367_);
v___x_369_ = l_Lean_PersistentArray_toArray___redArg(v_traces_368_);
lean_dec_ref(v_traces_368_);
v_sz_370_ = lean_array_size(v___x_369_);
v___x_371_ = ((size_t)0ULL);
v___x_372_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2_spec__3(v_sz_370_, v___x_371_, v___x_369_);
v_msg_373_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_373_, 0, v_data_350_);
lean_ctor_set(v_msg_373_, 1, v_msg_352_);
lean_ctor_set(v_msg_373_, 2, v___x_372_);
v___x_374_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__6(v_msg_373_, v___y_353_, v___y_354_, v___x_365_, v___y_356_);
lean_dec_ref_known(v___x_365_, 3);
v_a_375_ = lean_ctor_get(v___x_374_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_413_ == 0)
{
v___x_377_ = v___x_374_;
v_isShared_378_ = v_isSharedCheck_413_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_a_375_);
lean_dec(v___x_374_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_413_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_379_; lean_object* v_traceState_380_; lean_object* v_env_381_; lean_object* v_nextMacroScope_382_; lean_object* v_ngen_383_; lean_object* v_auxDeclNGen_384_; lean_object* v_cache_385_; lean_object* v_recordedDeps_386_; lean_object* v_messages_387_; lean_object* v_infoState_388_; lean_object* v_snapshotTasks_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_412_; 
v___x_379_ = lean_st_ref_take(v___y_356_);
v_traceState_380_ = lean_ctor_get(v___x_379_, 4);
v_env_381_ = lean_ctor_get(v___x_379_, 0);
v_nextMacroScope_382_ = lean_ctor_get(v___x_379_, 1);
v_ngen_383_ = lean_ctor_get(v___x_379_, 2);
v_auxDeclNGen_384_ = lean_ctor_get(v___x_379_, 3);
v_cache_385_ = lean_ctor_get(v___x_379_, 5);
v_recordedDeps_386_ = lean_ctor_get(v___x_379_, 6);
v_messages_387_ = lean_ctor_get(v___x_379_, 7);
v_infoState_388_ = lean_ctor_get(v___x_379_, 8);
v_snapshotTasks_389_ = lean_ctor_get(v___x_379_, 9);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_412_ == 0)
{
v___x_391_ = v___x_379_;
v_isShared_392_ = v_isSharedCheck_412_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_snapshotTasks_389_);
lean_inc(v_infoState_388_);
lean_inc(v_messages_387_);
lean_inc(v_recordedDeps_386_);
lean_inc(v_cache_385_);
lean_inc(v_traceState_380_);
lean_inc(v_auxDeclNGen_384_);
lean_inc(v_ngen_383_);
lean_inc(v_nextMacroScope_382_);
lean_inc(v_env_381_);
lean_dec(v___x_379_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_412_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
uint64_t v_tid_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_410_; 
v_tid_393_ = lean_ctor_get_uint64(v_traceState_380_, sizeof(void*)*1);
v_isSharedCheck_410_ = !lean_is_exclusive(v_traceState_380_);
if (v_isSharedCheck_410_ == 0)
{
lean_object* v_unused_411_; 
v_unused_411_ = lean_ctor_get(v_traceState_380_, 0);
lean_dec(v_unused_411_);
v___x_395_ = v_traceState_380_;
v_isShared_396_ = v_isSharedCheck_410_;
goto v_resetjp_394_;
}
else
{
lean_dec(v_traceState_380_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_410_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_401_; 
v___x_397_ = lean_box(0);
v___x_398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_398_, 0, v_ref_351_);
lean_ctor_set(v___x_398_, 1, v_a_375_);
v___x_399_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_349_, v___x_398_);
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 0, v___x_399_);
v___x_401_ = v___x_395_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_399_);
lean_ctor_set_uint64(v_reuseFailAlloc_409_, sizeof(void*)*1, v_tid_393_);
v___x_401_ = v_reuseFailAlloc_409_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
lean_object* v___x_403_; 
if (v_isShared_392_ == 0)
{
lean_ctor_set(v___x_391_, 4, v___x_401_);
v___x_403_ = v___x_391_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_env_381_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v_nextMacroScope_382_);
lean_ctor_set(v_reuseFailAlloc_408_, 2, v_ngen_383_);
lean_ctor_set(v_reuseFailAlloc_408_, 3, v_auxDeclNGen_384_);
lean_ctor_set(v_reuseFailAlloc_408_, 4, v___x_401_);
lean_ctor_set(v_reuseFailAlloc_408_, 5, v_cache_385_);
lean_ctor_set(v_reuseFailAlloc_408_, 6, v_recordedDeps_386_);
lean_ctor_set(v_reuseFailAlloc_408_, 7, v_messages_387_);
lean_ctor_set(v_reuseFailAlloc_408_, 8, v_infoState_388_);
lean_ctor_set(v_reuseFailAlloc_408_, 9, v_snapshotTasks_389_);
v___x_403_ = v_reuseFailAlloc_408_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
lean_object* v___x_404_; lean_object* v___x_406_; 
v___x_404_ = lean_st_ref_put(v___y_356_, v___x_403_);
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 0, v___x_397_);
v___x_406_ = v___x_377_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_397_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2___boxed(lean_object* v_oldTraces_414_, lean_object* v_data_415_, lean_object* v_ref_416_, lean_object* v_msg_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2(v_oldTraces_414_, v_data_415_, v_ref_416_, v_msg_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_);
lean_dec(v___y_421_);
lean_dec_ref(v___y_420_);
lean_dec(v___y_419_);
lean_dec_ref(v___y_418_);
return v_res_423_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0(void){
_start:
{
lean_object* v___x_424_; double v___x_425_; 
v___x_424_ = lean_unsigned_to_nat(0u);
v___x_425_ = lean_float_of_nat(v___x_424_);
return v___x_425_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2(void){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__1));
v___x_428_ = l_Lean_stringToMessageData(v___x_427_);
return v___x_428_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3(void){
_start:
{
lean_object* v___x_429_; double v___x_430_; 
v___x_429_ = lean_unsigned_to_nat(1000u);
v___x_430_ = lean_float_of_nat(v___x_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4(lean_object* v_cls_431_, uint8_t v_collapsed_432_, lean_object* v_tag_433_, lean_object* v_opts_434_, uint8_t v_clsEnabled_435_, lean_object* v_oldTraces_436_, lean_object* v_msg_437_, lean_object* v_resStartStop_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
lean_object* v_fst_444_; lean_object* v_snd_445_; lean_object* v___y_447_; lean_object* v___y_448_; lean_object* v_data_449_; lean_object* v_fst_452_; lean_object* v_snd_453_; lean_object* v___x_454_; uint8_t v___x_455_; lean_object* v___y_457_; lean_object* v_a_458_; uint8_t v___y_473_; double v___y_505_; 
v_fst_444_ = lean_ctor_get(v_resStartStop_438_, 0);
lean_inc(v_fst_444_);
v_snd_445_ = lean_ctor_get(v_resStartStop_438_, 1);
lean_inc(v_snd_445_);
lean_dec_ref(v_resStartStop_438_);
v_fst_452_ = lean_ctor_get(v_snd_445_, 0);
lean_inc(v_fst_452_);
v_snd_453_ = lean_ctor_get(v_snd_445_, 1);
lean_inc(v_snd_453_);
lean_dec(v_snd_445_);
v___x_454_ = l_Lean_trace_profiler;
v___x_455_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_434_, v___x_454_);
if (v___x_455_ == 0)
{
v___y_473_ = v___x_455_;
goto v___jp_472_;
}
else
{
lean_object* v___x_510_; uint8_t v___x_511_; 
v___x_510_ = l_Lean_trace_profiler_useHeartbeats;
v___x_511_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_434_, v___x_510_);
if (v___x_511_ == 0)
{
lean_object* v___x_512_; lean_object* v___x_513_; double v___x_514_; double v___x_515_; double v___x_516_; 
v___x_512_ = l_Lean_trace_profiler_threshold;
v___x_513_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_434_, v___x_512_);
v___x_514_ = lean_float_of_nat(v___x_513_);
v___x_515_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3);
v___x_516_ = lean_float_div(v___x_514_, v___x_515_);
v___y_505_ = v___x_516_;
goto v___jp_504_;
}
else
{
lean_object* v___x_517_; lean_object* v___x_518_; double v___x_519_; 
v___x_517_ = l_Lean_trace_profiler_threshold;
v___x_518_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_434_, v___x_517_);
v___x_519_ = lean_float_of_nat(v___x_518_);
v___y_505_ = v___x_519_;
goto v___jp_504_;
}
}
v___jp_446_:
{
lean_object* v___x_450_; 
lean_inc(v___y_447_);
v___x_450_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2(v_oldTraces_436_, v_data_449_, v___y_447_, v___y_448_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
if (lean_obj_tag(v___x_450_) == 0)
{
lean_object* v___x_451_; 
lean_dec_ref_known(v___x_450_, 1);
v___x_451_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(v_fst_444_);
return v___x_451_;
}
else
{
lean_dec(v_fst_444_);
return v___x_450_;
}
}
v___jp_456_:
{
uint8_t v_result_459_; lean_object* v___x_460_; lean_object* v___x_461_; double v___x_462_; lean_object* v_data_463_; 
v_result_459_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4_spec__8(v_fst_444_);
v___x_460_ = lean_box(v_result_459_);
v___x_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_461_, 0, v___x_460_);
v___x_462_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0);
lean_inc_ref(v_tag_433_);
lean_inc_ref(v___x_461_);
lean_inc(v_cls_431_);
v_data_463_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_463_, 0, v_cls_431_);
lean_ctor_set(v_data_463_, 1, v___x_461_);
lean_ctor_set(v_data_463_, 2, v_tag_433_);
lean_ctor_set_float(v_data_463_, sizeof(void*)*3, v___x_462_);
lean_ctor_set_float(v_data_463_, sizeof(void*)*3 + 8, v___x_462_);
lean_ctor_set_uint8(v_data_463_, sizeof(void*)*3 + 16, v_collapsed_432_);
if (v___x_455_ == 0)
{
lean_dec_ref_known(v___x_461_, 1);
lean_dec(v_snd_453_);
lean_dec(v_fst_452_);
lean_dec_ref(v_tag_433_);
lean_dec(v_cls_431_);
v___y_447_ = v___y_457_;
v___y_448_ = v_a_458_;
v_data_449_ = v_data_463_;
goto v___jp_446_;
}
else
{
lean_object* v_data_464_; double v___x_465_; double v___x_466_; 
lean_dec_ref_known(v_data_463_, 3);
v_data_464_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_464_, 0, v_cls_431_);
lean_ctor_set(v_data_464_, 1, v___x_461_);
lean_ctor_set(v_data_464_, 2, v_tag_433_);
v___x_465_ = lean_unbox_float(v_fst_452_);
lean_dec(v_fst_452_);
lean_ctor_set_float(v_data_464_, sizeof(void*)*3, v___x_465_);
v___x_466_ = lean_unbox_float(v_snd_453_);
lean_dec(v_snd_453_);
lean_ctor_set_float(v_data_464_, sizeof(void*)*3 + 8, v___x_466_);
lean_ctor_set_uint8(v_data_464_, sizeof(void*)*3 + 16, v_collapsed_432_);
v___y_447_ = v___y_457_;
v___y_448_ = v_a_458_;
v_data_449_ = v_data_464_;
goto v___jp_446_;
}
}
v___jp_467_:
{
lean_object* v_ref_468_; lean_object* v___x_469_; 
v_ref_468_ = lean_ctor_get(v___y_441_, 2);
lean_inc(v___y_442_);
lean_inc_ref(v___y_441_);
lean_inc(v___y_440_);
lean_inc_ref(v___y_439_);
lean_inc(v_fst_444_);
v___x_469_ = lean_apply_6(v_msg_437_, v_fst_444_, v___y_439_, v___y_440_, v___y_441_, v___y_442_, lean_box(0));
if (lean_obj_tag(v___x_469_) == 0)
{
lean_object* v_a_470_; 
v_a_470_ = lean_ctor_get(v___x_469_, 0);
lean_inc(v_a_470_);
lean_dec_ref_known(v___x_469_, 1);
v___y_457_ = v_ref_468_;
v_a_458_ = v_a_470_;
goto v___jp_456_;
}
else
{
lean_object* v___x_471_; 
lean_dec_ref_known(v___x_469_, 1);
v___x_471_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2);
v___y_457_ = v_ref_468_;
v_a_458_ = v___x_471_;
goto v___jp_456_;
}
}
v___jp_472_:
{
if (v_clsEnabled_435_ == 0)
{
if (v___y_473_ == 0)
{
lean_object* v___x_474_; lean_object* v_traceState_475_; lean_object* v_env_476_; lean_object* v_nextMacroScope_477_; lean_object* v_ngen_478_; lean_object* v_auxDeclNGen_479_; lean_object* v_cache_480_; lean_object* v_recordedDeps_481_; lean_object* v_messages_482_; lean_object* v_infoState_483_; lean_object* v_snapshotTasks_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_503_; 
lean_dec(v_snd_453_);
lean_dec(v_fst_452_);
lean_dec_ref(v_msg_437_);
lean_dec_ref(v_tag_433_);
lean_dec(v_cls_431_);
v___x_474_ = lean_st_ref_take(v___y_442_);
v_traceState_475_ = lean_ctor_get(v___x_474_, 4);
v_env_476_ = lean_ctor_get(v___x_474_, 0);
v_nextMacroScope_477_ = lean_ctor_get(v___x_474_, 1);
v_ngen_478_ = lean_ctor_get(v___x_474_, 2);
v_auxDeclNGen_479_ = lean_ctor_get(v___x_474_, 3);
v_cache_480_ = lean_ctor_get(v___x_474_, 5);
v_recordedDeps_481_ = lean_ctor_get(v___x_474_, 6);
v_messages_482_ = lean_ctor_get(v___x_474_, 7);
v_infoState_483_ = lean_ctor_get(v___x_474_, 8);
v_snapshotTasks_484_ = lean_ctor_get(v___x_474_, 9);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_503_ == 0)
{
v___x_486_ = v___x_474_;
v_isShared_487_ = v_isSharedCheck_503_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_snapshotTasks_484_);
lean_inc(v_infoState_483_);
lean_inc(v_messages_482_);
lean_inc(v_recordedDeps_481_);
lean_inc(v_cache_480_);
lean_inc(v_traceState_475_);
lean_inc(v_auxDeclNGen_479_);
lean_inc(v_ngen_478_);
lean_inc(v_nextMacroScope_477_);
lean_inc(v_env_476_);
lean_dec(v___x_474_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_503_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
uint64_t v_tid_488_; lean_object* v_traces_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_502_; 
v_tid_488_ = lean_ctor_get_uint64(v_traceState_475_, sizeof(void*)*1);
v_traces_489_ = lean_ctor_get(v_traceState_475_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v_traceState_475_);
if (v_isSharedCheck_502_ == 0)
{
v___x_491_ = v_traceState_475_;
v_isShared_492_ = v_isSharedCheck_502_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_traces_489_);
lean_dec(v_traceState_475_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_502_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___x_493_; lean_object* v___x_495_; 
v___x_493_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_436_, v_traces_489_);
lean_dec_ref(v_traces_489_);
if (v_isShared_492_ == 0)
{
lean_ctor_set(v___x_491_, 0, v___x_493_);
v___x_495_ = v___x_491_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v___x_493_);
lean_ctor_set_uint64(v_reuseFailAlloc_501_, sizeof(void*)*1, v_tid_488_);
v___x_495_ = v_reuseFailAlloc_501_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
lean_object* v___x_497_; 
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 4, v___x_495_);
v___x_497_ = v___x_486_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_env_476_);
lean_ctor_set(v_reuseFailAlloc_500_, 1, v_nextMacroScope_477_);
lean_ctor_set(v_reuseFailAlloc_500_, 2, v_ngen_478_);
lean_ctor_set(v_reuseFailAlloc_500_, 3, v_auxDeclNGen_479_);
lean_ctor_set(v_reuseFailAlloc_500_, 4, v___x_495_);
lean_ctor_set(v_reuseFailAlloc_500_, 5, v_cache_480_);
lean_ctor_set(v_reuseFailAlloc_500_, 6, v_recordedDeps_481_);
lean_ctor_set(v_reuseFailAlloc_500_, 7, v_messages_482_);
lean_ctor_set(v_reuseFailAlloc_500_, 8, v_infoState_483_);
lean_ctor_set(v_reuseFailAlloc_500_, 9, v_snapshotTasks_484_);
v___x_497_ = v_reuseFailAlloc_500_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = lean_st_ref_put(v___y_442_, v___x_497_);
v___x_499_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(v_fst_444_);
return v___x_499_;
}
}
}
}
}
else
{
goto v___jp_467_;
}
}
else
{
goto v___jp_467_;
}
}
v___jp_504_:
{
double v___x_506_; double v___x_507_; double v___x_508_; uint8_t v___x_509_; 
v___x_506_ = lean_unbox_float(v_snd_453_);
v___x_507_ = lean_unbox_float(v_fst_452_);
v___x_508_ = lean_float_sub(v___x_506_, v___x_507_);
v___x_509_ = lean_float_decLt(v___y_505_, v___x_508_);
v___y_473_ = v___x_509_;
goto v___jp_472_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___boxed(lean_object* v_cls_520_, lean_object* v_collapsed_521_, lean_object* v_tag_522_, lean_object* v_opts_523_, lean_object* v_clsEnabled_524_, lean_object* v_oldTraces_525_, lean_object* v_msg_526_, lean_object* v_resStartStop_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_){
_start:
{
uint8_t v_collapsed_boxed_533_; uint8_t v_clsEnabled_boxed_534_; lean_object* v_res_535_; 
v_collapsed_boxed_533_ = lean_unbox(v_collapsed_521_);
v_clsEnabled_boxed_534_ = lean_unbox(v_clsEnabled_524_);
v_res_535_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4(v_cls_520_, v_collapsed_boxed_533_, v_tag_522_, v_opts_523_, v_clsEnabled_boxed_534_, v_oldTraces_525_, v_msg_526_, v_resStartStop_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_528_);
lean_dec_ref(v_opts_523_);
return v_res_535_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__4(lean_object* v_e_536_){
_start:
{
if (lean_obj_tag(v_e_536_) == 0)
{
uint8_t v___x_537_; 
v___x_537_ = 2;
return v___x_537_;
}
else
{
lean_object* v_a_538_; uint8_t v___x_539_; 
v_a_538_ = lean_ctor_get(v_e_536_, 0);
v___x_539_ = l_Lean_Expr_hasSyntheticSorry(v_a_538_);
if (v___x_539_ == 0)
{
uint8_t v___x_540_; 
v___x_540_ = 0;
return v___x_540_;
}
else
{
uint8_t v___x_541_; 
v___x_541_ = 1;
return v___x_541_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__4___boxed(lean_object* v_e_542_){
_start:
{
uint8_t v_res_543_; lean_object* v_r_544_; 
v_res_543_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__4(v_e_542_);
lean_dec_ref(v_e_542_);
v_r_544_ = lean_box(v_res_543_);
return v_r_544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2(lean_object* v_cls_545_, uint8_t v_collapsed_546_, lean_object* v_tag_547_, lean_object* v_opts_548_, uint8_t v_clsEnabled_549_, lean_object* v_oldTraces_550_, lean_object* v_msg_551_, lean_object* v_resStartStop_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_){
_start:
{
lean_object* v_fst_558_; lean_object* v_snd_559_; lean_object* v___y_561_; lean_object* v___y_562_; lean_object* v_data_563_; lean_object* v_fst_574_; lean_object* v_snd_575_; lean_object* v___x_576_; uint8_t v___x_577_; lean_object* v___y_579_; lean_object* v_a_580_; uint8_t v___y_595_; double v___y_627_; 
v_fst_558_ = lean_ctor_get(v_resStartStop_552_, 0);
lean_inc(v_fst_558_);
v_snd_559_ = lean_ctor_get(v_resStartStop_552_, 1);
lean_inc(v_snd_559_);
lean_dec_ref(v_resStartStop_552_);
v_fst_574_ = lean_ctor_get(v_snd_559_, 0);
lean_inc(v_fst_574_);
v_snd_575_ = lean_ctor_get(v_snd_559_, 1);
lean_inc(v_snd_575_);
lean_dec(v_snd_559_);
v___x_576_ = l_Lean_trace_profiler;
v___x_577_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_548_, v___x_576_);
if (v___x_577_ == 0)
{
v___y_595_ = v___x_577_;
goto v___jp_594_;
}
else
{
lean_object* v___x_632_; uint8_t v___x_633_; 
v___x_632_ = l_Lean_trace_profiler_useHeartbeats;
v___x_633_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_548_, v___x_632_);
if (v___x_633_ == 0)
{
lean_object* v___x_634_; lean_object* v___x_635_; double v___x_636_; double v___x_637_; double v___x_638_; 
v___x_634_ = l_Lean_trace_profiler_threshold;
v___x_635_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_548_, v___x_634_);
v___x_636_ = lean_float_of_nat(v___x_635_);
v___x_637_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3);
v___x_638_ = lean_float_div(v___x_636_, v___x_637_);
v___y_627_ = v___x_638_;
goto v___jp_626_;
}
else
{
lean_object* v___x_639_; lean_object* v___x_640_; double v___x_641_; 
v___x_639_ = l_Lean_trace_profiler_threshold;
v___x_640_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_548_, v___x_639_);
v___x_641_ = lean_float_of_nat(v___x_640_);
v___y_627_ = v___x_641_;
goto v___jp_626_;
}
}
v___jp_560_:
{
lean_object* v___x_564_; 
lean_inc(v___y_561_);
v___x_564_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2(v_oldTraces_550_, v_data_563_, v___y_561_, v___y_562_, v___y_553_, v___y_554_, v___y_555_, v___y_556_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v___x_565_; 
lean_dec_ref_known(v___x_564_, 1);
v___x_565_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(v_fst_558_);
return v___x_565_;
}
else
{
lean_object* v_a_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_573_; 
lean_dec(v_fst_558_);
v_a_566_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_573_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_573_ == 0)
{
v___x_568_ = v___x_564_;
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_a_566_);
lean_dec(v___x_564_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_571_; 
if (v_isShared_569_ == 0)
{
v___x_571_ = v___x_568_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_a_566_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
}
v___jp_578_:
{
uint8_t v_result_581_; lean_object* v___x_582_; lean_object* v___x_583_; double v___x_584_; lean_object* v_data_585_; 
v_result_581_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__4(v_fst_558_);
v___x_582_ = lean_box(v_result_581_);
v___x_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_583_, 0, v___x_582_);
v___x_584_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0);
lean_inc_ref(v_tag_547_);
lean_inc_ref(v___x_583_);
lean_inc(v_cls_545_);
v_data_585_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_585_, 0, v_cls_545_);
lean_ctor_set(v_data_585_, 1, v___x_583_);
lean_ctor_set(v_data_585_, 2, v_tag_547_);
lean_ctor_set_float(v_data_585_, sizeof(void*)*3, v___x_584_);
lean_ctor_set_float(v_data_585_, sizeof(void*)*3 + 8, v___x_584_);
lean_ctor_set_uint8(v_data_585_, sizeof(void*)*3 + 16, v_collapsed_546_);
if (v___x_577_ == 0)
{
lean_dec_ref_known(v___x_583_, 1);
lean_dec(v_snd_575_);
lean_dec(v_fst_574_);
lean_dec_ref(v_tag_547_);
lean_dec(v_cls_545_);
v___y_561_ = v___y_579_;
v___y_562_ = v_a_580_;
v_data_563_ = v_data_585_;
goto v___jp_560_;
}
else
{
lean_object* v_data_586_; double v___x_587_; double v___x_588_; 
lean_dec_ref_known(v_data_585_, 3);
v_data_586_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_586_, 0, v_cls_545_);
lean_ctor_set(v_data_586_, 1, v___x_583_);
lean_ctor_set(v_data_586_, 2, v_tag_547_);
v___x_587_ = lean_unbox_float(v_fst_574_);
lean_dec(v_fst_574_);
lean_ctor_set_float(v_data_586_, sizeof(void*)*3, v___x_587_);
v___x_588_ = lean_unbox_float(v_snd_575_);
lean_dec(v_snd_575_);
lean_ctor_set_float(v_data_586_, sizeof(void*)*3 + 8, v___x_588_);
lean_ctor_set_uint8(v_data_586_, sizeof(void*)*3 + 16, v_collapsed_546_);
v___y_561_ = v___y_579_;
v___y_562_ = v_a_580_;
v_data_563_ = v_data_586_;
goto v___jp_560_;
}
}
v___jp_589_:
{
lean_object* v_ref_590_; lean_object* v___x_591_; 
v_ref_590_ = lean_ctor_get(v___y_555_, 2);
lean_inc(v___y_556_);
lean_inc_ref(v___y_555_);
lean_inc(v___y_554_);
lean_inc_ref(v___y_553_);
lean_inc(v_fst_558_);
v___x_591_ = lean_apply_6(v_msg_551_, v_fst_558_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, lean_box(0));
if (lean_obj_tag(v___x_591_) == 0)
{
lean_object* v_a_592_; 
v_a_592_ = lean_ctor_get(v___x_591_, 0);
lean_inc(v_a_592_);
lean_dec_ref_known(v___x_591_, 1);
v___y_579_ = v_ref_590_;
v_a_580_ = v_a_592_;
goto v___jp_578_;
}
else
{
lean_object* v___x_593_; 
lean_dec_ref_known(v___x_591_, 1);
v___x_593_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2);
v___y_579_ = v_ref_590_;
v_a_580_ = v___x_593_;
goto v___jp_578_;
}
}
v___jp_594_:
{
if (v_clsEnabled_549_ == 0)
{
if (v___y_595_ == 0)
{
lean_object* v___x_596_; lean_object* v_traceState_597_; lean_object* v_env_598_; lean_object* v_nextMacroScope_599_; lean_object* v_ngen_600_; lean_object* v_auxDeclNGen_601_; lean_object* v_cache_602_; lean_object* v_recordedDeps_603_; lean_object* v_messages_604_; lean_object* v_infoState_605_; lean_object* v_snapshotTasks_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_625_; 
lean_dec(v_snd_575_);
lean_dec(v_fst_574_);
lean_dec_ref(v_msg_551_);
lean_dec_ref(v_tag_547_);
lean_dec(v_cls_545_);
v___x_596_ = lean_st_ref_take(v___y_556_);
v_traceState_597_ = lean_ctor_get(v___x_596_, 4);
v_env_598_ = lean_ctor_get(v___x_596_, 0);
v_nextMacroScope_599_ = lean_ctor_get(v___x_596_, 1);
v_ngen_600_ = lean_ctor_get(v___x_596_, 2);
v_auxDeclNGen_601_ = lean_ctor_get(v___x_596_, 3);
v_cache_602_ = lean_ctor_get(v___x_596_, 5);
v_recordedDeps_603_ = lean_ctor_get(v___x_596_, 6);
v_messages_604_ = lean_ctor_get(v___x_596_, 7);
v_infoState_605_ = lean_ctor_get(v___x_596_, 8);
v_snapshotTasks_606_ = lean_ctor_get(v___x_596_, 9);
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_625_ == 0)
{
v___x_608_ = v___x_596_;
v_isShared_609_ = v_isSharedCheck_625_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_snapshotTasks_606_);
lean_inc(v_infoState_605_);
lean_inc(v_messages_604_);
lean_inc(v_recordedDeps_603_);
lean_inc(v_cache_602_);
lean_inc(v_traceState_597_);
lean_inc(v_auxDeclNGen_601_);
lean_inc(v_ngen_600_);
lean_inc(v_nextMacroScope_599_);
lean_inc(v_env_598_);
lean_dec(v___x_596_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_625_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
uint64_t v_tid_610_; lean_object* v_traces_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_624_; 
v_tid_610_ = lean_ctor_get_uint64(v_traceState_597_, sizeof(void*)*1);
v_traces_611_ = lean_ctor_get(v_traceState_597_, 0);
v_isSharedCheck_624_ = !lean_is_exclusive(v_traceState_597_);
if (v_isSharedCheck_624_ == 0)
{
v___x_613_ = v_traceState_597_;
v_isShared_614_ = v_isSharedCheck_624_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_traces_611_);
lean_dec(v_traceState_597_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_624_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_615_; lean_object* v___x_617_; 
v___x_615_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_550_, v_traces_611_);
lean_dec_ref(v_traces_611_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v___x_615_);
v___x_617_ = v___x_613_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v___x_615_);
lean_ctor_set_uint64(v_reuseFailAlloc_623_, sizeof(void*)*1, v_tid_610_);
v___x_617_ = v_reuseFailAlloc_623_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
lean_object* v___x_619_; 
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 4, v___x_617_);
v___x_619_ = v___x_608_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_env_598_);
lean_ctor_set(v_reuseFailAlloc_622_, 1, v_nextMacroScope_599_);
lean_ctor_set(v_reuseFailAlloc_622_, 2, v_ngen_600_);
lean_ctor_set(v_reuseFailAlloc_622_, 3, v_auxDeclNGen_601_);
lean_ctor_set(v_reuseFailAlloc_622_, 4, v___x_617_);
lean_ctor_set(v_reuseFailAlloc_622_, 5, v_cache_602_);
lean_ctor_set(v_reuseFailAlloc_622_, 6, v_recordedDeps_603_);
lean_ctor_set(v_reuseFailAlloc_622_, 7, v_messages_604_);
lean_ctor_set(v_reuseFailAlloc_622_, 8, v_infoState_605_);
lean_ctor_set(v_reuseFailAlloc_622_, 9, v_snapshotTasks_606_);
v___x_619_ = v_reuseFailAlloc_622_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_620_ = lean_st_ref_put(v___y_556_, v___x_619_);
v___x_621_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(v_fst_558_);
return v___x_621_;
}
}
}
}
}
else
{
goto v___jp_589_;
}
}
else
{
goto v___jp_589_;
}
}
v___jp_626_:
{
double v___x_628_; double v___x_629_; double v___x_630_; uint8_t v___x_631_; 
v___x_628_ = lean_unbox_float(v_snd_575_);
v___x_629_ = lean_unbox_float(v_fst_574_);
v___x_630_ = lean_float_sub(v___x_628_, v___x_629_);
v___x_631_ = lean_float_decLt(v___y_627_, v___x_630_);
v___y_595_ = v___x_631_;
goto v___jp_594_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___boxed(lean_object* v_cls_642_, lean_object* v_collapsed_643_, lean_object* v_tag_644_, lean_object* v_opts_645_, lean_object* v_clsEnabled_646_, lean_object* v_oldTraces_647_, lean_object* v_msg_648_, lean_object* v_resStartStop_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_){
_start:
{
uint8_t v_collapsed_boxed_655_; uint8_t v_clsEnabled_boxed_656_; lean_object* v_res_657_; 
v_collapsed_boxed_655_ = lean_unbox(v_collapsed_643_);
v_clsEnabled_boxed_656_ = lean_unbox(v_clsEnabled_646_);
v_res_657_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2(v_cls_642_, v_collapsed_boxed_655_, v_tag_644_, v_opts_645_, v_clsEnabled_boxed_656_, v_oldTraces_647_, v_msg_648_, v_resStartStop_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
lean_dec_ref(v_opts_645_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___redArg(lean_object* v_msg_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_){
_start:
{
lean_object* v_ref_664_; lean_object* v___x_665_; lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_674_; 
v_ref_664_ = lean_ctor_get(v___y_661_, 2);
v___x_665_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__6(v_msg_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_);
v_a_666_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_674_ == 0)
{
v___x_668_ = v___x_665_;
v_isShared_669_ = v_isSharedCheck_674_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_dec(v___x_665_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_674_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_670_; lean_object* v___x_672_; 
lean_inc(v_ref_664_);
v___x_670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_670_, 0, v_ref_664_);
lean_ctor_set(v___x_670_, 1, v_a_666_);
if (v_isShared_669_ == 0)
{
lean_ctor_set_tag(v___x_668_, 1);
lean_ctor_set(v___x_668_, 0, v___x_670_);
v___x_672_ = v___x_668_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v___x_670_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___redArg___boxed(lean_object* v_msg_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___redArg(v_msg_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
return v_res_681_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__10(void){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_699_ = lean_box(0);
v___x_700_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__9));
v___x_701_ = l_Lean_mkConst(v___x_700_, v___x_699_);
return v___x_701_;
}
}
static double _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12(void){
_start:
{
lean_object* v___x_703_; double v___x_704_; 
v___x_703_ = lean_unsigned_to_nat(1000000000u);
v___x_704_ = lean_float_of_nat(v___x_703_);
return v___x_704_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17(void){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_710_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__16));
v___x_711_ = l_Lean_stringToMessageData(v___x_710_);
return v___x_711_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__21(void){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_720_ = lean_box(0);
v___x_721_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__20));
v___x_722_ = l_Lean_mkConst(v___x_721_, v___x_720_);
return v___x_722_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23(void){
_start:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_729_ = lean_box(0);
v___x_730_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__22));
v___x_731_ = l_Lean_mkConst(v___x_730_, v___x_729_);
return v___x_731_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24(void){
_start:
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_732_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
v___x_733_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
v___x_734_ = l_Lean_Name_append(v___x_733_, v___x_732_);
return v___x_734_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__27(void){
_start:
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_738_ = lean_box(0);
v___x_739_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__26));
v___x_740_ = l_Lean_mkConst(v___x_739_, v___x_738_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(lean_object* v_cert_742_, lean_object* v_ctx_743_, lean_object* v_reflectionResult_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_){
_start:
{
lean_object* v_toCold_750_; lean_object* v_options_751_; lean_object* v_exprDef_752_; lean_object* v_certDef_753_; lean_object* v_expr_754_; lean_object* v_ref_755_; lean_object* v_inheritedTraceOptions_756_; uint8_t v_hasTrace_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___f_760_; lean_object* v___f_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; uint8_t v___x_766_; lean_object* v___x_767_; lean_object* v___y_769_; lean_object* v___y_770_; lean_object* v___y_771_; uint8_t v___y_772_; lean_object* v_a_773_; lean_object* v___y_786_; lean_object* v___y_787_; lean_object* v___y_788_; uint8_t v___y_789_; lean_object* v_a_790_; lean_object* v___y_793_; lean_object* v___y_794_; lean_object* v___y_795_; uint8_t v___y_796_; lean_object* v_a_797_; lean_object* v___y_800_; lean_object* v___y_801_; lean_object* v___y_802_; uint8_t v___y_803_; lean_object* v_a_804_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; uint8_t v___y_817_; lean_object* v_a_818_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v___y_823_; uint8_t v___y_824_; lean_object* v_a_825_; lean_object* v___y_828_; lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; uint8_t v___y_834_; lean_object* v___y_880_; lean_object* v___y_951_; uint8_t v___y_952_; lean_object* v___y_953_; lean_object* v___y_954_; lean_object* v_a_955_; uint8_t v___y_968_; lean_object* v___y_969_; lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v_a_972_; uint8_t v___y_982_; lean_object* v___y_983_; lean_object* v___y_984_; lean_object* v___y_985_; lean_object* v___y_1027_; 
v_toCold_750_ = lean_ctor_get(v_a_747_, 0);
v_options_751_ = lean_ctor_get(v_toCold_750_, 2);
v_exprDef_752_ = lean_ctor_get(v_ctx_743_, 0);
lean_inc(v_exprDef_752_);
v_certDef_753_ = lean_ctor_get(v_ctx_743_, 1);
lean_inc(v_certDef_753_);
lean_dec_ref(v_ctx_743_);
v_expr_754_ = lean_ctor_get(v_reflectionResult_744_, 3);
lean_inc_ref(v_expr_754_);
lean_dec_ref(v_reflectionResult_744_);
v_ref_755_ = lean_ctor_get(v_a_747_, 2);
v_inheritedTraceOptions_756_ = lean_ctor_get(v_toCold_750_, 11);
v_hasTrace_757_ = lean_ctor_get_uint8(v_options_751_, sizeof(void*)*1);
v___x_758_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__1));
v___x_759_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
v___f_760_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__4));
v___f_761_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__5));
v___x_762_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__6));
v___x_763_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__7));
v___x_764_ = lean_box(0);
v___x_765_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__10, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__10_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__10);
v___x_766_ = 1;
v___x_767_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
if (v_hasTrace_757_ == 0)
{
lean_object* v___x_1044_; 
lean_inc(v_exprDef_752_);
v___x_1044_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_exprDef_752_, v_expr_754_, v___x_765_, v_a_747_, v_a_748_);
v___y_1027_ = v___x_1044_;
goto v___jp_1026_;
}
else
{
lean_object* v___f_1045_; lean_object* v___x_1046_; uint8_t v___x_1047_; lean_object* v___y_1049_; lean_object* v___y_1050_; lean_object* v_a_1051_; lean_object* v___y_1064_; lean_object* v___y_1065_; lean_object* v_a_1066_; 
v___f_1045_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__28));
v___x_1046_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_1047_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_756_, v_options_751_, v___x_1046_);
if (v___x_1047_ == 0)
{
lean_object* v___x_1116_; uint8_t v___x_1117_; 
v___x_1116_ = l_Lean_trace_profiler;
v___x_1117_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_751_, v___x_1116_);
if (v___x_1117_ == 0)
{
lean_object* v___x_1118_; 
lean_inc(v_exprDef_752_);
v___x_1118_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_exprDef_752_, v_expr_754_, v___x_765_, v_a_747_, v_a_748_);
v___y_1027_ = v___x_1118_;
goto v___jp_1026_;
}
else
{
goto v___jp_1075_;
}
}
else
{
goto v___jp_1075_;
}
v___jp_1048_:
{
lean_object* v___x_1052_; double v___x_1053_; double v___x_1054_; double v___x_1055_; double v___x_1056_; double v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1052_ = lean_io_mono_nanos_now();
v___x_1053_ = lean_float_of_nat(v___y_1050_);
v___x_1054_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_1055_ = lean_float_div(v___x_1053_, v___x_1054_);
v___x_1056_ = lean_float_of_nat(v___x_1052_);
v___x_1057_ = lean_float_div(v___x_1056_, v___x_1054_);
v___x_1058_ = lean_box_float(v___x_1055_);
v___x_1059_ = lean_box_float(v___x_1057_);
v___x_1060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1058_);
lean_ctor_set(v___x_1060_, 1, v___x_1059_);
v___x_1061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1061_, 0, v_a_1051_);
lean_ctor_set(v___x_1061_, 1, v___x_1060_);
v___x_1062_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4(v___x_759_, v___x_766_, v___x_767_, v_options_751_, v___x_1047_, v___y_1049_, v___f_1045_, v___x_1061_, v_a_745_, v_a_746_, v_a_747_, v_a_748_);
v___y_1027_ = v___x_1062_;
goto v___jp_1026_;
}
v___jp_1063_:
{
lean_object* v___x_1067_; double v___x_1068_; double v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1067_ = lean_io_get_num_heartbeats();
v___x_1068_ = lean_float_of_nat(v___y_1065_);
v___x_1069_ = lean_float_of_nat(v___x_1067_);
v___x_1070_ = lean_box_float(v___x_1068_);
v___x_1071_ = lean_box_float(v___x_1069_);
v___x_1072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1070_);
lean_ctor_set(v___x_1072_, 1, v___x_1071_);
v___x_1073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1073_, 0, v_a_1066_);
lean_ctor_set(v___x_1073_, 1, v___x_1072_);
v___x_1074_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4(v___x_759_, v___x_766_, v___x_767_, v_options_751_, v___x_1047_, v___y_1064_, v___f_1045_, v___x_1073_, v_a_745_, v_a_746_, v_a_747_, v_a_748_);
v___y_1027_ = v___x_1074_;
goto v___jp_1026_;
}
v___jp_1075_:
{
lean_object* v___x_1076_; lean_object* v_a_1077_; lean_object* v___x_1078_; uint8_t v___x_1079_; 
v___x_1076_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_748_);
v_a_1077_ = lean_ctor_get(v___x_1076_, 0);
lean_inc(v_a_1077_);
lean_dec_ref(v___x_1076_);
v___x_1078_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1079_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_751_, v___x_1078_);
if (v___x_1079_ == 0)
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1080_ = lean_io_mono_nanos_now();
lean_inc(v_exprDef_752_);
v___x_1081_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_exprDef_752_, v_expr_754_, v___x_765_, v_a_747_, v_a_748_);
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
v___y_1049_ = v_a_1077_;
v___y_1050_ = v___x_1080_;
v_a_1051_ = v___x_1087_;
goto v___jp_1048_;
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
v___y_1049_ = v_a_1077_;
v___y_1050_ = v___x_1080_;
v_a_1051_ = v___x_1095_;
goto v___jp_1048_;
}
}
}
}
else
{
lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1098_ = lean_io_get_num_heartbeats();
lean_inc(v_exprDef_752_);
v___x_1099_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_exprDef_752_, v_expr_754_, v___x_765_, v_a_747_, v_a_748_);
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
v_a_1100_ = lean_ctor_get(v___x_1099_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1102_ = v___x_1099_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1099_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
lean_ctor_set_tag(v___x_1102_, 1);
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_a_1100_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
v___y_1064_ = v_a_1077_;
v___y_1065_ = v___x_1098_;
v_a_1066_ = v___x_1105_;
goto v___jp_1063_;
}
}
}
else
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1115_; 
v_a_1108_ = lean_ctor_get(v___x_1099_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1110_ = v___x_1099_;
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1099_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1113_; 
if (v_isShared_1111_ == 0)
{
lean_ctor_set_tag(v___x_1110_, 0);
v___x_1113_ = v___x_1110_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_a_1108_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
v___y_1064_ = v_a_1077_;
v___y_1065_ = v___x_1098_;
v_a_1066_ = v___x_1113_;
goto v___jp_1063_;
}
}
}
}
}
}
v___jp_768_:
{
lean_object* v___x_774_; double v___x_775_; double v___x_776_; double v___x_777_; double v___x_778_; double v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_774_ = lean_io_mono_nanos_now();
v___x_775_ = lean_float_of_nat(v___y_771_);
v___x_776_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_777_ = lean_float_div(v___x_775_, v___x_776_);
v___x_778_ = lean_float_of_nat(v___x_774_);
v___x_779_ = lean_float_div(v___x_778_, v___x_776_);
v___x_780_ = lean_box_float(v___x_777_);
v___x_781_ = lean_box_float(v___x_779_);
v___x_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_782_, 0, v___x_780_);
lean_ctor_set(v___x_782_, 1, v___x_781_);
v___x_783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_783_, 0, v_a_773_);
lean_ctor_set(v___x_783_, 1, v___x_782_);
v___x_784_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2(v___x_759_, v___x_766_, v___x_767_, v___y_770_, v___y_772_, v___y_769_, v___f_761_, v___x_783_, v_a_745_, v_a_746_, v_a_747_, v_a_748_);
return v___x_784_;
}
v___jp_785_:
{
lean_object* v___x_791_; 
v___x_791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_791_, 0, v_a_790_);
v___y_769_ = v___y_786_;
v___y_770_ = v___y_787_;
v___y_771_ = v___y_788_;
v___y_772_ = v___y_789_;
v_a_773_ = v___x_791_;
goto v___jp_768_;
}
v___jp_792_:
{
lean_object* v___x_798_; 
v___x_798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_798_, 0, v_a_797_);
v___y_769_ = v___y_793_;
v___y_770_ = v___y_794_;
v___y_771_ = v___y_795_;
v___y_772_ = v___y_796_;
v_a_773_ = v___x_798_;
goto v___jp_768_;
}
v___jp_799_:
{
lean_object* v___x_805_; double v___x_806_; double v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_805_ = lean_io_get_num_heartbeats();
v___x_806_ = lean_float_of_nat(v___y_800_);
v___x_807_ = lean_float_of_nat(v___x_805_);
v___x_808_ = lean_box_float(v___x_806_);
v___x_809_ = lean_box_float(v___x_807_);
v___x_810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_810_, 0, v___x_808_);
lean_ctor_set(v___x_810_, 1, v___x_809_);
v___x_811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_811_, 0, v_a_804_);
lean_ctor_set(v___x_811_, 1, v___x_810_);
v___x_812_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2(v___x_759_, v___x_766_, v___x_767_, v___y_802_, v___y_803_, v___y_801_, v___f_761_, v___x_811_, v_a_745_, v_a_746_, v_a_747_, v_a_748_);
return v___x_812_;
}
v___jp_813_:
{
lean_object* v___x_819_; 
v___x_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_819_, 0, v_a_818_);
v___y_800_ = v___y_814_;
v___y_801_ = v___y_815_;
v___y_802_ = v___y_816_;
v___y_803_ = v___y_817_;
v_a_804_ = v___x_819_;
goto v___jp_799_;
}
v___jp_820_:
{
lean_object* v___x_826_; 
v___x_826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_826_, 0, v_a_825_);
v___y_800_ = v___y_821_;
v___y_801_ = v___y_822_;
v___y_802_ = v___y_823_;
v___y_803_ = v___y_824_;
v_a_804_ = v___x_826_;
goto v___jp_799_;
}
v___jp_827_:
{
lean_object* v___x_835_; lean_object* v_a_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_878_; 
v___x_835_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_748_);
v_a_836_ = lean_ctor_get(v___x_835_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_878_ == 0)
{
v___x_838_ = v___x_835_;
v_isShared_839_ = v_isSharedCheck_878_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_a_836_);
lean_dec(v___x_835_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_878_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_840_; uint8_t v___x_841_; 
v___x_840_ = l_Lean_trace_profiler_useHeartbeats;
v___x_841_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_833_, v___x_840_);
if (v___x_841_ == 0)
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_845_; 
v___x_842_ = lean_io_mono_nanos_now();
v___x_843_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__14));
lean_inc(v___y_828_);
if (v_isShared_839_ == 0)
{
lean_ctor_set_tag(v___x_838_, 1);
lean_ctor_set(v___x_838_, 0, v___y_828_);
v___x_845_ = v___x_838_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v___y_828_);
v___x_845_ = v_reuseFailAlloc_859_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
lean_object* v___x_846_; 
lean_inc_ref(v___y_830_);
v___x_846_ = l_Lean_Meta_nativeEqTrue(v___x_843_, v___y_830_, v___x_845_, v_a_745_, v_a_746_, v_a_747_, v_a_748_);
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
lean_dec_ref(v___y_830_);
v_prf_848_ = lean_ctor_get(v_a_847_, 0);
lean_inc_ref(v_prf_848_);
lean_dec_ref_known(v_a_847_, 1);
v___x_849_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__15));
lean_inc_ref(v___y_832_);
v___x_850_ = l_Lean_Name_mkStr5(v___x_762_, v___x_758_, v___x_763_, v___y_832_, v___x_849_);
v___x_851_ = l_Lean_mkConst(v___x_850_, v___x_764_);
v___x_852_ = l_Lean_mkApp3(v___x_851_, v___y_831_, v___y_829_, v_prf_848_);
v___y_793_ = v_a_836_;
v___y_794_ = v___y_833_;
v___y_795_ = v___x_842_;
v___y_796_ = v___y_834_;
v_a_797_ = v___x_852_;
goto v___jp_792_;
}
else
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v_a_857_; 
lean_dec_ref(v___y_831_);
lean_dec_ref(v___y_829_);
v___x_853_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17);
v___x_854_ = l_Lean_indentExpr(v___y_830_);
v___x_855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_855_, 0, v___x_853_);
lean_ctor_set(v___x_855_, 1, v___x_854_);
v___x_856_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___redArg(v___x_855_, v_a_745_, v_a_746_, v_a_747_, v_a_748_);
v_a_857_ = lean_ctor_get(v___x_856_, 0);
lean_inc(v_a_857_);
lean_dec_ref(v___x_856_);
v___y_786_ = v_a_836_;
v___y_787_ = v___y_833_;
v___y_788_ = v___x_842_;
v___y_789_ = v___y_834_;
v_a_790_ = v_a_857_;
goto v___jp_785_;
}
}
else
{
lean_object* v_a_858_; 
lean_dec_ref(v___y_831_);
lean_dec_ref(v___y_830_);
lean_dec_ref(v___y_829_);
v_a_858_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_a_858_);
lean_dec_ref_known(v___x_846_, 1);
v___y_786_ = v_a_836_;
v___y_787_ = v___y_833_;
v___y_788_ = v___x_842_;
v___y_789_ = v___y_834_;
v_a_790_ = v_a_858_;
goto v___jp_785_;
}
}
}
else
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_863_; 
v___x_860_ = lean_io_get_num_heartbeats();
v___x_861_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__14));
lean_inc(v___y_828_);
if (v_isShared_839_ == 0)
{
lean_ctor_set_tag(v___x_838_, 1);
lean_ctor_set(v___x_838_, 0, v___y_828_);
v___x_863_ = v___x_838_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___y_828_);
v___x_863_ = v_reuseFailAlloc_877_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
lean_object* v___x_864_; 
lean_inc_ref(v___y_830_);
v___x_864_ = l_Lean_Meta_nativeEqTrue(v___x_861_, v___y_830_, v___x_863_, v_a_745_, v_a_746_, v_a_747_, v_a_748_);
lean_dec_ref(v___x_863_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v_a_865_; 
v_a_865_ = lean_ctor_get(v___x_864_, 0);
lean_inc(v_a_865_);
lean_dec_ref_known(v___x_864_, 1);
if (lean_obj_tag(v_a_865_) == 0)
{
lean_object* v_prf_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
lean_dec_ref(v___y_830_);
v_prf_866_ = lean_ctor_get(v_a_865_, 0);
lean_inc_ref(v_prf_866_);
lean_dec_ref_known(v_a_865_, 1);
v___x_867_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__15));
lean_inc_ref(v___y_832_);
v___x_868_ = l_Lean_Name_mkStr5(v___x_762_, v___x_758_, v___x_763_, v___y_832_, v___x_867_);
v___x_869_ = l_Lean_mkConst(v___x_868_, v___x_764_);
v___x_870_ = l_Lean_mkApp3(v___x_869_, v___y_831_, v___y_829_, v_prf_866_);
v___y_821_ = v___x_860_;
v___y_822_ = v_a_836_;
v___y_823_ = v___y_833_;
v___y_824_ = v___y_834_;
v_a_825_ = v___x_870_;
goto v___jp_820_;
}
else
{
lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v_a_875_; 
lean_dec_ref(v___y_831_);
lean_dec_ref(v___y_829_);
v___x_871_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17);
v___x_872_ = l_Lean_indentExpr(v___y_830_);
v___x_873_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_873_, 0, v___x_871_);
lean_ctor_set(v___x_873_, 1, v___x_872_);
v___x_874_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___redArg(v___x_873_, v_a_745_, v_a_746_, v_a_747_, v_a_748_);
v_a_875_ = lean_ctor_get(v___x_874_, 0);
lean_inc(v_a_875_);
lean_dec_ref(v___x_874_);
v___y_814_ = v___x_860_;
v___y_815_ = v_a_836_;
v___y_816_ = v___y_833_;
v___y_817_ = v___y_834_;
v_a_818_ = v_a_875_;
goto v___jp_813_;
}
}
else
{
lean_object* v_a_876_; 
lean_dec_ref(v___y_831_);
lean_dec_ref(v___y_830_);
lean_dec_ref(v___y_829_);
v_a_876_ = lean_ctor_get(v___x_864_, 0);
lean_inc(v_a_876_);
lean_dec_ref_known(v___x_864_, 1);
v___y_814_ = v___x_860_;
v___y_815_ = v_a_836_;
v___y_816_ = v___y_833_;
v___y_817_ = v___y_834_;
v_a_818_ = v_a_876_;
goto v___jp_813_;
}
}
}
}
}
v___jp_879_:
{
if (lean_obj_tag(v___y_880_) == 0)
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
lean_dec_ref_known(v___y_880_, 1);
v___x_881_ = l_Lean_mkConst(v_exprDef_752_, v___x_764_);
v___x_882_ = l_Lean_mkConst(v_certDef_753_, v___x_764_);
v___x_883_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__18));
v___x_884_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__21, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__21_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__21);
lean_inc_ref(v___x_882_);
lean_inc_ref(v___x_881_);
v___x_885_ = l_Lean_mkAppB(v___x_884_, v___x_881_, v___x_882_);
if (v_hasTrace_757_ == 0)
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_886_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__14));
lean_inc(v_ref_755_);
v___x_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_887_, 0, v_ref_755_);
lean_inc_ref(v___x_885_);
v___x_888_ = l_Lean_Meta_nativeEqTrue(v___x_886_, v___x_885_, v___x_887_, v_a_745_, v_a_746_, v_a_747_, v_a_748_);
lean_dec_ref_known(v___x_887_, 1);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_903_; 
v_a_889_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_903_ == 0)
{
v___x_891_ = v___x_888_;
v_isShared_892_ = v_isSharedCheck_903_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_888_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_903_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
if (lean_obj_tag(v_a_889_) == 0)
{
lean_object* v_prf_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_897_; 
lean_dec_ref(v___x_885_);
v_prf_893_ = lean_ctor_get(v_a_889_, 0);
lean_inc_ref(v_prf_893_);
lean_dec_ref_known(v_a_889_, 1);
v___x_894_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23);
v___x_895_ = l_Lean_mkApp3(v___x_894_, v___x_881_, v___x_882_, v_prf_893_);
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 0, v___x_895_);
v___x_897_ = v___x_891_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v___x_895_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
else
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
lean_del_object(v___x_891_);
lean_dec_ref(v___x_882_);
lean_dec_ref(v___x_881_);
v___x_899_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17);
v___x_900_ = l_Lean_indentExpr(v___x_885_);
v___x_901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_899_);
lean_ctor_set(v___x_901_, 1, v___x_900_);
v___x_902_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___redArg(v___x_901_, v_a_745_, v_a_746_, v_a_747_, v_a_748_);
return v___x_902_;
}
}
}
else
{
lean_object* v_a_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_911_; 
lean_dec_ref(v___x_885_);
lean_dec_ref(v___x_882_);
lean_dec_ref(v___x_881_);
v_a_904_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_911_ == 0)
{
v___x_906_ = v___x_888_;
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_a_904_);
lean_dec(v___x_888_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_909_; 
if (v_isShared_907_ == 0)
{
v___x_909_ = v___x_906_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_a_904_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
}
else
{
lean_object* v___x_912_; uint8_t v___x_913_; 
v___x_912_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_913_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_756_, v_options_751_, v___x_912_);
if (v___x_913_ == 0)
{
lean_object* v___x_914_; uint8_t v___x_915_; 
v___x_914_ = l_Lean_trace_profiler;
v___x_915_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_751_, v___x_914_);
if (v___x_915_ == 0)
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_916_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__14));
lean_inc(v_ref_755_);
v___x_917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_917_, 0, v_ref_755_);
lean_inc_ref(v___x_885_);
v___x_918_ = l_Lean_Meta_nativeEqTrue(v___x_916_, v___x_885_, v___x_917_, v_a_745_, v_a_746_, v_a_747_, v_a_748_);
lean_dec_ref_known(v___x_917_, 1);
if (lean_obj_tag(v___x_918_) == 0)
{
lean_object* v_a_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_933_; 
v_a_919_ = lean_ctor_get(v___x_918_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_933_ == 0)
{
v___x_921_ = v___x_918_;
v_isShared_922_ = v_isSharedCheck_933_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_a_919_);
lean_dec(v___x_918_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_933_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
if (lean_obj_tag(v_a_919_) == 0)
{
lean_object* v_prf_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_927_; 
lean_dec_ref(v___x_885_);
v_prf_923_ = lean_ctor_get(v_a_919_, 0);
lean_inc_ref(v_prf_923_);
lean_dec_ref_known(v_a_919_, 1);
v___x_924_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23);
v___x_925_ = l_Lean_mkApp3(v___x_924_, v___x_881_, v___x_882_, v_prf_923_);
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 0, v___x_925_);
v___x_927_ = v___x_921_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v___x_925_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
else
{
lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
lean_del_object(v___x_921_);
lean_dec_ref(v___x_882_);
lean_dec_ref(v___x_881_);
v___x_929_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17);
v___x_930_ = l_Lean_indentExpr(v___x_885_);
v___x_931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_931_, 0, v___x_929_);
lean_ctor_set(v___x_931_, 1, v___x_930_);
v___x_932_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___redArg(v___x_931_, v_a_745_, v_a_746_, v_a_747_, v_a_748_);
return v___x_932_;
}
}
}
else
{
lean_object* v_a_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_941_; 
lean_dec_ref(v___x_885_);
lean_dec_ref(v___x_882_);
lean_dec_ref(v___x_881_);
v_a_934_ = lean_ctor_get(v___x_918_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_941_ == 0)
{
v___x_936_ = v___x_918_;
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_a_934_);
lean_dec(v___x_918_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_939_; 
if (v_isShared_937_ == 0)
{
v___x_939_ = v___x_936_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_a_934_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
}
else
{
v___y_828_ = v_ref_755_;
v___y_829_ = v___x_882_;
v___y_830_ = v___x_885_;
v___y_831_ = v___x_881_;
v___y_832_ = v___x_883_;
v___y_833_ = v_options_751_;
v___y_834_ = v___x_913_;
goto v___jp_827_;
}
}
else
{
v___y_828_ = v_ref_755_;
v___y_829_ = v___x_882_;
v___y_830_ = v___x_885_;
v___y_831_ = v___x_881_;
v___y_832_ = v___x_883_;
v___y_833_ = v_options_751_;
v___y_834_ = v___x_913_;
goto v___jp_827_;
}
}
}
else
{
lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_949_; 
lean_dec(v_certDef_753_);
lean_dec(v_exprDef_752_);
v_a_942_ = lean_ctor_get(v___y_880_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___y_880_);
if (v_isSharedCheck_949_ == 0)
{
v___x_944_ = v___y_880_;
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___y_880_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_947_; 
if (v_isShared_945_ == 0)
{
v___x_947_ = v___x_944_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_a_942_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
}
v___jp_950_:
{
lean_object* v___x_956_; double v___x_957_; double v___x_958_; double v___x_959_; double v___x_960_; double v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_956_ = lean_io_mono_nanos_now();
v___x_957_ = lean_float_of_nat(v___y_951_);
v___x_958_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_959_ = lean_float_div(v___x_957_, v___x_958_);
v___x_960_ = lean_float_of_nat(v___x_956_);
v___x_961_ = lean_float_div(v___x_960_, v___x_958_);
v___x_962_ = lean_box_float(v___x_959_);
v___x_963_ = lean_box_float(v___x_961_);
v___x_964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_962_);
lean_ctor_set(v___x_964_, 1, v___x_963_);
v___x_965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_965_, 0, v_a_955_);
lean_ctor_set(v___x_965_, 1, v___x_964_);
v___x_966_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4(v___x_759_, v___x_766_, v___x_767_, v___y_953_, v___y_952_, v___y_954_, v___f_760_, v___x_965_, v_a_745_, v_a_746_, v_a_747_, v_a_748_);
v___y_880_ = v___x_966_;
goto v___jp_879_;
}
v___jp_967_:
{
lean_object* v___x_973_; double v___x_974_; double v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_973_ = lean_io_get_num_heartbeats();
v___x_974_ = lean_float_of_nat(v___y_970_);
v___x_975_ = lean_float_of_nat(v___x_973_);
v___x_976_ = lean_box_float(v___x_974_);
v___x_977_ = lean_box_float(v___x_975_);
v___x_978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_976_);
lean_ctor_set(v___x_978_, 1, v___x_977_);
v___x_979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_979_, 0, v_a_972_);
lean_ctor_set(v___x_979_, 1, v___x_978_);
v___x_980_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4(v___x_759_, v___x_766_, v___x_767_, v___y_969_, v___y_968_, v___y_971_, v___f_760_, v___x_979_, v_a_745_, v_a_746_, v_a_747_, v_a_748_);
v___y_880_ = v___x_980_;
goto v___jp_879_;
}
v___jp_981_:
{
lean_object* v___x_986_; lean_object* v_a_987_; lean_object* v___x_988_; uint8_t v___x_989_; 
v___x_986_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_748_);
v_a_987_ = lean_ctor_get(v___x_986_, 0);
lean_inc(v_a_987_);
lean_dec_ref(v___x_986_);
v___x_988_ = l_Lean_trace_profiler_useHeartbeats;
v___x_989_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_984_, v___x_988_);
if (v___x_989_ == 0)
{
lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_990_ = lean_io_mono_nanos_now();
lean_inc(v_certDef_753_);
v___x_991_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_certDef_753_, v___y_983_, v___y_985_, v_a_747_, v_a_748_);
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
v___y_951_ = v___x_990_;
v___y_952_ = v___y_982_;
v___y_953_ = v___y_984_;
v___y_954_ = v_a_987_;
v_a_955_ = v___x_997_;
goto v___jp_950_;
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
v___y_951_ = v___x_990_;
v___y_952_ = v___y_982_;
v___y_953_ = v___y_984_;
v___y_954_ = v_a_987_;
v_a_955_ = v___x_1005_;
goto v___jp_950_;
}
}
}
}
else
{
lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1008_ = lean_io_get_num_heartbeats();
lean_inc(v_certDef_753_);
v___x_1009_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_certDef_753_, v___y_983_, v___y_985_, v_a_747_, v_a_748_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1017_; 
v_a_1010_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1012_ = v___x_1009_;
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_1009_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1015_; 
if (v_isShared_1013_ == 0)
{
lean_ctor_set_tag(v___x_1012_, 1);
v___x_1015_ = v___x_1012_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_a_1010_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
v___y_968_ = v___y_982_;
v___y_969_ = v___y_984_;
v___y_970_ = v___x_1008_;
v___y_971_ = v_a_987_;
v_a_972_ = v___x_1015_;
goto v___jp_967_;
}
}
}
else
{
lean_object* v_a_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1025_; 
v_a_1018_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1020_ = v___x_1009_;
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_a_1018_);
lean_dec(v___x_1009_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1023_; 
if (v_isShared_1021_ == 0)
{
lean_ctor_set_tag(v___x_1020_, 0);
v___x_1023_ = v___x_1020_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_a_1018_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
v___y_968_ = v___y_982_;
v___y_969_ = v___y_984_;
v___y_970_ = v___x_1008_;
v___y_971_ = v_a_987_;
v_a_972_ = v___x_1023_;
goto v___jp_967_;
}
}
}
}
}
v___jp_1026_:
{
if (lean_obj_tag(v___y_1027_) == 0)
{
lean_object* v___x_1028_; lean_object* v___x_1029_; 
lean_dec_ref_known(v___y_1027_, 1);
v___x_1028_ = l_Lean_mkStrLit(v_cert_742_);
v___x_1029_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__27, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__27_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__27);
if (v_hasTrace_757_ == 0)
{
lean_object* v___x_1030_; 
lean_inc(v_certDef_753_);
v___x_1030_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_certDef_753_, v___x_1028_, v___x_1029_, v_a_747_, v_a_748_);
v___y_880_ = v___x_1030_;
goto v___jp_879_;
}
else
{
lean_object* v___x_1031_; uint8_t v___x_1032_; 
v___x_1031_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_1032_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_756_, v_options_751_, v___x_1031_);
if (v___x_1032_ == 0)
{
lean_object* v___x_1033_; uint8_t v___x_1034_; 
v___x_1033_ = l_Lean_trace_profiler;
v___x_1034_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_751_, v___x_1033_);
if (v___x_1034_ == 0)
{
lean_object* v___x_1035_; 
lean_inc(v_certDef_753_);
v___x_1035_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_certDef_753_, v___x_1028_, v___x_1029_, v_a_747_, v_a_748_);
v___y_880_ = v___x_1035_;
goto v___jp_879_;
}
else
{
v___y_982_ = v___x_1032_;
v___y_983_ = v___x_1028_;
v___y_984_ = v_options_751_;
v___y_985_ = v___x_1029_;
goto v___jp_981_;
}
}
else
{
v___y_982_ = v___x_1032_;
v___y_983_ = v___x_1028_;
v___y_984_ = v_options_751_;
v___y_985_ = v___x_1029_;
goto v___jp_981_;
}
}
}
else
{
lean_object* v_a_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1043_; 
lean_dec(v_certDef_753_);
lean_dec(v_exprDef_752_);
lean_dec_ref(v_cert_742_);
v_a_1036_ = lean_ctor_get(v___y_1027_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___y_1027_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1038_ = v___y_1027_;
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_a_1036_);
lean_dec(v___y_1027_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1041_; 
if (v_isShared_1039_ == 0)
{
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
return v___x_1041_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___boxed(lean_object* v_cert_1119_, lean_object* v_ctx_1120_, lean_object* v_reflectionResult_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_cert_1119_, v_ctx_1120_, v_reflectionResult_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_);
lean_dec(v_a_1125_);
lean_dec_ref(v_a_1124_);
lean_dec(v_a_1123_);
lean_dec_ref(v_a_1122_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3(lean_object* v_00_u03b1_1128_, lean_object* v_x_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_){
_start:
{
lean_object* v___x_1135_; 
v___x_1135_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(v_x_1129_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1136_, lean_object* v_x_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
lean_object* v_res_1143_; 
v_res_1143_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3(v_00_u03b1_1136_, v_x_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3(lean_object* v_00_u03b1_1144_, lean_object* v_msg_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
lean_object* v___x_1151_; 
v___x_1151_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___redArg(v_msg_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___boxed(lean_object* v_00_u03b1_1152_, lean_object* v_msg_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3(v_00_u03b1_1152_, v_msg_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0(lean_object* v_bvExpr_1160_, lean_object* v_x_1161_){
_start:
{
lean_object* v___x_1162_; 
v___x_1162_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast(v_bvExpr_1160_);
return v___x_1162_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1166_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__1));
v___x_1167_ = l_Lean_MessageData_ofFormat(v___x_1166_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1(lean_object* v_x_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1174_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__2);
v___x_1175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1174_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___boxed(lean_object* v_x_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1(v_x_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_);
lean_dec(v___y_1180_);
lean_dec_ref(v___y_1179_);
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
lean_dec_ref(v_x_1176_);
return v_res_1182_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__2(void){
_start:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1186_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__1));
v___x_1187_ = l_Lean_MessageData_ofFormat(v___x_1186_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2(lean_object* v_x_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_){
_start:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1194_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__2);
v___x_1195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1194_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___boxed(lean_object* v_x_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2(v_x_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_);
lean_dec(v___y_1200_);
lean_dec_ref(v___y_1199_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
lean_dec_ref(v_x_1196_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3(lean_object* v___x_1203_, lean_object* v_a_1204_, lean_object* v_x_1205_){
_start:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1206_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
v___x_1207_ = l_Std_Sat_AIG_toCNF___redArg(v___x_1203_, v___x_1206_, v_a_1204_);
lean_dec_ref(v___x_1206_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3___boxed(lean_object* v___x_1208_, lean_object* v_a_1209_, lean_object* v_x_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3(v___x_1208_, v_a_1209_, v_x_1210_);
lean_dec_ref(v___x_1208_);
return v_res_1211_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2(void){
_start:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1215_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__1));
v___x_1216_ = l_Lean_MessageData_ofFormat(v___x_1215_);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8(lean_object* v_x_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_){
_start:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1223_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2);
v___x_1224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1223_);
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___boxed(lean_object* v_x_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8(v_x_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec_ref(v_x_1225_);
return v_res_1231_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__2(void){
_start:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1235_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__1));
v___x_1236_ = l_Lean_MessageData_ofFormat(v___x_1235_);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4(lean_object* v_x_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_){
_start:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1243_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__2);
v___x_1244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1243_);
return v___x_1244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___boxed(lean_object* v_x_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4(v_x_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
lean_dec_ref(v_x_1245_);
return v_res_1251_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2_spec__3(lean_object* v_e_1252_){
_start:
{
if (lean_obj_tag(v_e_1252_) == 0)
{
uint8_t v___x_1253_; 
v___x_1253_ = 2;
return v___x_1253_;
}
else
{
uint8_t v___x_1254_; 
v___x_1254_ = 0;
return v___x_1254_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2_spec__3___boxed(lean_object* v_e_1255_){
_start:
{
uint8_t v_res_1256_; lean_object* v_r_1257_; 
v_res_1256_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2_spec__3(v_e_1255_);
lean_dec_ref(v_e_1255_);
v_r_1257_ = lean_box(v_res_1256_);
return v_r_1257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(lean_object* v_cls_1258_, uint8_t v_collapsed_1259_, lean_object* v_tag_1260_, lean_object* v_opts_1261_, uint8_t v_clsEnabled_1262_, lean_object* v_oldTraces_1263_, lean_object* v_msg_1264_, lean_object* v_resStartStop_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_){
_start:
{
lean_object* v_fst_1271_; lean_object* v_snd_1272_; lean_object* v___y_1274_; lean_object* v___y_1275_; lean_object* v_data_1276_; lean_object* v_fst_1287_; lean_object* v_snd_1288_; lean_object* v___x_1289_; uint8_t v___x_1290_; lean_object* v___y_1292_; lean_object* v_a_1293_; uint8_t v___y_1308_; double v___y_1340_; 
v_fst_1271_ = lean_ctor_get(v_resStartStop_1265_, 0);
lean_inc(v_fst_1271_);
v_snd_1272_ = lean_ctor_get(v_resStartStop_1265_, 1);
lean_inc(v_snd_1272_);
lean_dec_ref(v_resStartStop_1265_);
v_fst_1287_ = lean_ctor_get(v_snd_1272_, 0);
lean_inc(v_fst_1287_);
v_snd_1288_ = lean_ctor_get(v_snd_1272_, 1);
lean_inc(v_snd_1288_);
lean_dec(v_snd_1272_);
v___x_1289_ = l_Lean_trace_profiler;
v___x_1290_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_1261_, v___x_1289_);
if (v___x_1290_ == 0)
{
v___y_1308_ = v___x_1290_;
goto v___jp_1307_;
}
else
{
lean_object* v___x_1345_; uint8_t v___x_1346_; 
v___x_1345_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1346_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_1261_, v___x_1345_);
if (v___x_1346_ == 0)
{
lean_object* v___x_1347_; lean_object* v___x_1348_; double v___x_1349_; double v___x_1350_; double v___x_1351_; 
v___x_1347_ = l_Lean_trace_profiler_threshold;
v___x_1348_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_1261_, v___x_1347_);
v___x_1349_ = lean_float_of_nat(v___x_1348_);
v___x_1350_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3);
v___x_1351_ = lean_float_div(v___x_1349_, v___x_1350_);
v___y_1340_ = v___x_1351_;
goto v___jp_1339_;
}
else
{
lean_object* v___x_1352_; lean_object* v___x_1353_; double v___x_1354_; 
v___x_1352_ = l_Lean_trace_profiler_threshold;
v___x_1353_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_1261_, v___x_1352_);
v___x_1354_ = lean_float_of_nat(v___x_1353_);
v___y_1340_ = v___x_1354_;
goto v___jp_1339_;
}
}
v___jp_1273_:
{
lean_object* v___x_1277_; 
lean_inc(v___y_1275_);
v___x_1277_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2(v_oldTraces_1263_, v_data_1276_, v___y_1275_, v___y_1274_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
if (lean_obj_tag(v___x_1277_) == 0)
{
lean_object* v___x_1278_; 
lean_dec_ref_known(v___x_1277_, 1);
v___x_1278_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(v_fst_1271_);
return v___x_1278_;
}
else
{
lean_object* v_a_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1286_; 
lean_dec(v_fst_1271_);
v_a_1279_ = lean_ctor_get(v___x_1277_, 0);
v_isSharedCheck_1286_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1281_ = v___x_1277_;
v_isShared_1282_ = v_isSharedCheck_1286_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_a_1279_);
lean_dec(v___x_1277_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1286_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___x_1284_; 
if (v_isShared_1282_ == 0)
{
v___x_1284_ = v___x_1281_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_a_1279_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
return v___x_1284_;
}
}
}
}
v___jp_1291_:
{
uint8_t v_result_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; double v___x_1297_; lean_object* v_data_1298_; 
v_result_1294_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2_spec__3(v_fst_1271_);
v___x_1295_ = lean_box(v_result_1294_);
v___x_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1296_, 0, v___x_1295_);
v___x_1297_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0);
lean_inc_ref(v_tag_1260_);
lean_inc_ref(v___x_1296_);
lean_inc(v_cls_1258_);
v_data_1298_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1298_, 0, v_cls_1258_);
lean_ctor_set(v_data_1298_, 1, v___x_1296_);
lean_ctor_set(v_data_1298_, 2, v_tag_1260_);
lean_ctor_set_float(v_data_1298_, sizeof(void*)*3, v___x_1297_);
lean_ctor_set_float(v_data_1298_, sizeof(void*)*3 + 8, v___x_1297_);
lean_ctor_set_uint8(v_data_1298_, sizeof(void*)*3 + 16, v_collapsed_1259_);
if (v___x_1290_ == 0)
{
lean_dec_ref_known(v___x_1296_, 1);
lean_dec(v_snd_1288_);
lean_dec(v_fst_1287_);
lean_dec_ref(v_tag_1260_);
lean_dec(v_cls_1258_);
v___y_1274_ = v_a_1293_;
v___y_1275_ = v___y_1292_;
v_data_1276_ = v_data_1298_;
goto v___jp_1273_;
}
else
{
lean_object* v_data_1299_; double v___x_1300_; double v___x_1301_; 
lean_dec_ref_known(v_data_1298_, 3);
v_data_1299_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1299_, 0, v_cls_1258_);
lean_ctor_set(v_data_1299_, 1, v___x_1296_);
lean_ctor_set(v_data_1299_, 2, v_tag_1260_);
v___x_1300_ = lean_unbox_float(v_fst_1287_);
lean_dec(v_fst_1287_);
lean_ctor_set_float(v_data_1299_, sizeof(void*)*3, v___x_1300_);
v___x_1301_ = lean_unbox_float(v_snd_1288_);
lean_dec(v_snd_1288_);
lean_ctor_set_float(v_data_1299_, sizeof(void*)*3 + 8, v___x_1301_);
lean_ctor_set_uint8(v_data_1299_, sizeof(void*)*3 + 16, v_collapsed_1259_);
v___y_1274_ = v_a_1293_;
v___y_1275_ = v___y_1292_;
v_data_1276_ = v_data_1299_;
goto v___jp_1273_;
}
}
v___jp_1302_:
{
lean_object* v_ref_1303_; lean_object* v___x_1304_; 
v_ref_1303_ = lean_ctor_get(v___y_1268_, 2);
lean_inc(v___y_1269_);
lean_inc_ref(v___y_1268_);
lean_inc(v___y_1267_);
lean_inc_ref(v___y_1266_);
lean_inc(v_fst_1271_);
v___x_1304_ = lean_apply_6(v_msg_1264_, v_fst_1271_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, lean_box(0));
if (lean_obj_tag(v___x_1304_) == 0)
{
lean_object* v_a_1305_; 
v_a_1305_ = lean_ctor_get(v___x_1304_, 0);
lean_inc(v_a_1305_);
lean_dec_ref_known(v___x_1304_, 1);
v___y_1292_ = v_ref_1303_;
v_a_1293_ = v_a_1305_;
goto v___jp_1291_;
}
else
{
lean_object* v___x_1306_; 
lean_dec_ref_known(v___x_1304_, 1);
v___x_1306_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2);
v___y_1292_ = v_ref_1303_;
v_a_1293_ = v___x_1306_;
goto v___jp_1291_;
}
}
v___jp_1307_:
{
if (v_clsEnabled_1262_ == 0)
{
if (v___y_1308_ == 0)
{
lean_object* v___x_1309_; lean_object* v_traceState_1310_; lean_object* v_env_1311_; lean_object* v_nextMacroScope_1312_; lean_object* v_ngen_1313_; lean_object* v_auxDeclNGen_1314_; lean_object* v_cache_1315_; lean_object* v_recordedDeps_1316_; lean_object* v_messages_1317_; lean_object* v_infoState_1318_; lean_object* v_snapshotTasks_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1338_; 
lean_dec(v_snd_1288_);
lean_dec(v_fst_1287_);
lean_dec_ref(v_msg_1264_);
lean_dec_ref(v_tag_1260_);
lean_dec(v_cls_1258_);
v___x_1309_ = lean_st_ref_take(v___y_1269_);
v_traceState_1310_ = lean_ctor_get(v___x_1309_, 4);
v_env_1311_ = lean_ctor_get(v___x_1309_, 0);
v_nextMacroScope_1312_ = lean_ctor_get(v___x_1309_, 1);
v_ngen_1313_ = lean_ctor_get(v___x_1309_, 2);
v_auxDeclNGen_1314_ = lean_ctor_get(v___x_1309_, 3);
v_cache_1315_ = lean_ctor_get(v___x_1309_, 5);
v_recordedDeps_1316_ = lean_ctor_get(v___x_1309_, 6);
v_messages_1317_ = lean_ctor_get(v___x_1309_, 7);
v_infoState_1318_ = lean_ctor_get(v___x_1309_, 8);
v_snapshotTasks_1319_ = lean_ctor_get(v___x_1309_, 9);
v_isSharedCheck_1338_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1321_ = v___x_1309_;
v_isShared_1322_ = v_isSharedCheck_1338_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_snapshotTasks_1319_);
lean_inc(v_infoState_1318_);
lean_inc(v_messages_1317_);
lean_inc(v_recordedDeps_1316_);
lean_inc(v_cache_1315_);
lean_inc(v_traceState_1310_);
lean_inc(v_auxDeclNGen_1314_);
lean_inc(v_ngen_1313_);
lean_inc(v_nextMacroScope_1312_);
lean_inc(v_env_1311_);
lean_dec(v___x_1309_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1338_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
uint64_t v_tid_1323_; lean_object* v_traces_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1337_; 
v_tid_1323_ = lean_ctor_get_uint64(v_traceState_1310_, sizeof(void*)*1);
v_traces_1324_ = lean_ctor_get(v_traceState_1310_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v_traceState_1310_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1326_ = v_traceState_1310_;
v_isShared_1327_ = v_isSharedCheck_1337_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_traces_1324_);
lean_dec(v_traceState_1310_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1337_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1328_; lean_object* v___x_1330_; 
v___x_1328_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1263_, v_traces_1324_);
lean_dec_ref(v_traces_1324_);
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 0, v___x_1328_);
v___x_1330_ = v___x_1326_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v___x_1328_);
lean_ctor_set_uint64(v_reuseFailAlloc_1336_, sizeof(void*)*1, v_tid_1323_);
v___x_1330_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
lean_object* v___x_1332_; 
if (v_isShared_1322_ == 0)
{
lean_ctor_set(v___x_1321_, 4, v___x_1330_);
v___x_1332_ = v___x_1321_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_env_1311_);
lean_ctor_set(v_reuseFailAlloc_1335_, 1, v_nextMacroScope_1312_);
lean_ctor_set(v_reuseFailAlloc_1335_, 2, v_ngen_1313_);
lean_ctor_set(v_reuseFailAlloc_1335_, 3, v_auxDeclNGen_1314_);
lean_ctor_set(v_reuseFailAlloc_1335_, 4, v___x_1330_);
lean_ctor_set(v_reuseFailAlloc_1335_, 5, v_cache_1315_);
lean_ctor_set(v_reuseFailAlloc_1335_, 6, v_recordedDeps_1316_);
lean_ctor_set(v_reuseFailAlloc_1335_, 7, v_messages_1317_);
lean_ctor_set(v_reuseFailAlloc_1335_, 8, v_infoState_1318_);
lean_ctor_set(v_reuseFailAlloc_1335_, 9, v_snapshotTasks_1319_);
v___x_1332_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1333_ = lean_st_ref_put(v___y_1269_, v___x_1332_);
v___x_1334_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(v_fst_1271_);
return v___x_1334_;
}
}
}
}
}
else
{
goto v___jp_1302_;
}
}
else
{
goto v___jp_1302_;
}
}
v___jp_1339_:
{
double v___x_1341_; double v___x_1342_; double v___x_1343_; uint8_t v___x_1344_; 
v___x_1341_ = lean_unbox_float(v_snd_1288_);
v___x_1342_ = lean_unbox_float(v_fst_1287_);
v___x_1343_ = lean_float_sub(v___x_1341_, v___x_1342_);
v___x_1344_ = lean_float_decLt(v___y_1340_, v___x_1343_);
v___y_1308_ = v___x_1344_;
goto v___jp_1307_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___boxed(lean_object* v_cls_1355_, lean_object* v_collapsed_1356_, lean_object* v_tag_1357_, lean_object* v_opts_1358_, lean_object* v_clsEnabled_1359_, lean_object* v_oldTraces_1360_, lean_object* v_msg_1361_, lean_object* v_resStartStop_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_){
_start:
{
uint8_t v_collapsed_boxed_1368_; uint8_t v_clsEnabled_boxed_1369_; lean_object* v_res_1370_; 
v_collapsed_boxed_1368_ = lean_unbox(v_collapsed_1356_);
v_clsEnabled_boxed_1369_ = lean_unbox(v_clsEnabled_1359_);
v_res_1370_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v_cls_1355_, v_collapsed_boxed_1368_, v_tag_1357_, v_opts_1358_, v_clsEnabled_boxed_1369_, v_oldTraces_1360_, v_msg_1361_, v_resStartStop_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_);
lean_dec(v___y_1366_);
lean_dec_ref(v___y_1365_);
lean_dec(v___y_1364_);
lean_dec_ref(v___y_1363_);
lean_dec_ref(v_opts_1358_);
return v_res_1370_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5(lean_object* v_decls_1379_, lean_object* v_idx_1380_){
_start:
{
lean_object* v___x_1381_; 
v___x_1381_ = lean_array_fget_borrowed(v_decls_1379_, v_idx_1380_);
switch(lean_obj_tag(v___x_1381_))
{
case 0:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1382_ = l_Nat_reprFast(v_idx_1380_);
v___x_1383_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___closed__0));
v___x_1384_ = lean_string_append(v___x_1382_, v___x_1383_);
v___x_1385_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___closed__1));
v___x_1386_ = lean_string_append(v___x_1384_, v___x_1385_);
v___x_1387_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___closed__2));
v___x_1388_ = lean_string_append(v___x_1386_, v___x_1387_);
return v___x_1388_;
}
case 1:
{
lean_object* v_idx_1389_; lean_object* v_var_1390_; lean_object* v_idx_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; 
v_idx_1389_ = lean_ctor_get(v___x_1381_, 0);
v_var_1390_ = lean_ctor_get(v_idx_1389_, 0);
v_idx_1391_ = lean_ctor_get(v_idx_1389_, 2);
v___x_1392_ = l_Nat_reprFast(v_idx_1380_);
v___x_1393_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___closed__0));
v___x_1394_ = lean_string_append(v___x_1392_, v___x_1393_);
v___x_1395_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___closed__3));
lean_inc(v_var_1390_);
v___x_1396_ = l_Nat_reprFast(v_var_1390_);
v___x_1397_ = lean_string_append(v___x_1395_, v___x_1396_);
lean_dec_ref(v___x_1396_);
v___x_1398_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___closed__4));
v___x_1399_ = lean_string_append(v___x_1397_, v___x_1398_);
lean_inc(v_idx_1391_);
v___x_1400_ = l_Nat_reprFast(v_idx_1391_);
v___x_1401_ = lean_string_append(v___x_1399_, v___x_1400_);
lean_dec_ref(v___x_1400_);
v___x_1402_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___closed__5));
v___x_1403_ = lean_string_append(v___x_1401_, v___x_1402_);
v___x_1404_ = lean_string_append(v___x_1394_, v___x_1403_);
lean_dec_ref(v___x_1403_);
v___x_1405_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___closed__6));
v___x_1406_ = lean_string_append(v___x_1404_, v___x_1405_);
return v___x_1406_;
}
default: 
{
lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1407_ = l_Nat_reprFast(v_idx_1380_);
v___x_1408_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___closed__0));
lean_inc_ref(v___x_1407_);
v___x_1409_ = lean_string_append(v___x_1407_, v___x_1408_);
v___x_1410_ = lean_string_append(v___x_1409_, v___x_1407_);
lean_dec_ref(v___x_1407_);
v___x_1411_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___closed__7));
v___x_1412_ = lean_string_append(v___x_1410_, v___x_1411_);
return v___x_1412_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___boxed(lean_object* v_decls_1413_, lean_object* v_idx_1414_){
_start:
{
lean_object* v_res_1415_; 
v_res_1415_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5(v_decls_1413_, v_idx_1414_);
lean_dec_ref(v_decls_1413_);
return v_res_1415_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__7(lean_object* v_decls_1416_, lean_object* v_x_1417_, lean_object* v_x_1418_){
_start:
{
if (lean_obj_tag(v_x_1418_) == 0)
{
return v_x_1417_;
}
else
{
lean_object* v_key_1419_; lean_object* v_tail_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; 
v_key_1419_ = lean_ctor_get(v_x_1418_, 0);
lean_inc(v_key_1419_);
v_tail_1420_ = lean_ctor_get(v_x_1418_, 2);
lean_inc(v_tail_1420_);
lean_dec_ref_known(v_x_1418_, 3);
v___x_1421_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5(v_decls_1416_, v_key_1419_);
v___x_1422_ = lean_string_append(v_x_1417_, v___x_1421_);
lean_dec_ref(v___x_1421_);
v_x_1417_ = v___x_1422_;
v_x_1418_ = v_tail_1420_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__7___boxed(lean_object* v_decls_1424_, lean_object* v_x_1425_, lean_object* v_x_1426_){
_start:
{
lean_object* v_res_1427_; 
v_res_1427_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__7(v_decls_1424_, v_x_1425_, v_x_1426_);
lean_dec_ref(v_decls_1424_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__8(lean_object* v_decls_1428_, lean_object* v_as_1429_, size_t v_i_1430_, size_t v_stop_1431_, lean_object* v_b_1432_){
_start:
{
uint8_t v___x_1433_; 
v___x_1433_ = lean_usize_dec_eq(v_i_1430_, v_stop_1431_);
if (v___x_1433_ == 0)
{
lean_object* v___x_1434_; lean_object* v___x_1435_; size_t v___x_1436_; size_t v___x_1437_; 
v___x_1434_ = lean_array_uget_borrowed(v_as_1429_, v_i_1430_);
lean_inc(v___x_1434_);
v___x_1435_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__7(v_decls_1428_, v_b_1432_, v___x_1434_);
v___x_1436_ = ((size_t)1ULL);
v___x_1437_ = lean_usize_add(v_i_1430_, v___x_1436_);
v_i_1430_ = v___x_1437_;
v_b_1432_ = v___x_1435_;
goto _start;
}
else
{
return v_b_1432_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__8___boxed(lean_object* v_decls_1439_, lean_object* v_as_1440_, lean_object* v_i_1441_, lean_object* v_stop_1442_, lean_object* v_b_1443_){
_start:
{
size_t v_i_boxed_1444_; size_t v_stop_boxed_1445_; lean_object* v_res_1446_; 
v_i_boxed_1444_ = lean_unbox_usize(v_i_1441_);
lean_dec(v_i_1441_);
v_stop_boxed_1445_ = lean_unbox_usize(v_stop_1442_);
lean_dec(v_stop_1442_);
v_res_1446_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__8(v_decls_1439_, v_as_1440_, v_i_boxed_1444_, v_stop_boxed_1445_, v_b_1443_);
lean_dec_ref(v_as_1440_);
lean_dec_ref(v_decls_1439_);
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14_spec__17_spec__18___redArg(lean_object* v_x_1447_, lean_object* v_x_1448_){
_start:
{
if (lean_obj_tag(v_x_1448_) == 0)
{
return v_x_1447_;
}
else
{
lean_object* v_key_1449_; lean_object* v_value_1450_; lean_object* v_tail_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1474_; 
v_key_1449_ = lean_ctor_get(v_x_1448_, 0);
v_value_1450_ = lean_ctor_get(v_x_1448_, 1);
v_tail_1451_ = lean_ctor_get(v_x_1448_, 2);
v_isSharedCheck_1474_ = !lean_is_exclusive(v_x_1448_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1453_ = v_x_1448_;
v_isShared_1454_ = v_isSharedCheck_1474_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_tail_1451_);
lean_inc(v_value_1450_);
lean_inc(v_key_1449_);
lean_dec(v_x_1448_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1474_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1455_; uint64_t v___x_1456_; uint64_t v___x_1457_; uint64_t v___x_1458_; uint64_t v_fold_1459_; uint64_t v___x_1460_; uint64_t v___x_1461_; uint64_t v___x_1462_; size_t v___x_1463_; size_t v___x_1464_; size_t v___x_1465_; size_t v___x_1466_; size_t v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1470_; 
v___x_1455_ = lean_array_get_size(v_x_1447_);
v___x_1456_ = lean_uint64_of_nat(v_key_1449_);
v___x_1457_ = 32ULL;
v___x_1458_ = lean_uint64_shift_right(v___x_1456_, v___x_1457_);
v_fold_1459_ = lean_uint64_xor(v___x_1456_, v___x_1458_);
v___x_1460_ = 16ULL;
v___x_1461_ = lean_uint64_shift_right(v_fold_1459_, v___x_1460_);
v___x_1462_ = lean_uint64_xor(v_fold_1459_, v___x_1461_);
v___x_1463_ = lean_uint64_to_usize(v___x_1462_);
v___x_1464_ = lean_usize_of_nat(v___x_1455_);
v___x_1465_ = ((size_t)1ULL);
v___x_1466_ = lean_usize_sub(v___x_1464_, v___x_1465_);
v___x_1467_ = lean_usize_land(v___x_1463_, v___x_1466_);
v___x_1468_ = lean_array_uget_borrowed(v_x_1447_, v___x_1467_);
lean_inc(v___x_1468_);
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 2, v___x_1468_);
v___x_1470_ = v___x_1453_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_key_1449_);
lean_ctor_set(v_reuseFailAlloc_1473_, 1, v_value_1450_);
lean_ctor_set(v_reuseFailAlloc_1473_, 2, v___x_1468_);
v___x_1470_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
lean_object* v___x_1471_; 
v___x_1471_ = lean_array_uset(v_x_1447_, v___x_1467_, v___x_1470_);
v_x_1447_ = v___x_1471_;
v_x_1448_ = v_tail_1451_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14_spec__17___redArg(lean_object* v_i_1475_, lean_object* v_source_1476_, lean_object* v_target_1477_){
_start:
{
lean_object* v___x_1478_; uint8_t v___x_1479_; 
v___x_1478_ = lean_array_get_size(v_source_1476_);
v___x_1479_ = lean_nat_dec_lt(v_i_1475_, v___x_1478_);
if (v___x_1479_ == 0)
{
lean_dec_ref(v_source_1476_);
lean_dec(v_i_1475_);
return v_target_1477_;
}
else
{
lean_object* v_es_1480_; lean_object* v___x_1481_; lean_object* v_source_1482_; lean_object* v_target_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
v_es_1480_ = lean_array_fget(v_source_1476_, v_i_1475_);
v___x_1481_ = lean_box(0);
v_source_1482_ = lean_array_fset(v_source_1476_, v_i_1475_, v___x_1481_);
v_target_1483_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14_spec__17_spec__18___redArg(v_target_1477_, v_es_1480_);
v___x_1484_ = lean_unsigned_to_nat(1u);
v___x_1485_ = lean_nat_add(v_i_1475_, v___x_1484_);
lean_dec(v_i_1475_);
v_i_1475_ = v___x_1485_;
v_source_1476_ = v_source_1482_;
v_target_1477_ = v_target_1483_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14___redArg(lean_object* v___x_1487_, lean_object* v_data_1488_){
_start:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v_nbuckets_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1489_ = lean_array_get_size(v_data_1488_);
v___x_1490_ = lean_unsigned_to_nat(2u);
v_nbuckets_1491_ = lean_nat_mul(v___x_1489_, v___x_1490_);
v___x_1492_ = lean_unsigned_to_nat(0u);
v___x_1493_ = lean_box(0);
v___x_1494_ = lean_mk_array(v_nbuckets_1491_, v___x_1493_);
v___x_1495_ = lean_array_propagate_mark(v_data_1488_, v___x_1494_);
v___x_1496_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14_spec__17___redArg(v___x_1492_, v_data_1488_, v___x_1495_);
return v___x_1496_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14___redArg___boxed(lean_object* v___x_1497_, lean_object* v_data_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14___redArg(v___x_1497_, v_data_1498_);
lean_dec(v___x_1497_);
return v_res_1499_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7_spec__12___redArg(lean_object* v_a_1500_, lean_object* v_x_1501_){
_start:
{
if (lean_obj_tag(v_x_1501_) == 0)
{
uint8_t v___x_1502_; 
v___x_1502_ = 0;
return v___x_1502_;
}
else
{
lean_object* v_key_1503_; lean_object* v_tail_1504_; uint8_t v___x_1505_; 
v_key_1503_ = lean_ctor_get(v_x_1501_, 0);
v_tail_1504_ = lean_ctor_get(v_x_1501_, 2);
v___x_1505_ = lean_nat_dec_eq(v_key_1503_, v_a_1500_);
if (v___x_1505_ == 0)
{
v_x_1501_ = v_tail_1504_;
goto _start;
}
else
{
return v___x_1505_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7_spec__12___redArg___boxed(lean_object* v_a_1507_, lean_object* v_x_1508_){
_start:
{
uint8_t v_res_1509_; lean_object* v_r_1510_; 
v_res_1509_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7_spec__12___redArg(v_a_1507_, v_x_1508_);
lean_dec(v_x_1508_);
lean_dec(v_a_1507_);
v_r_1510_ = lean_box(v_res_1509_);
return v_r_1510_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8___redArg(lean_object* v___x_1511_, lean_object* v_m_1512_, lean_object* v_a_1513_, lean_object* v_b_1514_){
_start:
{
lean_object* v_size_1515_; lean_object* v_buckets_1516_; lean_object* v___x_1517_; uint64_t v___x_1518_; uint64_t v___x_1519_; uint64_t v___x_1520_; uint64_t v_fold_1521_; uint64_t v___x_1522_; uint64_t v___x_1523_; uint64_t v___x_1524_; size_t v___x_1525_; size_t v___x_1526_; size_t v___x_1527_; size_t v___x_1528_; size_t v___x_1529_; lean_object* v_bkt_1530_; uint8_t v___x_1531_; 
v_size_1515_ = lean_ctor_get(v_m_1512_, 0);
v_buckets_1516_ = lean_ctor_get(v_m_1512_, 1);
v___x_1517_ = lean_array_get_size(v_buckets_1516_);
v___x_1518_ = lean_uint64_of_nat(v_a_1513_);
v___x_1519_ = 32ULL;
v___x_1520_ = lean_uint64_shift_right(v___x_1518_, v___x_1519_);
v_fold_1521_ = lean_uint64_xor(v___x_1518_, v___x_1520_);
v___x_1522_ = 16ULL;
v___x_1523_ = lean_uint64_shift_right(v_fold_1521_, v___x_1522_);
v___x_1524_ = lean_uint64_xor(v_fold_1521_, v___x_1523_);
v___x_1525_ = lean_uint64_to_usize(v___x_1524_);
v___x_1526_ = lean_usize_of_nat(v___x_1517_);
v___x_1527_ = ((size_t)1ULL);
v___x_1528_ = lean_usize_sub(v___x_1526_, v___x_1527_);
v___x_1529_ = lean_usize_land(v___x_1525_, v___x_1528_);
v_bkt_1530_ = lean_array_uget_borrowed(v_buckets_1516_, v___x_1529_);
v___x_1531_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7_spec__12___redArg(v_a_1513_, v_bkt_1530_);
if (v___x_1531_ == 0)
{
lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1552_; 
lean_inc_ref(v_buckets_1516_);
lean_inc(v_size_1515_);
v_isSharedCheck_1552_ = !lean_is_exclusive(v_m_1512_);
if (v_isSharedCheck_1552_ == 0)
{
lean_object* v_unused_1553_; lean_object* v_unused_1554_; 
v_unused_1553_ = lean_ctor_get(v_m_1512_, 1);
lean_dec(v_unused_1553_);
v_unused_1554_ = lean_ctor_get(v_m_1512_, 0);
lean_dec(v_unused_1554_);
v___x_1533_ = v_m_1512_;
v_isShared_1534_ = v_isSharedCheck_1552_;
goto v_resetjp_1532_;
}
else
{
lean_dec(v_m_1512_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1552_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1535_; lean_object* v_size_x27_1536_; lean_object* v___x_1537_; lean_object* v_buckets_x27_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; uint8_t v___x_1544_; 
v___x_1535_ = lean_unsigned_to_nat(1u);
v_size_x27_1536_ = lean_nat_add(v_size_1515_, v___x_1535_);
lean_dec(v_size_1515_);
lean_inc(v_bkt_1530_);
v___x_1537_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1537_, 0, v_a_1513_);
lean_ctor_set(v___x_1537_, 1, v_b_1514_);
lean_ctor_set(v___x_1537_, 2, v_bkt_1530_);
v_buckets_x27_1538_ = lean_array_uset(v_buckets_1516_, v___x_1529_, v___x_1537_);
v___x_1539_ = lean_unsigned_to_nat(4u);
v___x_1540_ = lean_nat_mul(v_size_x27_1536_, v___x_1539_);
v___x_1541_ = lean_unsigned_to_nat(3u);
v___x_1542_ = lean_nat_div(v___x_1540_, v___x_1541_);
lean_dec(v___x_1540_);
v___x_1543_ = lean_array_get_size(v_buckets_x27_1538_);
v___x_1544_ = lean_nat_dec_le(v___x_1542_, v___x_1543_);
lean_dec(v___x_1542_);
if (v___x_1544_ == 0)
{
lean_object* v_val_1545_; lean_object* v___x_1547_; 
v_val_1545_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14___redArg(v___x_1511_, v_buckets_x27_1538_);
if (v_isShared_1534_ == 0)
{
lean_ctor_set(v___x_1533_, 1, v_val_1545_);
lean_ctor_set(v___x_1533_, 0, v_size_x27_1536_);
v___x_1547_ = v___x_1533_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_size_x27_1536_);
lean_ctor_set(v_reuseFailAlloc_1548_, 1, v_val_1545_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
return v___x_1547_;
}
}
else
{
lean_object* v___x_1550_; 
if (v_isShared_1534_ == 0)
{
lean_ctor_set(v___x_1533_, 1, v_buckets_x27_1538_);
lean_ctor_set(v___x_1533_, 0, v_size_x27_1536_);
v___x_1550_ = v___x_1533_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v_size_x27_1536_);
lean_ctor_set(v_reuseFailAlloc_1551_, 1, v_buckets_x27_1538_);
v___x_1550_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
return v___x_1550_;
}
}
}
}
else
{
lean_dec(v_b_1514_);
lean_dec(v_a_1513_);
return v_m_1512_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8___redArg___boxed(lean_object* v___x_1555_, lean_object* v_m_1556_, lean_object* v_a_1557_, lean_object* v_b_1558_){
_start:
{
lean_object* v_res_1559_; 
v_res_1559_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8___redArg(v___x_1555_, v_m_1556_, v_a_1557_, v_b_1558_);
lean_dec(v___x_1555_);
return v_res_1559_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7___redArg(lean_object* v___x_1560_, lean_object* v_m_1561_, lean_object* v_a_1562_){
_start:
{
lean_object* v_buckets_1563_; lean_object* v___x_1564_; uint64_t v___x_1565_; uint64_t v___x_1566_; uint64_t v___x_1567_; uint64_t v_fold_1568_; uint64_t v___x_1569_; uint64_t v___x_1570_; uint64_t v___x_1571_; size_t v___x_1572_; size_t v___x_1573_; size_t v___x_1574_; size_t v___x_1575_; size_t v___x_1576_; lean_object* v___x_1577_; uint8_t v___x_1578_; 
v_buckets_1563_ = lean_ctor_get(v_m_1561_, 1);
v___x_1564_ = lean_array_get_size(v_buckets_1563_);
v___x_1565_ = lean_uint64_of_nat(v_a_1562_);
v___x_1566_ = 32ULL;
v___x_1567_ = lean_uint64_shift_right(v___x_1565_, v___x_1566_);
v_fold_1568_ = lean_uint64_xor(v___x_1565_, v___x_1567_);
v___x_1569_ = 16ULL;
v___x_1570_ = lean_uint64_shift_right(v_fold_1568_, v___x_1569_);
v___x_1571_ = lean_uint64_xor(v_fold_1568_, v___x_1570_);
v___x_1572_ = lean_uint64_to_usize(v___x_1571_);
v___x_1573_ = lean_usize_of_nat(v___x_1564_);
v___x_1574_ = ((size_t)1ULL);
v___x_1575_ = lean_usize_sub(v___x_1573_, v___x_1574_);
v___x_1576_ = lean_usize_land(v___x_1572_, v___x_1575_);
v___x_1577_ = lean_array_uget_borrowed(v_buckets_1563_, v___x_1576_);
v___x_1578_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7_spec__12___redArg(v_a_1562_, v___x_1577_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7___redArg___boxed(lean_object* v___x_1579_, lean_object* v_m_1580_, lean_object* v_a_1581_){
_start:
{
uint8_t v_res_1582_; lean_object* v_r_1583_; 
v_res_1582_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7___redArg(v___x_1579_, v_m_1580_, v_a_1581_);
lean_dec(v_a_1581_);
lean_dec_ref(v_m_1580_);
lean_dec(v___x_1579_);
v_r_1583_ = lean_box(v_res_1582_);
return v_r_1583_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6___redArg(lean_object* v_acc_1587_, lean_object* v_decls_1588_, lean_object* v_idx_1589_, lean_object* v_a_1590_){
_start:
{
lean_object* v___x_1591_; uint8_t v___x_1592_; 
v___x_1591_ = lean_array_get_size(v_decls_1588_);
v___x_1592_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7___redArg(v___x_1591_, v_a_1590_, v_idx_1589_);
if (v___x_1592_ == 0)
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1593_ = lean_box(0);
lean_inc(v_idx_1589_);
v___x_1594_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8___redArg(v___x_1591_, v_a_1590_, v_idx_1589_, v___x_1593_);
v___x_1595_ = lean_array_fget_borrowed(v_decls_1588_, v_idx_1589_);
if (lean_obj_tag(v___x_1595_) == 2)
{
lean_object* v_l_1596_; lean_object* v_r_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___y_1601_; uint8_t v___y_1602_; uint8_t v___y_1603_; uint8_t v___y_1627_; lean_object* v___x_1633_; lean_object* v___x_1634_; uint8_t v___x_1635_; 
v_l_1596_ = lean_ctor_get(v___x_1595_, 0);
v_r_1597_ = lean_ctor_get(v___x_1595_, 1);
v___x_1598_ = lean_unsigned_to_nat(1u);
v___x_1599_ = lean_nat_shiftr(v_l_1596_, v___x_1598_);
v___x_1633_ = lean_nat_land(v___x_1598_, v_l_1596_);
v___x_1634_ = lean_unsigned_to_nat(0u);
v___x_1635_ = lean_nat_dec_eq(v___x_1633_, v___x_1634_);
lean_dec(v___x_1633_);
if (v___x_1635_ == 0)
{
uint8_t v___x_1636_; 
v___x_1636_ = 1;
v___y_1627_ = v___x_1636_;
goto v___jp_1626_;
}
else
{
v___y_1627_ = v___x_1592_;
goto v___jp_1626_;
}
v___jp_1600_:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v_fst_1623_; lean_object* v_snd_1624_; 
v___x_1604_ = l_Nat_reprFast(v_idx_1589_);
v___x_1605_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6___redArg___closed__0));
lean_inc_ref(v___x_1604_);
v___x_1606_ = lean_string_append(v___x_1604_, v___x_1605_);
lean_inc(v___x_1599_);
v___x_1607_ = l_Nat_reprFast(v___x_1599_);
v___x_1608_ = lean_string_append(v___x_1606_, v___x_1607_);
lean_dec_ref(v___x_1607_);
v___x_1609_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v___y_1602_);
v___x_1610_ = lean_string_append(v___x_1608_, v___x_1609_);
lean_dec_ref(v___x_1609_);
v___x_1611_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6___redArg___closed__1));
v___x_1612_ = lean_string_append(v___x_1610_, v___x_1611_);
v___x_1613_ = lean_string_append(v___x_1612_, v___x_1604_);
lean_dec_ref(v___x_1604_);
v___x_1614_ = lean_string_append(v___x_1613_, v___x_1605_);
lean_inc(v___y_1601_);
v___x_1615_ = l_Nat_reprFast(v___y_1601_);
v___x_1616_ = lean_string_append(v___x_1614_, v___x_1615_);
lean_dec_ref(v___x_1615_);
v___x_1617_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v___y_1603_);
v___x_1618_ = lean_string_append(v___x_1616_, v___x_1617_);
lean_dec_ref(v___x_1617_);
v___x_1619_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6___redArg___closed__2));
v___x_1620_ = lean_string_append(v___x_1618_, v___x_1619_);
v___x_1621_ = lean_string_append(v_acc_1587_, v___x_1620_);
lean_dec_ref(v___x_1620_);
v___x_1622_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6___redArg(v___x_1621_, v_decls_1588_, v___x_1599_, v___x_1594_);
v_fst_1623_ = lean_ctor_get(v___x_1622_, 0);
lean_inc(v_fst_1623_);
v_snd_1624_ = lean_ctor_get(v___x_1622_, 1);
lean_inc(v_snd_1624_);
lean_dec_ref(v___x_1622_);
v_acc_1587_ = v_fst_1623_;
v_idx_1589_ = v___y_1601_;
v_a_1590_ = v_snd_1624_;
goto _start;
}
v___jp_1626_:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; uint8_t v___x_1631_; 
v___x_1628_ = lean_nat_shiftr(v_r_1597_, v___x_1598_);
v___x_1629_ = lean_nat_land(v___x_1598_, v_r_1597_);
v___x_1630_ = lean_unsigned_to_nat(0u);
v___x_1631_ = lean_nat_dec_eq(v___x_1629_, v___x_1630_);
lean_dec(v___x_1629_);
if (v___x_1631_ == 0)
{
uint8_t v___x_1632_; 
v___x_1632_ = 1;
v___y_1601_ = v___x_1628_;
v___y_1602_ = v___y_1627_;
v___y_1603_ = v___x_1632_;
goto v___jp_1600_;
}
else
{
v___y_1601_ = v___x_1628_;
v___y_1602_ = v___y_1627_;
v___y_1603_ = v___x_1592_;
goto v___jp_1600_;
}
}
}
else
{
lean_object* v___x_1637_; 
lean_dec(v_idx_1589_);
v___x_1637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1637_, 0, v_acc_1587_);
lean_ctor_set(v___x_1637_, 1, v___x_1594_);
return v___x_1637_;
}
}
else
{
lean_object* v___x_1638_; 
lean_dec(v_idx_1589_);
v___x_1638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1638_, 0, v_acc_1587_);
lean_ctor_set(v___x_1638_, 1, v_a_1590_);
return v___x_1638_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6___redArg___boxed(lean_object* v_acc_1639_, lean_object* v_decls_1640_, lean_object* v_idx_1641_, lean_object* v_a_1642_){
_start:
{
lean_object* v_res_1643_; 
v_res_1643_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6___redArg(v_acc_1639_, v_decls_1640_, v_idx_1641_, v_a_1642_);
lean_dec_ref(v_decls_1640_);
return v_res_1643_;
}
}
static lean_object* _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1644_ = lean_box(0);
v___x_1645_ = lean_unsigned_to_nat(16u);
v___x_1646_ = lean_mk_array(v___x_1645_, v___x_1644_);
return v___x_1646_;
}
}
static lean_object* _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1647_ = lean_obj_once(&l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___closed__0, &l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___closed__0_once, _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___closed__0);
v___x_1648_ = lean_unsigned_to_nat(0u);
v___x_1649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1648_);
lean_ctor_set(v___x_1649_, 1, v___x_1647_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(lean_object* v_entry_1652_){
_start:
{
lean_object* v_aig_1653_; lean_object* v_ref_1654_; lean_object* v_decls_1655_; lean_object* v_gate_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v_fst_1661_; lean_object* v_snd_1662_; lean_object* v___y_1664_; lean_object* v_buckets_1670_; lean_object* v___x_1671_; uint8_t v___x_1672_; 
v_aig_1653_ = lean_ctor_get(v_entry_1652_, 0);
lean_inc_ref(v_aig_1653_);
v_ref_1654_ = lean_ctor_get(v_entry_1652_, 1);
lean_inc_ref(v_ref_1654_);
lean_dec_ref(v_entry_1652_);
v_decls_1655_ = lean_ctor_get(v_aig_1653_, 0);
lean_inc_ref(v_decls_1655_);
lean_dec_ref(v_aig_1653_);
v_gate_1656_ = lean_ctor_get(v_ref_1654_, 0);
lean_inc(v_gate_1656_);
lean_dec_ref(v_ref_1654_);
v___x_1657_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
v___x_1658_ = lean_unsigned_to_nat(0u);
v___x_1659_ = lean_obj_once(&l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___closed__1, &l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___closed__1_once, _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___closed__1);
v___x_1660_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6___redArg(v___x_1657_, v_decls_1655_, v_gate_1656_, v___x_1659_);
v_fst_1661_ = lean_ctor_get(v___x_1660_, 0);
lean_inc(v_fst_1661_);
v_snd_1662_ = lean_ctor_get(v___x_1660_, 1);
lean_inc(v_snd_1662_);
lean_dec_ref(v___x_1660_);
v_buckets_1670_ = lean_ctor_get(v_snd_1662_, 1);
lean_inc_ref(v_buckets_1670_);
lean_dec(v_snd_1662_);
v___x_1671_ = lean_array_get_size(v_buckets_1670_);
v___x_1672_ = lean_nat_dec_lt(v___x_1658_, v___x_1671_);
if (v___x_1672_ == 0)
{
lean_dec_ref(v_buckets_1670_);
lean_dec_ref(v_decls_1655_);
v___y_1664_ = v___x_1657_;
goto v___jp_1663_;
}
else
{
size_t v___x_1673_; size_t v___x_1674_; lean_object* v___x_1675_; 
v___x_1673_ = ((size_t)0ULL);
v___x_1674_ = lean_usize_of_nat(v___x_1671_);
v___x_1675_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__8(v_decls_1655_, v_buckets_1670_, v___x_1673_, v___x_1674_, v___x_1657_);
lean_dec_ref(v_buckets_1670_);
lean_dec_ref(v_decls_1655_);
v___y_1664_ = v___x_1675_;
goto v___jp_1663_;
}
v___jp_1663_:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
v___x_1665_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___closed__2));
v___x_1666_ = lean_string_append(v___x_1665_, v___y_1664_);
lean_dec_ref(v___y_1664_);
v___x_1667_ = lean_string_append(v___x_1666_, v_fst_1661_);
lean_dec(v_fst_1661_);
v___x_1668_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___closed__3));
v___x_1669_ = lean_string_append(v___x_1667_, v___x_1668_);
return v___x_1669_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(lean_object* v_cls_1678_, lean_object* v_msg_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_){
_start:
{
lean_object* v_ref_1685_; lean_object* v___x_1686_; lean_object* v_a_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1732_; 
v_ref_1685_ = lean_ctor_get(v___y_1682_, 2);
v___x_1686_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__6(v_msg_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
v_a_1687_ = lean_ctor_get(v___x_1686_, 0);
v_isSharedCheck_1732_ = !lean_is_exclusive(v___x_1686_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1689_ = v___x_1686_;
v_isShared_1690_ = v_isSharedCheck_1732_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_a_1687_);
lean_dec(v___x_1686_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1732_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v___x_1691_; lean_object* v_traceState_1692_; lean_object* v_env_1693_; lean_object* v_nextMacroScope_1694_; lean_object* v_ngen_1695_; lean_object* v_auxDeclNGen_1696_; lean_object* v_cache_1697_; lean_object* v_recordedDeps_1698_; lean_object* v_messages_1699_; lean_object* v_infoState_1700_; lean_object* v_snapshotTasks_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1731_; 
v___x_1691_ = lean_st_ref_take(v___y_1683_);
v_traceState_1692_ = lean_ctor_get(v___x_1691_, 4);
v_env_1693_ = lean_ctor_get(v___x_1691_, 0);
v_nextMacroScope_1694_ = lean_ctor_get(v___x_1691_, 1);
v_ngen_1695_ = lean_ctor_get(v___x_1691_, 2);
v_auxDeclNGen_1696_ = lean_ctor_get(v___x_1691_, 3);
v_cache_1697_ = lean_ctor_get(v___x_1691_, 5);
v_recordedDeps_1698_ = lean_ctor_get(v___x_1691_, 6);
v_messages_1699_ = lean_ctor_get(v___x_1691_, 7);
v_infoState_1700_ = lean_ctor_get(v___x_1691_, 8);
v_snapshotTasks_1701_ = lean_ctor_get(v___x_1691_, 9);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___x_1691_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1703_ = v___x_1691_;
v_isShared_1704_ = v_isSharedCheck_1731_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_snapshotTasks_1701_);
lean_inc(v_infoState_1700_);
lean_inc(v_messages_1699_);
lean_inc(v_recordedDeps_1698_);
lean_inc(v_cache_1697_);
lean_inc(v_traceState_1692_);
lean_inc(v_auxDeclNGen_1696_);
lean_inc(v_ngen_1695_);
lean_inc(v_nextMacroScope_1694_);
lean_inc(v_env_1693_);
lean_dec(v___x_1691_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1731_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
uint64_t v_tid_1705_; lean_object* v_traces_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1730_; 
v_tid_1705_ = lean_ctor_get_uint64(v_traceState_1692_, sizeof(void*)*1);
v_traces_1706_ = lean_ctor_get(v_traceState_1692_, 0);
v_isSharedCheck_1730_ = !lean_is_exclusive(v_traceState_1692_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1708_ = v_traceState_1692_;
v_isShared_1709_ = v_isSharedCheck_1730_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_traces_1706_);
lean_dec(v_traceState_1692_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1730_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1710_; lean_object* v___x_1711_; double v___x_1712_; uint8_t v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1721_; 
v___x_1710_ = lean_box(0);
v___x_1711_ = lean_box(0);
v___x_1712_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0);
v___x_1713_ = 0;
v___x_1714_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
v___x_1715_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1715_, 0, v_cls_1678_);
lean_ctor_set(v___x_1715_, 1, v___x_1711_);
lean_ctor_set(v___x_1715_, 2, v___x_1714_);
lean_ctor_set_float(v___x_1715_, sizeof(void*)*3, v___x_1712_);
lean_ctor_set_float(v___x_1715_, sizeof(void*)*3 + 8, v___x_1712_);
lean_ctor_set_uint8(v___x_1715_, sizeof(void*)*3 + 16, v___x_1713_);
v___x_1716_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0___closed__0));
v___x_1717_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1717_, 0, v___x_1715_);
lean_ctor_set(v___x_1717_, 1, v_a_1687_);
lean_ctor_set(v___x_1717_, 2, v___x_1716_);
lean_inc(v_ref_1685_);
v___x_1718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1718_, 0, v_ref_1685_);
lean_ctor_set(v___x_1718_, 1, v___x_1717_);
v___x_1719_ = l_Lean_PersistentArray_push___redArg(v_traces_1706_, v___x_1718_);
if (v_isShared_1709_ == 0)
{
lean_ctor_set(v___x_1708_, 0, v___x_1719_);
v___x_1721_ = v___x_1708_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v___x_1719_);
lean_ctor_set_uint64(v_reuseFailAlloc_1729_, sizeof(void*)*1, v_tid_1705_);
v___x_1721_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
lean_object* v___x_1723_; 
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 4, v___x_1721_);
v___x_1723_ = v___x_1703_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v_env_1693_);
lean_ctor_set(v_reuseFailAlloc_1728_, 1, v_nextMacroScope_1694_);
lean_ctor_set(v_reuseFailAlloc_1728_, 2, v_ngen_1695_);
lean_ctor_set(v_reuseFailAlloc_1728_, 3, v_auxDeclNGen_1696_);
lean_ctor_set(v_reuseFailAlloc_1728_, 4, v___x_1721_);
lean_ctor_set(v_reuseFailAlloc_1728_, 5, v_cache_1697_);
lean_ctor_set(v_reuseFailAlloc_1728_, 6, v_recordedDeps_1698_);
lean_ctor_set(v_reuseFailAlloc_1728_, 7, v_messages_1699_);
lean_ctor_set(v_reuseFailAlloc_1728_, 8, v_infoState_1700_);
lean_ctor_set(v_reuseFailAlloc_1728_, 9, v_snapshotTasks_1701_);
v___x_1723_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
lean_object* v___x_1724_; lean_object* v___x_1726_; 
v___x_1724_ = lean_st_ref_put(v___y_1683_, v___x_1723_);
if (v_isShared_1690_ == 0)
{
lean_ctor_set(v___x_1689_, 0, v___x_1710_);
v___x_1726_ = v___x_1689_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v___x_1710_);
v___x_1726_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
return v___x_1726_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0___boxed(lean_object* v_cls_1733_, lean_object* v_msg_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v_cls_1733_, v_msg_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v___y_1736_);
lean_dec_ref(v___y_1735_);
return v_res_1740_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1_spec__1(lean_object* v_e_1741_){
_start:
{
if (lean_obj_tag(v_e_1741_) == 0)
{
uint8_t v___x_1742_; 
v___x_1742_ = 2;
return v___x_1742_;
}
else
{
uint8_t v___x_1743_; 
v___x_1743_ = 0;
return v___x_1743_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1_spec__1___boxed(lean_object* v_e_1744_){
_start:
{
uint8_t v_res_1745_; lean_object* v_r_1746_; 
v_res_1745_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1_spec__1(v_e_1744_);
lean_dec_ref(v_e_1744_);
v_r_1746_ = lean_box(v_res_1745_);
return v_r_1746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(lean_object* v_cls_1747_, uint8_t v_collapsed_1748_, lean_object* v_tag_1749_, lean_object* v_opts_1750_, uint8_t v_clsEnabled_1751_, lean_object* v_oldTraces_1752_, lean_object* v_msg_1753_, lean_object* v_resStartStop_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
lean_object* v_fst_1760_; lean_object* v_snd_1761_; lean_object* v___y_1763_; lean_object* v___y_1764_; lean_object* v_data_1765_; lean_object* v_fst_1776_; lean_object* v_snd_1777_; lean_object* v___x_1778_; uint8_t v___x_1779_; lean_object* v___y_1781_; lean_object* v_a_1782_; uint8_t v___y_1797_; double v___y_1829_; 
v_fst_1760_ = lean_ctor_get(v_resStartStop_1754_, 0);
lean_inc(v_fst_1760_);
v_snd_1761_ = lean_ctor_get(v_resStartStop_1754_, 1);
lean_inc(v_snd_1761_);
lean_dec_ref(v_resStartStop_1754_);
v_fst_1776_ = lean_ctor_get(v_snd_1761_, 0);
lean_inc(v_fst_1776_);
v_snd_1777_ = lean_ctor_get(v_snd_1761_, 1);
lean_inc(v_snd_1777_);
lean_dec(v_snd_1761_);
v___x_1778_ = l_Lean_trace_profiler;
v___x_1779_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_1750_, v___x_1778_);
if (v___x_1779_ == 0)
{
v___y_1797_ = v___x_1779_;
goto v___jp_1796_;
}
else
{
lean_object* v___x_1834_; uint8_t v___x_1835_; 
v___x_1834_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1835_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_1750_, v___x_1834_);
if (v___x_1835_ == 0)
{
lean_object* v___x_1836_; lean_object* v___x_1837_; double v___x_1838_; double v___x_1839_; double v___x_1840_; 
v___x_1836_ = l_Lean_trace_profiler_threshold;
v___x_1837_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_1750_, v___x_1836_);
v___x_1838_ = lean_float_of_nat(v___x_1837_);
v___x_1839_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3);
v___x_1840_ = lean_float_div(v___x_1838_, v___x_1839_);
v___y_1829_ = v___x_1840_;
goto v___jp_1828_;
}
else
{
lean_object* v___x_1841_; lean_object* v___x_1842_; double v___x_1843_; 
v___x_1841_ = l_Lean_trace_profiler_threshold;
v___x_1842_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_1750_, v___x_1841_);
v___x_1843_ = lean_float_of_nat(v___x_1842_);
v___y_1829_ = v___x_1843_;
goto v___jp_1828_;
}
}
v___jp_1762_:
{
lean_object* v___x_1766_; 
lean_inc(v___y_1764_);
v___x_1766_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2(v_oldTraces_1752_, v_data_1765_, v___y_1764_, v___y_1763_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v___x_1767_; 
lean_dec_ref_known(v___x_1766_, 1);
v___x_1767_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(v_fst_1760_);
return v___x_1767_;
}
else
{
lean_object* v_a_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1775_; 
lean_dec(v_fst_1760_);
v_a_1768_ = lean_ctor_get(v___x_1766_, 0);
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1770_ = v___x_1766_;
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_a_1768_);
lean_dec(v___x_1766_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1773_; 
if (v_isShared_1771_ == 0)
{
v___x_1773_ = v___x_1770_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_a_1768_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
}
}
v___jp_1780_:
{
uint8_t v_result_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; double v___x_1786_; lean_object* v_data_1787_; 
v_result_1783_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1_spec__1(v_fst_1760_);
v___x_1784_ = lean_box(v_result_1783_);
v___x_1785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1785_, 0, v___x_1784_);
v___x_1786_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0);
lean_inc_ref(v_tag_1749_);
lean_inc_ref(v___x_1785_);
lean_inc(v_cls_1747_);
v_data_1787_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1787_, 0, v_cls_1747_);
lean_ctor_set(v_data_1787_, 1, v___x_1785_);
lean_ctor_set(v_data_1787_, 2, v_tag_1749_);
lean_ctor_set_float(v_data_1787_, sizeof(void*)*3, v___x_1786_);
lean_ctor_set_float(v_data_1787_, sizeof(void*)*3 + 8, v___x_1786_);
lean_ctor_set_uint8(v_data_1787_, sizeof(void*)*3 + 16, v_collapsed_1748_);
if (v___x_1779_ == 0)
{
lean_dec_ref_known(v___x_1785_, 1);
lean_dec(v_snd_1777_);
lean_dec(v_fst_1776_);
lean_dec_ref(v_tag_1749_);
lean_dec(v_cls_1747_);
v___y_1763_ = v_a_1782_;
v___y_1764_ = v___y_1781_;
v_data_1765_ = v_data_1787_;
goto v___jp_1762_;
}
else
{
lean_object* v_data_1788_; double v___x_1789_; double v___x_1790_; 
lean_dec_ref_known(v_data_1787_, 3);
v_data_1788_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1788_, 0, v_cls_1747_);
lean_ctor_set(v_data_1788_, 1, v___x_1785_);
lean_ctor_set(v_data_1788_, 2, v_tag_1749_);
v___x_1789_ = lean_unbox_float(v_fst_1776_);
lean_dec(v_fst_1776_);
lean_ctor_set_float(v_data_1788_, sizeof(void*)*3, v___x_1789_);
v___x_1790_ = lean_unbox_float(v_snd_1777_);
lean_dec(v_snd_1777_);
lean_ctor_set_float(v_data_1788_, sizeof(void*)*3 + 8, v___x_1790_);
lean_ctor_set_uint8(v_data_1788_, sizeof(void*)*3 + 16, v_collapsed_1748_);
v___y_1763_ = v_a_1782_;
v___y_1764_ = v___y_1781_;
v_data_1765_ = v_data_1788_;
goto v___jp_1762_;
}
}
v___jp_1791_:
{
lean_object* v_ref_1792_; lean_object* v___x_1793_; 
v_ref_1792_ = lean_ctor_get(v___y_1757_, 2);
lean_inc(v___y_1758_);
lean_inc_ref(v___y_1757_);
lean_inc(v___y_1756_);
lean_inc_ref(v___y_1755_);
lean_inc(v_fst_1760_);
v___x_1793_ = lean_apply_6(v_msg_1753_, v_fst_1760_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, lean_box(0));
if (lean_obj_tag(v___x_1793_) == 0)
{
lean_object* v_a_1794_; 
v_a_1794_ = lean_ctor_get(v___x_1793_, 0);
lean_inc(v_a_1794_);
lean_dec_ref_known(v___x_1793_, 1);
v___y_1781_ = v_ref_1792_;
v_a_1782_ = v_a_1794_;
goto v___jp_1780_;
}
else
{
lean_object* v___x_1795_; 
lean_dec_ref_known(v___x_1793_, 1);
v___x_1795_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2);
v___y_1781_ = v_ref_1792_;
v_a_1782_ = v___x_1795_;
goto v___jp_1780_;
}
}
v___jp_1796_:
{
if (v_clsEnabled_1751_ == 0)
{
if (v___y_1797_ == 0)
{
lean_object* v___x_1798_; lean_object* v_traceState_1799_; lean_object* v_env_1800_; lean_object* v_nextMacroScope_1801_; lean_object* v_ngen_1802_; lean_object* v_auxDeclNGen_1803_; lean_object* v_cache_1804_; lean_object* v_recordedDeps_1805_; lean_object* v_messages_1806_; lean_object* v_infoState_1807_; lean_object* v_snapshotTasks_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1827_; 
lean_dec(v_snd_1777_);
lean_dec(v_fst_1776_);
lean_dec_ref(v_msg_1753_);
lean_dec_ref(v_tag_1749_);
lean_dec(v_cls_1747_);
v___x_1798_ = lean_st_ref_take(v___y_1758_);
v_traceState_1799_ = lean_ctor_get(v___x_1798_, 4);
v_env_1800_ = lean_ctor_get(v___x_1798_, 0);
v_nextMacroScope_1801_ = lean_ctor_get(v___x_1798_, 1);
v_ngen_1802_ = lean_ctor_get(v___x_1798_, 2);
v_auxDeclNGen_1803_ = lean_ctor_get(v___x_1798_, 3);
v_cache_1804_ = lean_ctor_get(v___x_1798_, 5);
v_recordedDeps_1805_ = lean_ctor_get(v___x_1798_, 6);
v_messages_1806_ = lean_ctor_get(v___x_1798_, 7);
v_infoState_1807_ = lean_ctor_get(v___x_1798_, 8);
v_snapshotTasks_1808_ = lean_ctor_get(v___x_1798_, 9);
v_isSharedCheck_1827_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1810_ = v___x_1798_;
v_isShared_1811_ = v_isSharedCheck_1827_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_snapshotTasks_1808_);
lean_inc(v_infoState_1807_);
lean_inc(v_messages_1806_);
lean_inc(v_recordedDeps_1805_);
lean_inc(v_cache_1804_);
lean_inc(v_traceState_1799_);
lean_inc(v_auxDeclNGen_1803_);
lean_inc(v_ngen_1802_);
lean_inc(v_nextMacroScope_1801_);
lean_inc(v_env_1800_);
lean_dec(v___x_1798_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1827_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
uint64_t v_tid_1812_; lean_object* v_traces_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1826_; 
v_tid_1812_ = lean_ctor_get_uint64(v_traceState_1799_, sizeof(void*)*1);
v_traces_1813_ = lean_ctor_get(v_traceState_1799_, 0);
v_isSharedCheck_1826_ = !lean_is_exclusive(v_traceState_1799_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1815_ = v_traceState_1799_;
v_isShared_1816_ = v_isSharedCheck_1826_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_traces_1813_);
lean_dec(v_traceState_1799_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1826_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1817_; lean_object* v___x_1819_; 
v___x_1817_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1752_, v_traces_1813_);
lean_dec_ref(v_traces_1813_);
if (v_isShared_1816_ == 0)
{
lean_ctor_set(v___x_1815_, 0, v___x_1817_);
v___x_1819_ = v___x_1815_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v___x_1817_);
lean_ctor_set_uint64(v_reuseFailAlloc_1825_, sizeof(void*)*1, v_tid_1812_);
v___x_1819_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
lean_object* v___x_1821_; 
if (v_isShared_1811_ == 0)
{
lean_ctor_set(v___x_1810_, 4, v___x_1819_);
v___x_1821_ = v___x_1810_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v_env_1800_);
lean_ctor_set(v_reuseFailAlloc_1824_, 1, v_nextMacroScope_1801_);
lean_ctor_set(v_reuseFailAlloc_1824_, 2, v_ngen_1802_);
lean_ctor_set(v_reuseFailAlloc_1824_, 3, v_auxDeclNGen_1803_);
lean_ctor_set(v_reuseFailAlloc_1824_, 4, v___x_1819_);
lean_ctor_set(v_reuseFailAlloc_1824_, 5, v_cache_1804_);
lean_ctor_set(v_reuseFailAlloc_1824_, 6, v_recordedDeps_1805_);
lean_ctor_set(v_reuseFailAlloc_1824_, 7, v_messages_1806_);
lean_ctor_set(v_reuseFailAlloc_1824_, 8, v_infoState_1807_);
lean_ctor_set(v_reuseFailAlloc_1824_, 9, v_snapshotTasks_1808_);
v___x_1821_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; 
v___x_1822_ = lean_st_ref_put(v___y_1758_, v___x_1821_);
v___x_1823_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(v_fst_1760_);
return v___x_1823_;
}
}
}
}
}
else
{
goto v___jp_1791_;
}
}
else
{
goto v___jp_1791_;
}
}
v___jp_1828_:
{
double v___x_1830_; double v___x_1831_; double v___x_1832_; uint8_t v___x_1833_; 
v___x_1830_ = lean_unbox_float(v_snd_1777_);
v___x_1831_ = lean_unbox_float(v_fst_1776_);
v___x_1832_ = lean_float_sub(v___x_1830_, v___x_1831_);
v___x_1833_ = lean_float_decLt(v___y_1829_, v___x_1832_);
v___y_1797_ = v___x_1833_;
goto v___jp_1796_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1___boxed(lean_object* v_cls_1844_, lean_object* v_collapsed_1845_, lean_object* v_tag_1846_, lean_object* v_opts_1847_, lean_object* v_clsEnabled_1848_, lean_object* v_oldTraces_1849_, lean_object* v_msg_1850_, lean_object* v_resStartStop_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_){
_start:
{
uint8_t v_collapsed_boxed_1857_; uint8_t v_clsEnabled_boxed_1858_; lean_object* v_res_1859_; 
v_collapsed_boxed_1857_ = lean_unbox(v_collapsed_1845_);
v_clsEnabled_boxed_1858_ = lean_unbox(v_clsEnabled_1848_);
v_res_1859_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v_cls_1844_, v_collapsed_boxed_1857_, v_tag_1846_, v_opts_1847_, v_clsEnabled_boxed_1858_, v_oldTraces_1849_, v_msg_1850_, v_resStartStop_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_);
lean_dec(v___y_1855_);
lean_dec_ref(v___y_1854_);
lean_dec(v___y_1853_);
lean_dec_ref(v___y_1852_);
lean_dec_ref(v_opts_1847_);
return v_res_1859_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1(void){
_start:
{
lean_object* v___x_1861_; lean_object* v___x_1862_; 
v___x_1861_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__0));
v___x_1862_ = l_Lean_stringToMessageData(v___x_1861_);
return v___x_1862_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3(void){
_start:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; 
v___x_1864_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__2));
v___x_1865_ = l_Lean_stringToMessageData(v___x_1864_);
return v___x_1865_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6(void){
_start:
{
lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; 
v___x_1868_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__5));
v___x_1869_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__4));
v___x_1870_ = l_System_FilePath_join(v___x_1869_, v___x_1868_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6(lean_object* v_ctx_1871_, lean_object* v_aig_1872_, lean_object* v_atomsAssignment_1873_, lean_object* v_goal_1874_, lean_object* v_unusedHypotheses_1875_, lean_object* v_reflectionResult_1876_, uint8_t v___x_1877_, lean_object* v___x_1878_, lean_object* v___f_1879_, lean_object* v___x_1880_, lean_object* v___f_1881_, lean_object* v___f_1882_, lean_object* v___x_1883_, lean_object* v___x_1884_, lean_object* v_a_1885_, lean_object* v_____r_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_){
_start:
{
lean_object* v___y_1893_; lean_object* v___y_1899_; lean_object* v___y_1900_; lean_object* v___y_1901_; lean_object* v___y_1902_; lean_object* v___y_1903_; lean_object* v___y_1924_; lean_object* v___y_1925_; lean_object* v___y_1926_; lean_object* v___y_1927_; lean_object* v___y_1928_; lean_object* v___y_1929_; uint8_t v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_1980_; lean_object* v___y_1981_; lean_object* v___y_1982_; lean_object* v___y_1983_; lean_object* v___y_1984_; lean_object* v___y_1985_; lean_object* v___y_1986_; lean_object* v_a_1987_; uint8_t v___y_2000_; lean_object* v___y_2001_; lean_object* v___y_2002_; lean_object* v___y_2003_; lean_object* v___y_2004_; lean_object* v___y_2005_; lean_object* v___y_2006_; lean_object* v___y_2007_; lean_object* v___y_2008_; lean_object* v_a_2009_; uint8_t v___y_2019_; lean_object* v___y_2020_; lean_object* v___y_2021_; lean_object* v___y_2022_; lean_object* v___y_2023_; uint8_t v___y_2024_; uint8_t v___y_2025_; lean_object* v___y_2026_; lean_object* v___y_2027_; lean_object* v___y_2028_; lean_object* v___y_2029_; lean_object* v___y_2030_; lean_object* v___y_2031_; uint8_t v___y_2032_; lean_object* v_config_2072_; lean_object* v_solver_2073_; lean_object* v_lratPath_2074_; lean_object* v_timeout_2075_; uint8_t v_trimProofs_2076_; uint8_t v_binaryProofs_2077_; uint8_t v_graphviz_2078_; uint8_t v_solverMode_2079_; lean_object* v___y_2081_; lean_object* v___y_2082_; lean_object* v___y_2083_; lean_object* v___y_2084_; lean_object* v___y_2085_; lean_object* v_options_2086_; lean_object* v_inheritedTraceOptions_2087_; lean_object* v_a_2088_; lean_object* v___y_2096_; lean_object* v___y_2097_; lean_object* v___y_2098_; lean_object* v___y_2099_; lean_object* v___y_2100_; lean_object* v_a_2101_; lean_object* v___y_2104_; lean_object* v___y_2105_; lean_object* v___y_2106_; lean_object* v___y_2107_; lean_object* v___y_2108_; lean_object* v___y_2109_; lean_object* v___y_2125_; lean_object* v___y_2126_; lean_object* v___y_2127_; lean_object* v___y_2128_; lean_object* v___y_2129_; lean_object* v___y_2130_; lean_object* v___y_2131_; lean_object* v___y_2132_; uint8_t v___y_2133_; lean_object* v_a_2134_; lean_object* v___y_2144_; lean_object* v___y_2145_; lean_object* v___y_2146_; lean_object* v___y_2147_; lean_object* v___y_2148_; lean_object* v___y_2149_; lean_object* v___y_2150_; lean_object* v___y_2151_; uint8_t v___y_2152_; lean_object* v_a_2153_; lean_object* v___y_2166_; lean_object* v___y_2167_; lean_object* v___y_2168_; lean_object* v___y_2169_; lean_object* v___y_2170_; lean_object* v___y_2171_; lean_object* v___y_2172_; uint8_t v___y_2173_; lean_object* v___y_2230_; lean_object* v___y_2231_; lean_object* v___y_2232_; lean_object* v_toCold_2233_; lean_object* v_ref_2234_; lean_object* v___y_2235_; 
v_config_2072_ = lean_ctor_get(v_ctx_1871_, 5);
v_solver_2073_ = lean_ctor_get(v_ctx_1871_, 3);
v_lratPath_2074_ = lean_ctor_get(v_ctx_1871_, 4);
v_timeout_2075_ = lean_ctor_get(v_config_2072_, 0);
v_trimProofs_2076_ = lean_ctor_get_uint8(v_config_2072_, sizeof(void*)*2);
v_binaryProofs_2077_ = lean_ctor_get_uint8(v_config_2072_, sizeof(void*)*2 + 1);
v_graphviz_2078_ = lean_ctor_get_uint8(v_config_2072_, sizeof(void*)*2 + 8);
v_solverMode_2079_ = lean_ctor_get_uint8(v_config_2072_, sizeof(void*)*2 + 10);
if (v_graphviz_2078_ == 0)
{
lean_object* v_toCold_2274_; lean_object* v_ref_2275_; 
lean_dec_ref(v_a_1885_);
v_toCold_2274_ = lean_ctor_get(v___y_1889_, 0);
v_ref_2275_ = lean_ctor_get(v___y_1889_, 2);
v___y_2230_ = v___y_1887_;
v___y_2231_ = v___y_1888_;
v___y_2232_ = v___y_1889_;
v_toCold_2233_ = v_toCold_2274_;
v_ref_2234_ = v_ref_2275_;
v___y_2235_ = v___y_1890_;
goto v___jp_2229_;
}
else
{
lean_object* v_toCold_2276_; lean_object* v_ref_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; 
v_toCold_2276_ = lean_ctor_get(v___y_1889_, 0);
v_ref_2277_ = lean_ctor_get(v___y_1889_, 2);
v___x_2278_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6);
v___x_2279_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v_a_1885_);
v___x_2280_ = l_IO_FS_writeFile(v___x_2278_, v___x_2279_);
lean_dec_ref(v___x_2279_);
if (lean_obj_tag(v___x_2280_) == 0)
{
lean_dec_ref_known(v___x_2280_, 1);
v___y_2230_ = v___y_1887_;
v___y_2231_ = v___y_1888_;
v___y_2232_ = v___y_1889_;
v_toCold_2233_ = v_toCold_2276_;
v_ref_2234_ = v_ref_2277_;
v___y_2235_ = v___y_1890_;
goto v___jp_2229_;
}
else
{
lean_object* v_a_2281_; lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2292_; 
lean_dec_ref(v___x_1884_);
lean_dec_ref(v___x_1883_);
lean_dec_ref(v___f_1882_);
lean_dec_ref(v___f_1881_);
lean_dec_ref(v___f_1879_);
lean_dec_ref(v___x_1878_);
lean_dec_ref(v_reflectionResult_1876_);
lean_dec_ref(v_unusedHypotheses_1875_);
lean_dec(v_goal_1874_);
lean_dec_ref(v_aig_1872_);
lean_dec_ref(v_ctx_1871_);
v_a_2281_ = lean_ctor_get(v___x_2280_, 0);
v_isSharedCheck_2292_ = !lean_is_exclusive(v___x_2280_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2283_ = v___x_2280_;
v_isShared_2284_ = v_isSharedCheck_2292_;
goto v_resetjp_2282_;
}
else
{
lean_inc(v_a_2281_);
lean_dec(v___x_2280_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2292_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2290_; 
v___x_2285_ = lean_io_error_to_string(v_a_2281_);
v___x_2286_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2285_);
v___x_2287_ = l_Lean_MessageData_ofFormat(v___x_2286_);
lean_inc(v_ref_2277_);
v___x_2288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2288_, 0, v_ref_2277_);
lean_ctor_set(v___x_2288_, 1, v___x_2287_);
if (v_isShared_2284_ == 0)
{
lean_ctor_set(v___x_2283_, 0, v___x_2288_);
v___x_2290_ = v___x_2283_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v___x_2288_);
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
v___jp_1892_:
{
lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1894_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v_aig_1872_, v___y_1893_, v_atomsAssignment_1873_);
lean_dec_ref(v___y_1893_);
v___x_1895_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1895_, 0, v_goal_1874_);
lean_ctor_set(v___x_1895_, 1, v_unusedHypotheses_1875_);
lean_ctor_set(v___x_1895_, 2, v___x_1894_);
v___x_1896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1895_);
v___x_1897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1896_);
return v___x_1897_;
}
v___jp_1898_:
{
lean_object* v___x_1904_; 
lean_inc_ref(v___y_1899_);
v___x_1904_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_1899_, v_ctx_1871_, v_reflectionResult_1876_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
if (lean_obj_tag(v___x_1904_) == 0)
{
lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1914_; 
v_a_1905_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1907_ = v___x_1904_;
v_isShared_1908_ = v_isSharedCheck_1914_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_dec(v___x_1904_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1914_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1912_; 
v___x_1909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1909_, 0, v_a_1905_);
lean_ctor_set(v___x_1909_, 1, v___y_1899_);
v___x_1910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1910_, 0, v___x_1909_);
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 0, v___x_1910_);
v___x_1912_ = v___x_1907_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v___x_1910_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
}
else
{
lean_object* v_a_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1922_; 
lean_dec_ref(v___y_1899_);
v_a_1915_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1917_ = v___x_1904_;
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_a_1915_);
lean_dec(v___x_1904_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1920_; 
if (v_isShared_1918_ == 0)
{
v___x_1920_ = v___x_1917_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v_a_1915_);
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
v___jp_1923_:
{
if (lean_obj_tag(v___y_1929_) == 0)
{
lean_object* v_a_1930_; 
v_a_1930_ = lean_ctor_get(v___y_1929_, 0);
lean_inc(v_a_1930_);
lean_dec_ref_known(v___y_1929_, 1);
if (lean_obj_tag(v_a_1930_) == 0)
{
lean_object* v_toCold_1931_; lean_object* v_options_1932_; uint8_t v_hasTrace_1933_; 
lean_dec_ref(v_reflectionResult_1876_);
lean_dec_ref(v_ctx_1871_);
v_toCold_1931_ = lean_ctor_get(v___y_1928_, 0);
v_options_1932_ = lean_ctor_get(v_toCold_1931_, 2);
v_hasTrace_1933_ = lean_ctor_get_uint8(v_options_1932_, sizeof(void*)*1);
if (v_hasTrace_1933_ == 0)
{
lean_object* v_a_1934_; 
lean_dec(v___y_1925_);
v_a_1934_ = lean_ctor_get(v_a_1930_, 0);
lean_inc(v_a_1934_);
lean_dec_ref_known(v_a_1930_, 1);
v___y_1893_ = v_a_1934_;
goto v___jp_1892_;
}
else
{
lean_object* v_a_1935_; lean_object* v_inheritedTraceOptions_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; uint8_t v___x_1939_; 
v_a_1935_ = lean_ctor_get(v_a_1930_, 0);
lean_inc(v_a_1935_);
lean_dec_ref_known(v_a_1930_, 1);
v_inheritedTraceOptions_1936_ = lean_ctor_get(v_toCold_1931_, 11);
v___x_1937_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___y_1925_);
v___x_1938_ = l_Lean_Name_append(v___x_1937_, v___y_1925_);
v___x_1939_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1936_, v_options_1932_, v___x_1938_);
lean_dec(v___x_1938_);
if (v___x_1939_ == 0)
{
lean_dec(v___y_1925_);
v___y_1893_ = v_a_1935_;
goto v___jp_1892_;
}
else
{
lean_object* v___x_1940_; lean_object* v___x_1941_; 
v___x_1940_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1);
v___x_1941_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v___y_1925_, v___x_1940_, v___y_1924_, v___y_1927_, v___y_1928_, v___y_1926_);
if (lean_obj_tag(v___x_1941_) == 0)
{
lean_dec_ref_known(v___x_1941_, 1);
v___y_1893_ = v_a_1935_;
goto v___jp_1892_;
}
else
{
lean_object* v_a_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1949_; 
lean_dec(v_a_1935_);
lean_dec_ref(v_unusedHypotheses_1875_);
lean_dec(v_goal_1874_);
lean_dec_ref(v_aig_1872_);
v_a_1942_ = lean_ctor_get(v___x_1941_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1941_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1944_ = v___x_1941_;
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_a_1942_);
lean_dec(v___x_1941_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1947_; 
if (v_isShared_1945_ == 0)
{
v___x_1947_ = v___x_1944_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_a_1942_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
}
}
}
else
{
lean_object* v_toCold_1950_; lean_object* v_options_1951_; uint8_t v_hasTrace_1952_; 
lean_dec_ref(v_unusedHypotheses_1875_);
lean_dec(v_goal_1874_);
lean_dec_ref(v_aig_1872_);
v_toCold_1950_ = lean_ctor_get(v___y_1928_, 0);
v_options_1951_ = lean_ctor_get(v_toCold_1950_, 2);
v_hasTrace_1952_ = lean_ctor_get_uint8(v_options_1951_, sizeof(void*)*1);
if (v_hasTrace_1952_ == 0)
{
lean_object* v_a_1953_; 
lean_dec(v___y_1925_);
v_a_1953_ = lean_ctor_get(v_a_1930_, 0);
lean_inc(v_a_1953_);
lean_dec_ref_known(v_a_1930_, 1);
v___y_1899_ = v_a_1953_;
v___y_1900_ = v___y_1924_;
v___y_1901_ = v___y_1927_;
v___y_1902_ = v___y_1928_;
v___y_1903_ = v___y_1926_;
goto v___jp_1898_;
}
else
{
lean_object* v_a_1954_; lean_object* v_inheritedTraceOptions_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; uint8_t v___x_1958_; 
v_a_1954_ = lean_ctor_get(v_a_1930_, 0);
lean_inc(v_a_1954_);
lean_dec_ref_known(v_a_1930_, 1);
v_inheritedTraceOptions_1955_ = lean_ctor_get(v_toCold_1950_, 11);
v___x_1956_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___y_1925_);
v___x_1957_ = l_Lean_Name_append(v___x_1956_, v___y_1925_);
v___x_1958_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1955_, v_options_1951_, v___x_1957_);
lean_dec(v___x_1957_);
if (v___x_1958_ == 0)
{
lean_dec(v___y_1925_);
v___y_1899_ = v_a_1954_;
v___y_1900_ = v___y_1924_;
v___y_1901_ = v___y_1927_;
v___y_1902_ = v___y_1928_;
v___y_1903_ = v___y_1926_;
goto v___jp_1898_;
}
else
{
lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1959_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3);
v___x_1960_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v___y_1925_, v___x_1959_, v___y_1924_, v___y_1927_, v___y_1928_, v___y_1926_);
if (lean_obj_tag(v___x_1960_) == 0)
{
lean_dec_ref_known(v___x_1960_, 1);
v___y_1899_ = v_a_1954_;
v___y_1900_ = v___y_1924_;
v___y_1901_ = v___y_1927_;
v___y_1902_ = v___y_1928_;
v___y_1903_ = v___y_1926_;
goto v___jp_1898_;
}
else
{
lean_object* v_a_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1968_; 
lean_dec(v_a_1954_);
lean_dec_ref(v_reflectionResult_1876_);
lean_dec_ref(v_ctx_1871_);
v_a_1961_ = lean_ctor_get(v___x_1960_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1963_ = v___x_1960_;
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v___x_1960_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1966_; 
if (v_isShared_1964_ == 0)
{
v___x_1966_ = v___x_1963_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_a_1961_);
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
else
{
lean_object* v_a_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1976_; 
lean_dec(v___y_1925_);
lean_dec_ref(v_reflectionResult_1876_);
lean_dec_ref(v_unusedHypotheses_1875_);
lean_dec(v_goal_1874_);
lean_dec_ref(v_aig_1872_);
lean_dec_ref(v_ctx_1871_);
v_a_1969_ = lean_ctor_get(v___y_1929_, 0);
v_isSharedCheck_1976_ = !lean_is_exclusive(v___y_1929_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1971_ = v___y_1929_;
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_a_1969_);
lean_dec(v___y_1929_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___x_1974_; 
if (v_isShared_1972_ == 0)
{
v___x_1974_ = v___x_1971_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v_a_1969_);
v___x_1974_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
return v___x_1974_;
}
}
}
}
v___jp_1977_:
{
lean_object* v___x_1988_; double v___x_1989_; double v___x_1990_; double v___x_1991_; double v___x_1992_; double v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1988_ = lean_io_mono_nanos_now();
v___x_1989_ = lean_float_of_nat(v___y_1981_);
v___x_1990_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_1991_ = lean_float_div(v___x_1989_, v___x_1990_);
v___x_1992_ = lean_float_of_nat(v___x_1988_);
v___x_1993_ = lean_float_div(v___x_1992_, v___x_1990_);
v___x_1994_ = lean_box_float(v___x_1991_);
v___x_1995_ = lean_box_float(v___x_1993_);
v___x_1996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1996_, 0, v___x_1994_);
lean_ctor_set(v___x_1996_, 1, v___x_1995_);
v___x_1997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1997_, 0, v_a_1987_);
lean_ctor_set(v___x_1997_, 1, v___x_1996_);
lean_inc(v___y_1980_);
v___x_1998_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_1980_, v___x_1877_, v___x_1878_, v___y_1985_, v___y_1978_, v___y_1984_, v___f_1879_, v___x_1997_, v___y_1979_, v___y_1983_, v___y_1986_, v___y_1982_);
v___y_1924_ = v___y_1979_;
v___y_1925_ = v___y_1980_;
v___y_1926_ = v___y_1982_;
v___y_1927_ = v___y_1983_;
v___y_1928_ = v___y_1986_;
v___y_1929_ = v___x_1998_;
goto v___jp_1923_;
}
v___jp_1999_:
{
lean_object* v___x_2010_; double v___x_2011_; double v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; 
v___x_2010_ = lean_io_get_num_heartbeats();
v___x_2011_ = lean_float_of_nat(v___y_2004_);
v___x_2012_ = lean_float_of_nat(v___x_2010_);
v___x_2013_ = lean_box_float(v___x_2011_);
v___x_2014_ = lean_box_float(v___x_2012_);
v___x_2015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2015_, 0, v___x_2013_);
lean_ctor_set(v___x_2015_, 1, v___x_2014_);
v___x_2016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2016_, 0, v_a_2009_);
lean_ctor_set(v___x_2016_, 1, v___x_2015_);
lean_inc(v___y_2002_);
v___x_2017_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_2002_, v___x_1877_, v___x_1878_, v___y_2007_, v___y_2000_, v___y_2006_, v___f_1879_, v___x_2016_, v___y_2001_, v___y_2005_, v___y_2008_, v___y_2003_);
v___y_1924_ = v___y_2001_;
v___y_1925_ = v___y_2002_;
v___y_1926_ = v___y_2003_;
v___y_1927_ = v___y_2005_;
v___y_1928_ = v___y_2008_;
v___y_1929_ = v___x_2017_;
goto v___jp_1923_;
}
v___jp_2018_:
{
lean_object* v___x_2033_; lean_object* v_a_2034_; uint8_t v___x_2035_; 
v___x_2033_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_2022_);
v_a_2034_ = lean_ctor_get(v___x_2033_, 0);
lean_inc(v_a_2034_);
lean_dec_ref(v___x_2033_);
v___x_2035_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_2023_, v___x_1880_);
if (v___x_2035_ == 0)
{
lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2036_ = lean_io_mono_nanos_now();
v___x_2037_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_2026_, v___y_2029_, v___y_2027_, v___y_2032_, v___y_2020_, v___y_2025_, v___y_2024_, v___y_2031_, v___y_2022_);
if (lean_obj_tag(v___x_2037_) == 0)
{
lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2045_; 
v_a_2038_ = lean_ctor_get(v___x_2037_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2040_ = v___x_2037_;
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_dec(v___x_2037_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2043_; 
if (v_isShared_2041_ == 0)
{
lean_ctor_set_tag(v___x_2040_, 1);
v___x_2043_ = v___x_2040_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_a_2038_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
v___y_1978_ = v___y_2019_;
v___y_1979_ = v___y_2021_;
v___y_1980_ = v___y_2028_;
v___y_1981_ = v___x_2036_;
v___y_1982_ = v___y_2022_;
v___y_1983_ = v___y_2030_;
v___y_1984_ = v_a_2034_;
v___y_1985_ = v___y_2023_;
v___y_1986_ = v___y_2031_;
v_a_1987_ = v___x_2043_;
goto v___jp_1977_;
}
}
}
else
{
lean_object* v_a_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2053_; 
v_a_2046_ = lean_ctor_get(v___x_2037_, 0);
v_isSharedCheck_2053_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_2048_ = v___x_2037_;
v_isShared_2049_ = v_isSharedCheck_2053_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_a_2046_);
lean_dec(v___x_2037_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2053_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
lean_object* v___x_2051_; 
if (v_isShared_2049_ == 0)
{
lean_ctor_set_tag(v___x_2048_, 0);
v___x_2051_ = v___x_2048_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v_a_2046_);
v___x_2051_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
v___y_1978_ = v___y_2019_;
v___y_1979_ = v___y_2021_;
v___y_1980_ = v___y_2028_;
v___y_1981_ = v___x_2036_;
v___y_1982_ = v___y_2022_;
v___y_1983_ = v___y_2030_;
v___y_1984_ = v_a_2034_;
v___y_1985_ = v___y_2023_;
v___y_1986_ = v___y_2031_;
v_a_1987_ = v___x_2051_;
goto v___jp_1977_;
}
}
}
}
else
{
lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2054_ = lean_io_get_num_heartbeats();
v___x_2055_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_2026_, v___y_2029_, v___y_2027_, v___y_2032_, v___y_2020_, v___y_2025_, v___y_2024_, v___y_2031_, v___y_2022_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v_a_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2063_; 
v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2058_ = v___x_2055_;
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_a_2056_);
lean_dec(v___x_2055_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2061_; 
if (v_isShared_2059_ == 0)
{
lean_ctor_set_tag(v___x_2058_, 1);
v___x_2061_ = v___x_2058_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_a_2056_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
v___y_2000_ = v___y_2019_;
v___y_2001_ = v___y_2021_;
v___y_2002_ = v___y_2028_;
v___y_2003_ = v___y_2022_;
v___y_2004_ = v___x_2054_;
v___y_2005_ = v___y_2030_;
v___y_2006_ = v_a_2034_;
v___y_2007_ = v___y_2023_;
v___y_2008_ = v___y_2031_;
v_a_2009_ = v___x_2061_;
goto v___jp_1999_;
}
}
}
else
{
lean_object* v_a_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2071_; 
v_a_2064_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2066_ = v___x_2055_;
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_a_2064_);
lean_dec(v___x_2055_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2069_; 
if (v_isShared_2067_ == 0)
{
lean_ctor_set_tag(v___x_2066_, 0);
v___x_2069_ = v___x_2066_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_a_2064_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
v___y_2000_ = v___y_2019_;
v___y_2001_ = v___y_2021_;
v___y_2002_ = v___y_2028_;
v___y_2003_ = v___y_2022_;
v___y_2004_ = v___x_2054_;
v___y_2005_ = v___y_2030_;
v___y_2006_ = v_a_2034_;
v___y_2007_ = v___y_2023_;
v___y_2008_ = v___y_2031_;
v_a_2009_ = v___x_2069_;
goto v___jp_1999_;
}
}
}
}
}
v___jp_2080_:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; uint8_t v___x_2091_; 
v___x_2089_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___y_2081_);
v___x_2090_ = l_Lean_Name_append(v___x_2089_, v___y_2081_);
v___x_2091_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2087_, v_options_2086_, v___x_2090_);
lean_dec(v___x_2090_);
if (v___x_2091_ == 0)
{
lean_object* v___x_2092_; uint8_t v___x_2093_; 
v___x_2092_ = l_Lean_trace_profiler;
v___x_2093_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_2086_, v___x_2092_);
if (v___x_2093_ == 0)
{
lean_object* v___x_2094_; 
lean_dec_ref(v___f_1879_);
lean_dec_ref(v___x_1878_);
lean_inc(v_timeout_2075_);
lean_inc_ref(v_lratPath_2074_);
lean_inc_ref(v_solver_2073_);
v___x_2094_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_a_2088_, v_solver_2073_, v_lratPath_2074_, v_trimProofs_2076_, v_timeout_2075_, v_binaryProofs_2077_, v_solverMode_2079_, v___y_2085_, v___y_2083_);
v___y_1924_ = v___y_2082_;
v___y_1925_ = v___y_2081_;
v___y_1926_ = v___y_2083_;
v___y_1927_ = v___y_2084_;
v___y_1928_ = v___y_2085_;
v___y_1929_ = v___x_2094_;
goto v___jp_1923_;
}
else
{
lean_inc_ref(v_solver_2073_);
lean_inc_ref(v_lratPath_2074_);
lean_inc(v_timeout_2075_);
v___y_2019_ = v___x_2091_;
v___y_2020_ = v_timeout_2075_;
v___y_2021_ = v___y_2082_;
v___y_2022_ = v___y_2083_;
v___y_2023_ = v_options_2086_;
v___y_2024_ = v_solverMode_2079_;
v___y_2025_ = v_binaryProofs_2077_;
v___y_2026_ = v_a_2088_;
v___y_2027_ = v_lratPath_2074_;
v___y_2028_ = v___y_2081_;
v___y_2029_ = v_solver_2073_;
v___y_2030_ = v___y_2084_;
v___y_2031_ = v___y_2085_;
v___y_2032_ = v_trimProofs_2076_;
goto v___jp_2018_;
}
}
else
{
lean_inc_ref(v_solver_2073_);
lean_inc_ref(v_lratPath_2074_);
lean_inc(v_timeout_2075_);
v___y_2019_ = v___x_2091_;
v___y_2020_ = v_timeout_2075_;
v___y_2021_ = v___y_2082_;
v___y_2022_ = v___y_2083_;
v___y_2023_ = v_options_2086_;
v___y_2024_ = v_solverMode_2079_;
v___y_2025_ = v_binaryProofs_2077_;
v___y_2026_ = v_a_2088_;
v___y_2027_ = v_lratPath_2074_;
v___y_2028_ = v___y_2081_;
v___y_2029_ = v_solver_2073_;
v___y_2030_ = v___y_2084_;
v___y_2031_ = v___y_2085_;
v___y_2032_ = v_trimProofs_2076_;
goto v___jp_2018_;
}
}
v___jp_2095_:
{
lean_object* v___x_2102_; 
lean_inc(v_timeout_2075_);
lean_inc_ref(v_lratPath_2074_);
lean_inc_ref(v_solver_2073_);
v___x_2102_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_a_2101_, v_solver_2073_, v_lratPath_2074_, v_trimProofs_2076_, v_timeout_2075_, v_binaryProofs_2077_, v_solverMode_2079_, v___y_2100_, v___y_2098_);
v___y_1924_ = v___y_2097_;
v___y_1925_ = v___y_2096_;
v___y_1926_ = v___y_2098_;
v___y_1927_ = v___y_2099_;
v___y_1928_ = v___y_2100_;
v___y_1929_ = v___x_2102_;
goto v___jp_1923_;
}
v___jp_2103_:
{
if (lean_obj_tag(v___y_2109_) == 0)
{
lean_object* v_toCold_2110_; lean_object* v_options_2111_; uint8_t v_hasTrace_2112_; 
v_toCold_2110_ = lean_ctor_get(v___y_2108_, 0);
v_options_2111_ = lean_ctor_get(v_toCold_2110_, 2);
v_hasTrace_2112_ = lean_ctor_get_uint8(v_options_2111_, sizeof(void*)*1);
if (v_hasTrace_2112_ == 0)
{
lean_object* v_a_2113_; 
lean_dec_ref(v___f_1879_);
lean_dec_ref(v___x_1878_);
v_a_2113_ = lean_ctor_get(v___y_2109_, 0);
lean_inc(v_a_2113_);
lean_dec_ref_known(v___y_2109_, 1);
v___y_2096_ = v___y_2105_;
v___y_2097_ = v___y_2104_;
v___y_2098_ = v___y_2106_;
v___y_2099_ = v___y_2107_;
v___y_2100_ = v___y_2108_;
v_a_2101_ = v_a_2113_;
goto v___jp_2095_;
}
else
{
lean_object* v_a_2114_; lean_object* v_inheritedTraceOptions_2115_; 
v_a_2114_ = lean_ctor_get(v___y_2109_, 0);
lean_inc(v_a_2114_);
lean_dec_ref_known(v___y_2109_, 1);
v_inheritedTraceOptions_2115_ = lean_ctor_get(v_toCold_2110_, 11);
v___y_2081_ = v___y_2105_;
v___y_2082_ = v___y_2104_;
v___y_2083_ = v___y_2106_;
v___y_2084_ = v___y_2107_;
v___y_2085_ = v___y_2108_;
v_options_2086_ = v_options_2111_;
v_inheritedTraceOptions_2087_ = v_inheritedTraceOptions_2115_;
v_a_2088_ = v_a_2114_;
goto v___jp_2080_;
}
}
else
{
lean_object* v_a_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2123_; 
lean_dec(v___y_2105_);
lean_dec_ref(v___f_1879_);
lean_dec_ref(v___x_1878_);
lean_dec_ref(v_reflectionResult_1876_);
lean_dec_ref(v_unusedHypotheses_1875_);
lean_dec(v_goal_1874_);
lean_dec_ref(v_aig_1872_);
lean_dec_ref(v_ctx_1871_);
v_a_2116_ = lean_ctor_get(v___y_2109_, 0);
v_isSharedCheck_2123_ = !lean_is_exclusive(v___y_2109_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2118_ = v___y_2109_;
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_a_2116_);
lean_dec(v___y_2109_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2121_; 
if (v_isShared_2119_ == 0)
{
v___x_2121_ = v___x_2118_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v_a_2116_);
v___x_2121_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
return v___x_2121_;
}
}
}
}
v___jp_2124_:
{
lean_object* v___x_2135_; double v___x_2136_; double v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2135_ = lean_io_get_num_heartbeats();
v___x_2136_ = lean_float_of_nat(v___y_2132_);
v___x_2137_ = lean_float_of_nat(v___x_2135_);
v___x_2138_ = lean_box_float(v___x_2136_);
v___x_2139_ = lean_box_float(v___x_2137_);
v___x_2140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2140_, 0, v___x_2138_);
lean_ctor_set(v___x_2140_, 1, v___x_2139_);
v___x_2141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2141_, 0, v_a_2134_);
lean_ctor_set(v___x_2141_, 1, v___x_2140_);
lean_inc_ref(v___x_1878_);
lean_inc(v___y_2126_);
v___x_2142_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_2126_, v___x_1877_, v___x_1878_, v___y_2131_, v___y_2133_, v___y_2129_, v___f_1881_, v___x_2141_, v___y_2125_, v___y_2128_, v___y_2130_, v___y_2127_);
v___y_2104_ = v___y_2125_;
v___y_2105_ = v___y_2126_;
v___y_2106_ = v___y_2127_;
v___y_2107_ = v___y_2128_;
v___y_2108_ = v___y_2130_;
v___y_2109_ = v___x_2142_;
goto v___jp_2103_;
}
v___jp_2143_:
{
lean_object* v___x_2154_; double v___x_2155_; double v___x_2156_; double v___x_2157_; double v___x_2158_; double v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; 
v___x_2154_ = lean_io_mono_nanos_now();
v___x_2155_ = lean_float_of_nat(v___y_2147_);
v___x_2156_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_2157_ = lean_float_div(v___x_2155_, v___x_2156_);
v___x_2158_ = lean_float_of_nat(v___x_2154_);
v___x_2159_ = lean_float_div(v___x_2158_, v___x_2156_);
v___x_2160_ = lean_box_float(v___x_2157_);
v___x_2161_ = lean_box_float(v___x_2159_);
v___x_2162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2160_);
lean_ctor_set(v___x_2162_, 1, v___x_2161_);
v___x_2163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2163_, 0, v_a_2153_);
lean_ctor_set(v___x_2163_, 1, v___x_2162_);
lean_inc_ref(v___x_1878_);
lean_inc(v___y_2145_);
v___x_2164_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_2145_, v___x_1877_, v___x_1878_, v___y_2151_, v___y_2152_, v___y_2149_, v___f_1881_, v___x_2163_, v___y_2144_, v___y_2148_, v___y_2150_, v___y_2146_);
v___y_2104_ = v___y_2144_;
v___y_2105_ = v___y_2145_;
v___y_2106_ = v___y_2146_;
v___y_2107_ = v___y_2148_;
v___y_2108_ = v___y_2150_;
v___y_2109_ = v___x_2164_;
goto v___jp_2103_;
}
v___jp_2165_:
{
lean_object* v___x_2174_; lean_object* v_a_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2228_; 
v___x_2174_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_2168_);
v_a_2175_ = lean_ctor_get(v___x_2174_, 0);
v_isSharedCheck_2228_ = !lean_is_exclusive(v___x_2174_);
if (v_isSharedCheck_2228_ == 0)
{
v___x_2177_ = v___x_2174_;
v_isShared_2178_ = v_isSharedCheck_2228_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_a_2175_);
lean_dec(v___x_2174_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2228_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
uint8_t v___x_2179_; 
v___x_2179_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_2171_, v___x_1880_);
if (v___x_2179_ == 0)
{
lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2180_ = lean_io_mono_nanos_now();
v___x_2181_ = l_IO_lazyPure___redArg(v___f_1882_);
if (lean_obj_tag(v___x_2181_) == 0)
{
lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2189_; 
lean_del_object(v___x_2177_);
v_a_2182_ = lean_ctor_get(v___x_2181_, 0);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2181_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2184_ = v___x_2181_;
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_dec(v___x_2181_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
lean_object* v___x_2187_; 
if (v_isShared_2185_ == 0)
{
lean_ctor_set_tag(v___x_2184_, 1);
v___x_2187_ = v___x_2184_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_a_2182_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
v___y_2144_ = v___y_2167_;
v___y_2145_ = v___y_2166_;
v___y_2146_ = v___y_2168_;
v___y_2147_ = v___x_2180_;
v___y_2148_ = v___y_2169_;
v___y_2149_ = v_a_2175_;
v___y_2150_ = v___y_2170_;
v___y_2151_ = v___y_2171_;
v___y_2152_ = v___y_2173_;
v_a_2153_ = v___x_2187_;
goto v___jp_2143_;
}
}
}
else
{
lean_object* v_a_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2203_; 
v_a_2190_ = lean_ctor_get(v___x_2181_, 0);
v_isSharedCheck_2203_ = !lean_is_exclusive(v___x_2181_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2192_ = v___x_2181_;
v_isShared_2193_ = v_isSharedCheck_2203_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_a_2190_);
lean_dec(v___x_2181_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2203_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2194_; lean_object* v___x_2196_; 
v___x_2194_ = lean_io_error_to_string(v_a_2190_);
if (v_isShared_2193_ == 0)
{
lean_ctor_set_tag(v___x_2192_, 3);
lean_ctor_set(v___x_2192_, 0, v___x_2194_);
v___x_2196_ = v___x_2192_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v___x_2194_);
v___x_2196_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2200_; 
v___x_2197_ = l_Lean_MessageData_ofFormat(v___x_2196_);
lean_inc(v___y_2172_);
v___x_2198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2198_, 0, v___y_2172_);
lean_ctor_set(v___x_2198_, 1, v___x_2197_);
if (v_isShared_2178_ == 0)
{
lean_ctor_set(v___x_2177_, 0, v___x_2198_);
v___x_2200_ = v___x_2177_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v___x_2198_);
v___x_2200_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
v___y_2144_ = v___y_2167_;
v___y_2145_ = v___y_2166_;
v___y_2146_ = v___y_2168_;
v___y_2147_ = v___x_2180_;
v___y_2148_ = v___y_2169_;
v___y_2149_ = v_a_2175_;
v___y_2150_ = v___y_2170_;
v___y_2151_ = v___y_2171_;
v___y_2152_ = v___y_2173_;
v_a_2153_ = v___x_2200_;
goto v___jp_2143_;
}
}
}
}
}
else
{
lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2204_ = lean_io_get_num_heartbeats();
v___x_2205_ = l_IO_lazyPure___redArg(v___f_1882_);
if (lean_obj_tag(v___x_2205_) == 0)
{
lean_object* v_a_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2213_; 
lean_del_object(v___x_2177_);
v_a_2206_ = lean_ctor_get(v___x_2205_, 0);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2208_ = v___x_2205_;
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_a_2206_);
lean_dec(v___x_2205_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2211_; 
if (v_isShared_2209_ == 0)
{
lean_ctor_set_tag(v___x_2208_, 1);
v___x_2211_ = v___x_2208_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v_a_2206_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
v___y_2125_ = v___y_2167_;
v___y_2126_ = v___y_2166_;
v___y_2127_ = v___y_2168_;
v___y_2128_ = v___y_2169_;
v___y_2129_ = v_a_2175_;
v___y_2130_ = v___y_2170_;
v___y_2131_ = v___y_2171_;
v___y_2132_ = v___x_2204_;
v___y_2133_ = v___y_2173_;
v_a_2134_ = v___x_2211_;
goto v___jp_2124_;
}
}
}
else
{
lean_object* v_a_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2227_; 
v_a_2214_ = lean_ctor_get(v___x_2205_, 0);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2216_ = v___x_2205_;
v_isShared_2217_ = v_isSharedCheck_2227_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_a_2214_);
lean_dec(v___x_2205_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2227_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___x_2218_; lean_object* v___x_2220_; 
v___x_2218_ = lean_io_error_to_string(v_a_2214_);
if (v_isShared_2217_ == 0)
{
lean_ctor_set_tag(v___x_2216_, 3);
lean_ctor_set(v___x_2216_, 0, v___x_2218_);
v___x_2220_ = v___x_2216_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v___x_2218_);
v___x_2220_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2224_; 
v___x_2221_ = l_Lean_MessageData_ofFormat(v___x_2220_);
lean_inc(v___y_2172_);
v___x_2222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2222_, 0, v___y_2172_);
lean_ctor_set(v___x_2222_, 1, v___x_2221_);
if (v_isShared_2178_ == 0)
{
lean_ctor_set(v___x_2177_, 0, v___x_2222_);
v___x_2224_ = v___x_2177_;
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
v___y_2125_ = v___y_2167_;
v___y_2126_ = v___y_2166_;
v___y_2127_ = v___y_2168_;
v___y_2128_ = v___y_2169_;
v___y_2129_ = v_a_2175_;
v___y_2130_ = v___y_2170_;
v___y_2131_ = v___y_2171_;
v___y_2132_ = v___x_2204_;
v___y_2133_ = v___y_2173_;
v_a_2134_ = v___x_2224_;
goto v___jp_2124_;
}
}
}
}
}
}
}
v___jp_2229_:
{
lean_object* v_options_2236_; lean_object* v_inheritedTraceOptions_2237_; uint8_t v_hasTrace_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
v_options_2236_ = lean_ctor_get(v_toCold_2233_, 2);
v_inheritedTraceOptions_2237_ = lean_ctor_get(v_toCold_2233_, 11);
v_hasTrace_2238_ = lean_ctor_get_uint8(v_options_2236_, sizeof(void*)*1);
v___x_2239_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__2));
v___x_2240_ = l_Lean_Name_mkStr3(v___x_1883_, v___x_1884_, v___x_2239_);
if (v_hasTrace_2238_ == 0)
{
lean_object* v___x_2241_; 
lean_dec_ref(v___f_1881_);
lean_dec_ref(v___f_1879_);
lean_dec_ref(v___x_1878_);
v___x_2241_ = l_IO_lazyPure___redArg(v___f_1882_);
if (lean_obj_tag(v___x_2241_) == 0)
{
lean_object* v_a_2242_; 
v_a_2242_ = lean_ctor_get(v___x_2241_, 0);
lean_inc(v_a_2242_);
lean_dec_ref_known(v___x_2241_, 1);
v___y_2096_ = v___x_2240_;
v___y_2097_ = v___y_2230_;
v___y_2098_ = v___y_2235_;
v___y_2099_ = v___y_2231_;
v___y_2100_ = v___y_2232_;
v_a_2101_ = v_a_2242_;
goto v___jp_2095_;
}
else
{
lean_object* v_a_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2254_; 
lean_dec(v___x_2240_);
lean_dec_ref(v_reflectionResult_1876_);
lean_dec_ref(v_unusedHypotheses_1875_);
lean_dec(v_goal_1874_);
lean_dec_ref(v_aig_1872_);
lean_dec_ref(v_ctx_1871_);
v_a_2243_ = lean_ctor_get(v___x_2241_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2241_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2245_ = v___x_2241_;
v_isShared_2246_ = v_isSharedCheck_2254_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_a_2243_);
lean_dec(v___x_2241_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2254_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2252_; 
v___x_2247_ = lean_io_error_to_string(v_a_2243_);
v___x_2248_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2248_, 0, v___x_2247_);
v___x_2249_ = l_Lean_MessageData_ofFormat(v___x_2248_);
lean_inc(v_ref_2234_);
v___x_2250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2250_, 0, v_ref_2234_);
lean_ctor_set(v___x_2250_, 1, v___x_2249_);
if (v_isShared_2246_ == 0)
{
lean_ctor_set(v___x_2245_, 0, v___x_2250_);
v___x_2252_ = v___x_2245_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v___x_2250_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
}
}
}
}
else
{
lean_object* v___x_2255_; lean_object* v___x_2256_; uint8_t v___x_2257_; 
v___x_2255_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___x_2240_);
v___x_2256_ = l_Lean_Name_append(v___x_2255_, v___x_2240_);
v___x_2257_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2237_, v_options_2236_, v___x_2256_);
lean_dec(v___x_2256_);
if (v___x_2257_ == 0)
{
lean_object* v___x_2258_; uint8_t v___x_2259_; 
v___x_2258_ = l_Lean_trace_profiler;
v___x_2259_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_2236_, v___x_2258_);
if (v___x_2259_ == 0)
{
lean_object* v___x_2260_; 
lean_dec_ref(v___f_1881_);
v___x_2260_ = l_IO_lazyPure___redArg(v___f_1882_);
if (lean_obj_tag(v___x_2260_) == 0)
{
lean_object* v_a_2261_; 
v_a_2261_ = lean_ctor_get(v___x_2260_, 0);
lean_inc(v_a_2261_);
lean_dec_ref_known(v___x_2260_, 1);
v___y_2081_ = v___x_2240_;
v___y_2082_ = v___y_2230_;
v___y_2083_ = v___y_2235_;
v___y_2084_ = v___y_2231_;
v___y_2085_ = v___y_2232_;
v_options_2086_ = v_options_2236_;
v_inheritedTraceOptions_2087_ = v_inheritedTraceOptions_2237_;
v_a_2088_ = v_a_2261_;
goto v___jp_2080_;
}
else
{
lean_object* v_a_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2273_; 
lean_dec(v___x_2240_);
lean_dec_ref(v___f_1879_);
lean_dec_ref(v___x_1878_);
lean_dec_ref(v_reflectionResult_1876_);
lean_dec_ref(v_unusedHypotheses_1875_);
lean_dec(v_goal_1874_);
lean_dec_ref(v_aig_1872_);
lean_dec_ref(v_ctx_1871_);
v_a_2262_ = lean_ctor_get(v___x_2260_, 0);
v_isSharedCheck_2273_ = !lean_is_exclusive(v___x_2260_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2264_ = v___x_2260_;
v_isShared_2265_ = v_isSharedCheck_2273_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_a_2262_);
lean_dec(v___x_2260_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2273_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2271_; 
v___x_2266_ = lean_io_error_to_string(v_a_2262_);
v___x_2267_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2267_, 0, v___x_2266_);
v___x_2268_ = l_Lean_MessageData_ofFormat(v___x_2267_);
lean_inc(v_ref_2234_);
v___x_2269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2269_, 0, v_ref_2234_);
lean_ctor_set(v___x_2269_, 1, v___x_2268_);
if (v_isShared_2265_ == 0)
{
lean_ctor_set(v___x_2264_, 0, v___x_2269_);
v___x_2271_ = v___x_2264_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v___x_2269_);
v___x_2271_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
return v___x_2271_;
}
}
}
}
else
{
v___y_2166_ = v___x_2240_;
v___y_2167_ = v___y_2230_;
v___y_2168_ = v___y_2235_;
v___y_2169_ = v___y_2231_;
v___y_2170_ = v___y_2232_;
v___y_2171_ = v_options_2236_;
v___y_2172_ = v_ref_2234_;
v___y_2173_ = v___x_2257_;
goto v___jp_2165_;
}
}
else
{
v___y_2166_ = v___x_2240_;
v___y_2167_ = v___y_2230_;
v___y_2168_ = v___y_2235_;
v___y_2169_ = v___y_2231_;
v___y_2170_ = v___y_2232_;
v___y_2171_ = v_options_2236_;
v___y_2172_ = v_ref_2234_;
v___y_2173_ = v___x_2257_;
goto v___jp_2165_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___boxed(lean_object** _args){
lean_object* v_ctx_2293_ = _args[0];
lean_object* v_aig_2294_ = _args[1];
lean_object* v_atomsAssignment_2295_ = _args[2];
lean_object* v_goal_2296_ = _args[3];
lean_object* v_unusedHypotheses_2297_ = _args[4];
lean_object* v_reflectionResult_2298_ = _args[5];
lean_object* v___x_2299_ = _args[6];
lean_object* v___x_2300_ = _args[7];
lean_object* v___f_2301_ = _args[8];
lean_object* v___x_2302_ = _args[9];
lean_object* v___f_2303_ = _args[10];
lean_object* v___f_2304_ = _args[11];
lean_object* v___x_2305_ = _args[12];
lean_object* v___x_2306_ = _args[13];
lean_object* v_a_2307_ = _args[14];
lean_object* v_____r_2308_ = _args[15];
lean_object* v___y_2309_ = _args[16];
lean_object* v___y_2310_ = _args[17];
lean_object* v___y_2311_ = _args[18];
lean_object* v___y_2312_ = _args[19];
lean_object* v___y_2313_ = _args[20];
_start:
{
uint8_t v___x_68699__boxed_2314_; lean_object* v_res_2315_; 
v___x_68699__boxed_2314_ = lean_unbox(v___x_2299_);
v_res_2315_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6(v_ctx_2293_, v_aig_2294_, v_atomsAssignment_2295_, v_goal_2296_, v_unusedHypotheses_2297_, v_reflectionResult_2298_, v___x_68699__boxed_2314_, v___x_2300_, v___f_2301_, v___x_2302_, v___f_2303_, v___f_2304_, v___x_2305_, v___x_2306_, v_a_2307_, v_____r_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_);
lean_dec(v___y_2312_);
lean_dec_ref(v___y_2311_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
lean_dec_ref(v___x_2302_);
lean_dec_ref(v_atomsAssignment_2295_);
return v_res_2315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(lean_object* v_ctx_2316_, lean_object* v_aig_2317_, lean_object* v_atomsAssignment_2318_, lean_object* v_goal_2319_, lean_object* v_unusedHypotheses_2320_, lean_object* v_reflectionResult_2321_, uint8_t v___x_2322_, lean_object* v___x_2323_, lean_object* v___f_2324_, lean_object* v___x_2325_, lean_object* v___f_2326_, lean_object* v___f_2327_, lean_object* v___x_2328_, lean_object* v___x_2329_, lean_object* v_a_2330_, lean_object* v_____r_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_){
_start:
{
lean_object* v___y_2338_; lean_object* v___y_2344_; lean_object* v___y_2345_; lean_object* v___y_2346_; lean_object* v___y_2347_; lean_object* v___y_2348_; lean_object* v___y_2369_; lean_object* v___y_2370_; lean_object* v___y_2371_; lean_object* v___y_2372_; lean_object* v___y_2373_; lean_object* v___y_2374_; lean_object* v___y_2423_; lean_object* v___y_2424_; lean_object* v___y_2425_; lean_object* v___y_2426_; uint8_t v___y_2427_; lean_object* v___y_2428_; lean_object* v___y_2429_; lean_object* v___y_2430_; lean_object* v___y_2431_; lean_object* v_a_2432_; lean_object* v___y_2445_; lean_object* v___y_2446_; lean_object* v___y_2447_; lean_object* v___y_2448_; uint8_t v___y_2449_; lean_object* v___y_2450_; lean_object* v___y_2451_; lean_object* v___y_2452_; lean_object* v___y_2453_; lean_object* v_a_2454_; lean_object* v___y_2464_; lean_object* v___y_2465_; lean_object* v___y_2466_; lean_object* v___y_2467_; lean_object* v___y_2468_; uint8_t v___y_2469_; lean_object* v___y_2470_; lean_object* v___y_2471_; uint8_t v___y_2472_; uint8_t v___y_2473_; lean_object* v___y_2474_; uint8_t v___y_2475_; lean_object* v___y_2476_; lean_object* v___y_2477_; lean_object* v_config_2517_; lean_object* v_solver_2518_; lean_object* v_lratPath_2519_; lean_object* v_timeout_2520_; uint8_t v_trimProofs_2521_; uint8_t v_binaryProofs_2522_; uint8_t v_graphviz_2523_; uint8_t v_solverMode_2524_; lean_object* v___y_2526_; lean_object* v___y_2527_; lean_object* v_options_2528_; lean_object* v_inheritedTraceOptions_2529_; lean_object* v___y_2530_; lean_object* v___y_2531_; lean_object* v___y_2532_; lean_object* v_a_2533_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2545_; lean_object* v_a_2546_; lean_object* v___y_2549_; lean_object* v___y_2550_; lean_object* v___y_2551_; lean_object* v___y_2552_; lean_object* v___y_2553_; lean_object* v___y_2554_; lean_object* v___y_2570_; lean_object* v___y_2571_; lean_object* v___y_2572_; lean_object* v___y_2573_; lean_object* v___y_2574_; lean_object* v___y_2575_; uint8_t v___y_2576_; lean_object* v___y_2577_; lean_object* v___y_2578_; lean_object* v_a_2579_; lean_object* v___y_2589_; lean_object* v___y_2590_; lean_object* v___y_2591_; lean_object* v___y_2592_; lean_object* v___y_2593_; lean_object* v___y_2594_; uint8_t v___y_2595_; lean_object* v___y_2596_; lean_object* v___y_2597_; lean_object* v_a_2598_; lean_object* v___y_2611_; lean_object* v___y_2612_; lean_object* v___y_2613_; lean_object* v___y_2614_; lean_object* v___y_2615_; lean_object* v___y_2616_; uint8_t v___y_2617_; lean_object* v___y_2618_; lean_object* v___y_2675_; lean_object* v___y_2676_; lean_object* v___y_2677_; lean_object* v_toCold_2678_; lean_object* v_ref_2679_; lean_object* v___y_2680_; 
v_config_2517_ = lean_ctor_get(v_ctx_2316_, 5);
v_solver_2518_ = lean_ctor_get(v_ctx_2316_, 3);
v_lratPath_2519_ = lean_ctor_get(v_ctx_2316_, 4);
v_timeout_2520_ = lean_ctor_get(v_config_2517_, 0);
v_trimProofs_2521_ = lean_ctor_get_uint8(v_config_2517_, sizeof(void*)*2);
v_binaryProofs_2522_ = lean_ctor_get_uint8(v_config_2517_, sizeof(void*)*2 + 1);
v_graphviz_2523_ = lean_ctor_get_uint8(v_config_2517_, sizeof(void*)*2 + 8);
v_solverMode_2524_ = lean_ctor_get_uint8(v_config_2517_, sizeof(void*)*2 + 10);
if (v_graphviz_2523_ == 0)
{
lean_object* v_toCold_2719_; lean_object* v_ref_2720_; 
lean_dec_ref(v_a_2330_);
v_toCold_2719_ = lean_ctor_get(v___y_2334_, 0);
v_ref_2720_ = lean_ctor_get(v___y_2334_, 2);
v___y_2675_ = v___y_2332_;
v___y_2676_ = v___y_2333_;
v___y_2677_ = v___y_2334_;
v_toCold_2678_ = v_toCold_2719_;
v_ref_2679_ = v_ref_2720_;
v___y_2680_ = v___y_2335_;
goto v___jp_2674_;
}
else
{
lean_object* v_toCold_2721_; lean_object* v_ref_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; 
v_toCold_2721_ = lean_ctor_get(v___y_2334_, 0);
v_ref_2722_ = lean_ctor_get(v___y_2334_, 2);
v___x_2723_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6);
v___x_2724_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v_a_2330_);
v___x_2725_ = l_IO_FS_writeFile(v___x_2723_, v___x_2724_);
lean_dec_ref(v___x_2724_);
if (lean_obj_tag(v___x_2725_) == 0)
{
lean_dec_ref_known(v___x_2725_, 1);
v___y_2675_ = v___y_2332_;
v___y_2676_ = v___y_2333_;
v___y_2677_ = v___y_2334_;
v_toCold_2678_ = v_toCold_2721_;
v_ref_2679_ = v_ref_2722_;
v___y_2680_ = v___y_2335_;
goto v___jp_2674_;
}
else
{
lean_object* v_a_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2737_; 
lean_dec_ref(v___x_2329_);
lean_dec_ref(v___x_2328_);
lean_dec_ref(v___f_2327_);
lean_dec_ref(v___f_2326_);
lean_dec_ref(v___f_2324_);
lean_dec_ref(v___x_2323_);
lean_dec_ref(v_reflectionResult_2321_);
lean_dec_ref(v_unusedHypotheses_2320_);
lean_dec(v_goal_2319_);
lean_dec_ref(v_aig_2317_);
lean_dec_ref(v_ctx_2316_);
v_a_2726_ = lean_ctor_get(v___x_2725_, 0);
v_isSharedCheck_2737_ = !lean_is_exclusive(v___x_2725_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2728_ = v___x_2725_;
v_isShared_2729_ = v_isSharedCheck_2737_;
goto v_resetjp_2727_;
}
else
{
lean_inc(v_a_2726_);
lean_dec(v___x_2725_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2737_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2735_; 
v___x_2730_ = lean_io_error_to_string(v_a_2726_);
v___x_2731_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2731_, 0, v___x_2730_);
v___x_2732_ = l_Lean_MessageData_ofFormat(v___x_2731_);
lean_inc(v_ref_2722_);
v___x_2733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2733_, 0, v_ref_2722_);
lean_ctor_set(v___x_2733_, 1, v___x_2732_);
if (v_isShared_2729_ == 0)
{
lean_ctor_set(v___x_2728_, 0, v___x_2733_);
v___x_2735_ = v___x_2728_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v___x_2733_);
v___x_2735_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
return v___x_2735_;
}
}
}
}
v___jp_2337_:
{
lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
v___x_2339_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v_aig_2317_, v___y_2338_, v_atomsAssignment_2318_);
lean_dec_ref(v___y_2338_);
v___x_2340_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2340_, 0, v_goal_2319_);
lean_ctor_set(v___x_2340_, 1, v_unusedHypotheses_2320_);
lean_ctor_set(v___x_2340_, 2, v___x_2339_);
v___x_2341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2341_, 0, v___x_2340_);
v___x_2342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2342_, 0, v___x_2341_);
return v___x_2342_;
}
v___jp_2343_:
{
lean_object* v___x_2349_; 
lean_inc_ref(v___y_2344_);
v___x_2349_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_2344_, v_ctx_2316_, v_reflectionResult_2321_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_);
if (lean_obj_tag(v___x_2349_) == 0)
{
lean_object* v_a_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2359_; 
v_a_2350_ = lean_ctor_get(v___x_2349_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2352_ = v___x_2349_;
v_isShared_2353_ = v_isSharedCheck_2359_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_a_2350_);
lean_dec(v___x_2349_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2359_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2357_; 
v___x_2354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2354_, 0, v_a_2350_);
lean_ctor_set(v___x_2354_, 1, v___y_2344_);
v___x_2355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2355_, 0, v___x_2354_);
if (v_isShared_2353_ == 0)
{
lean_ctor_set(v___x_2352_, 0, v___x_2355_);
v___x_2357_ = v___x_2352_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v___x_2355_);
v___x_2357_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
return v___x_2357_;
}
}
}
else
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2367_; 
lean_dec_ref(v___y_2344_);
v_a_2360_ = lean_ctor_get(v___x_2349_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2362_ = v___x_2349_;
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___x_2349_);
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
if (lean_obj_tag(v___y_2374_) == 0)
{
lean_object* v_a_2375_; 
v_a_2375_ = lean_ctor_get(v___y_2374_, 0);
lean_inc(v_a_2375_);
lean_dec_ref_known(v___y_2374_, 1);
if (lean_obj_tag(v_a_2375_) == 0)
{
lean_object* v_toCold_2376_; lean_object* v_options_2377_; uint8_t v_hasTrace_2378_; 
lean_dec_ref(v_reflectionResult_2321_);
lean_dec_ref(v_ctx_2316_);
v_toCold_2376_ = lean_ctor_get(v___y_2370_, 0);
v_options_2377_ = lean_ctor_get(v_toCold_2376_, 2);
v_hasTrace_2378_ = lean_ctor_get_uint8(v_options_2377_, sizeof(void*)*1);
if (v_hasTrace_2378_ == 0)
{
lean_object* v_a_2379_; 
lean_dec(v___y_2373_);
v_a_2379_ = lean_ctor_get(v_a_2375_, 0);
lean_inc(v_a_2379_);
lean_dec_ref_known(v_a_2375_, 1);
v___y_2338_ = v_a_2379_;
goto v___jp_2337_;
}
else
{
lean_object* v_a_2380_; lean_object* v_inheritedTraceOptions_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; uint8_t v___x_2384_; 
v_a_2380_ = lean_ctor_get(v_a_2375_, 0);
lean_inc(v_a_2380_);
lean_dec_ref_known(v_a_2375_, 1);
v_inheritedTraceOptions_2381_ = lean_ctor_get(v_toCold_2376_, 11);
v___x_2382_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___y_2373_);
v___x_2383_ = l_Lean_Name_append(v___x_2382_, v___y_2373_);
v___x_2384_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2381_, v_options_2377_, v___x_2383_);
lean_dec(v___x_2383_);
if (v___x_2384_ == 0)
{
lean_dec(v___y_2373_);
v___y_2338_ = v_a_2380_;
goto v___jp_2337_;
}
else
{
lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2385_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1);
v___x_2386_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v___y_2373_, v___x_2385_, v___y_2369_, v___y_2371_, v___y_2370_, v___y_2372_);
if (lean_obj_tag(v___x_2386_) == 0)
{
lean_dec_ref_known(v___x_2386_, 1);
v___y_2338_ = v_a_2380_;
goto v___jp_2337_;
}
else
{
lean_object* v_a_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2394_; 
lean_dec(v_a_2380_);
lean_dec_ref(v_unusedHypotheses_2320_);
lean_dec(v_goal_2319_);
lean_dec_ref(v_aig_2317_);
v_a_2387_ = lean_ctor_get(v___x_2386_, 0);
v_isSharedCheck_2394_ = !lean_is_exclusive(v___x_2386_);
if (v_isSharedCheck_2394_ == 0)
{
v___x_2389_ = v___x_2386_;
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_a_2387_);
lean_dec(v___x_2386_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v___x_2392_; 
if (v_isShared_2390_ == 0)
{
v___x_2392_ = v___x_2389_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_a_2387_);
v___x_2392_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
return v___x_2392_;
}
}
}
}
}
}
else
{
lean_object* v_toCold_2395_; lean_object* v_options_2396_; uint8_t v_hasTrace_2397_; 
lean_dec_ref(v_unusedHypotheses_2320_);
lean_dec(v_goal_2319_);
lean_dec_ref(v_aig_2317_);
v_toCold_2395_ = lean_ctor_get(v___y_2370_, 0);
v_options_2396_ = lean_ctor_get(v_toCold_2395_, 2);
v_hasTrace_2397_ = lean_ctor_get_uint8(v_options_2396_, sizeof(void*)*1);
if (v_hasTrace_2397_ == 0)
{
lean_object* v_a_2398_; 
lean_dec(v___y_2373_);
v_a_2398_ = lean_ctor_get(v_a_2375_, 0);
lean_inc(v_a_2398_);
lean_dec_ref_known(v_a_2375_, 1);
v___y_2344_ = v_a_2398_;
v___y_2345_ = v___y_2369_;
v___y_2346_ = v___y_2371_;
v___y_2347_ = v___y_2370_;
v___y_2348_ = v___y_2372_;
goto v___jp_2343_;
}
else
{
lean_object* v_a_2399_; lean_object* v_inheritedTraceOptions_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; uint8_t v___x_2403_; 
v_a_2399_ = lean_ctor_get(v_a_2375_, 0);
lean_inc(v_a_2399_);
lean_dec_ref_known(v_a_2375_, 1);
v_inheritedTraceOptions_2400_ = lean_ctor_get(v_toCold_2395_, 11);
v___x_2401_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___y_2373_);
v___x_2402_ = l_Lean_Name_append(v___x_2401_, v___y_2373_);
v___x_2403_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2400_, v_options_2396_, v___x_2402_);
lean_dec(v___x_2402_);
if (v___x_2403_ == 0)
{
lean_dec(v___y_2373_);
v___y_2344_ = v_a_2399_;
v___y_2345_ = v___y_2369_;
v___y_2346_ = v___y_2371_;
v___y_2347_ = v___y_2370_;
v___y_2348_ = v___y_2372_;
goto v___jp_2343_;
}
else
{
lean_object* v___x_2404_; lean_object* v___x_2405_; 
v___x_2404_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3);
v___x_2405_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v___y_2373_, v___x_2404_, v___y_2369_, v___y_2371_, v___y_2370_, v___y_2372_);
if (lean_obj_tag(v___x_2405_) == 0)
{
lean_dec_ref_known(v___x_2405_, 1);
v___y_2344_ = v_a_2399_;
v___y_2345_ = v___y_2369_;
v___y_2346_ = v___y_2371_;
v___y_2347_ = v___y_2370_;
v___y_2348_ = v___y_2372_;
goto v___jp_2343_;
}
else
{
lean_object* v_a_2406_; lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2413_; 
lean_dec(v_a_2399_);
lean_dec_ref(v_reflectionResult_2321_);
lean_dec_ref(v_ctx_2316_);
v_a_2406_ = lean_ctor_get(v___x_2405_, 0);
v_isSharedCheck_2413_ = !lean_is_exclusive(v___x_2405_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2408_ = v___x_2405_;
v_isShared_2409_ = v_isSharedCheck_2413_;
goto v_resetjp_2407_;
}
else
{
lean_inc(v_a_2406_);
lean_dec(v___x_2405_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2413_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
lean_object* v___x_2411_; 
if (v_isShared_2409_ == 0)
{
v___x_2411_ = v___x_2408_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v_a_2406_);
v___x_2411_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
return v___x_2411_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2421_; 
lean_dec(v___y_2373_);
lean_dec_ref(v_reflectionResult_2321_);
lean_dec_ref(v_unusedHypotheses_2320_);
lean_dec(v_goal_2319_);
lean_dec_ref(v_aig_2317_);
lean_dec_ref(v_ctx_2316_);
v_a_2414_ = lean_ctor_get(v___y_2374_, 0);
v_isSharedCheck_2421_ = !lean_is_exclusive(v___y_2374_);
if (v_isSharedCheck_2421_ == 0)
{
v___x_2416_ = v___y_2374_;
v_isShared_2417_ = v_isSharedCheck_2421_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_a_2414_);
lean_dec(v___y_2374_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2421_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v___x_2419_; 
if (v_isShared_2417_ == 0)
{
v___x_2419_ = v___x_2416_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v_a_2414_);
v___x_2419_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
return v___x_2419_;
}
}
}
}
v___jp_2422_:
{
lean_object* v___x_2433_; double v___x_2434_; double v___x_2435_; double v___x_2436_; double v___x_2437_; double v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; 
v___x_2433_ = lean_io_mono_nanos_now();
v___x_2434_ = lean_float_of_nat(v___y_2430_);
v___x_2435_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_2436_ = lean_float_div(v___x_2434_, v___x_2435_);
v___x_2437_ = lean_float_of_nat(v___x_2433_);
v___x_2438_ = lean_float_div(v___x_2437_, v___x_2435_);
v___x_2439_ = lean_box_float(v___x_2436_);
v___x_2440_ = lean_box_float(v___x_2438_);
v___x_2441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2441_, 0, v___x_2439_);
lean_ctor_set(v___x_2441_, 1, v___x_2440_);
v___x_2442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2442_, 0, v_a_2432_);
lean_ctor_set(v___x_2442_, 1, v___x_2441_);
lean_inc(v___y_2429_);
v___x_2443_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_2429_, v___x_2322_, v___x_2323_, v___y_2431_, v___y_2427_, v___y_2423_, v___f_2324_, v___x_2442_, v___y_2425_, v___y_2426_, v___y_2424_, v___y_2428_);
v___y_2369_ = v___y_2425_;
v___y_2370_ = v___y_2424_;
v___y_2371_ = v___y_2426_;
v___y_2372_ = v___y_2428_;
v___y_2373_ = v___y_2429_;
v___y_2374_ = v___x_2443_;
goto v___jp_2368_;
}
v___jp_2444_:
{
lean_object* v___x_2455_; double v___x_2456_; double v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; 
v___x_2455_ = lean_io_get_num_heartbeats();
v___x_2456_ = lean_float_of_nat(v___y_2453_);
v___x_2457_ = lean_float_of_nat(v___x_2455_);
v___x_2458_ = lean_box_float(v___x_2456_);
v___x_2459_ = lean_box_float(v___x_2457_);
v___x_2460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2460_, 0, v___x_2458_);
lean_ctor_set(v___x_2460_, 1, v___x_2459_);
v___x_2461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2461_, 0, v_a_2454_);
lean_ctor_set(v___x_2461_, 1, v___x_2460_);
lean_inc(v___y_2451_);
v___x_2462_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_2451_, v___x_2322_, v___x_2323_, v___y_2452_, v___y_2449_, v___y_2445_, v___f_2324_, v___x_2461_, v___y_2447_, v___y_2448_, v___y_2446_, v___y_2450_);
v___y_2369_ = v___y_2447_;
v___y_2370_ = v___y_2446_;
v___y_2371_ = v___y_2448_;
v___y_2372_ = v___y_2450_;
v___y_2373_ = v___y_2451_;
v___y_2374_ = v___x_2462_;
goto v___jp_2368_;
}
v___jp_2463_:
{
lean_object* v___x_2478_; lean_object* v_a_2479_; uint8_t v___x_2480_; 
v___x_2478_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_2467_);
v_a_2479_ = lean_ctor_get(v___x_2478_, 0);
lean_inc(v_a_2479_);
lean_dec_ref(v___x_2478_);
v___x_2480_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_2476_, v___x_2325_);
if (v___x_2480_ == 0)
{
lean_object* v___x_2481_; lean_object* v___x_2482_; 
v___x_2481_ = lean_io_mono_nanos_now();
v___x_2482_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_2465_, v___y_2468_, v___y_2477_, v___y_2469_, v___y_2466_, v___y_2472_, v___y_2475_, v___y_2470_, v___y_2467_);
if (lean_obj_tag(v___x_2482_) == 0)
{
lean_object* v_a_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2490_; 
v_a_2483_ = lean_ctor_get(v___x_2482_, 0);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2485_ = v___x_2482_;
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_a_2483_);
lean_dec(v___x_2482_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2488_; 
if (v_isShared_2486_ == 0)
{
lean_ctor_set_tag(v___x_2485_, 1);
v___x_2488_ = v___x_2485_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_a_2483_);
v___x_2488_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
v___y_2423_ = v_a_2479_;
v___y_2424_ = v___y_2470_;
v___y_2425_ = v___y_2464_;
v___y_2426_ = v___y_2471_;
v___y_2427_ = v___y_2473_;
v___y_2428_ = v___y_2467_;
v___y_2429_ = v___y_2474_;
v___y_2430_ = v___x_2481_;
v___y_2431_ = v___y_2476_;
v_a_2432_ = v___x_2488_;
goto v___jp_2422_;
}
}
}
else
{
lean_object* v_a_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2498_; 
v_a_2491_ = lean_ctor_get(v___x_2482_, 0);
v_isSharedCheck_2498_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2498_ == 0)
{
v___x_2493_ = v___x_2482_;
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_a_2491_);
lean_dec(v___x_2482_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v___x_2496_; 
if (v_isShared_2494_ == 0)
{
lean_ctor_set_tag(v___x_2493_, 0);
v___x_2496_ = v___x_2493_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v_a_2491_);
v___x_2496_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
v___y_2423_ = v_a_2479_;
v___y_2424_ = v___y_2470_;
v___y_2425_ = v___y_2464_;
v___y_2426_ = v___y_2471_;
v___y_2427_ = v___y_2473_;
v___y_2428_ = v___y_2467_;
v___y_2429_ = v___y_2474_;
v___y_2430_ = v___x_2481_;
v___y_2431_ = v___y_2476_;
v_a_2432_ = v___x_2496_;
goto v___jp_2422_;
}
}
}
}
else
{
lean_object* v___x_2499_; lean_object* v___x_2500_; 
v___x_2499_ = lean_io_get_num_heartbeats();
v___x_2500_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_2465_, v___y_2468_, v___y_2477_, v___y_2469_, v___y_2466_, v___y_2472_, v___y_2475_, v___y_2470_, v___y_2467_);
if (lean_obj_tag(v___x_2500_) == 0)
{
lean_object* v_a_2501_; lean_object* v___x_2503_; uint8_t v_isShared_2504_; uint8_t v_isSharedCheck_2508_; 
v_a_2501_ = lean_ctor_get(v___x_2500_, 0);
v_isSharedCheck_2508_ = !lean_is_exclusive(v___x_2500_);
if (v_isSharedCheck_2508_ == 0)
{
v___x_2503_ = v___x_2500_;
v_isShared_2504_ = v_isSharedCheck_2508_;
goto v_resetjp_2502_;
}
else
{
lean_inc(v_a_2501_);
lean_dec(v___x_2500_);
v___x_2503_ = lean_box(0);
v_isShared_2504_ = v_isSharedCheck_2508_;
goto v_resetjp_2502_;
}
v_resetjp_2502_:
{
lean_object* v___x_2506_; 
if (v_isShared_2504_ == 0)
{
lean_ctor_set_tag(v___x_2503_, 1);
v___x_2506_ = v___x_2503_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2507_, 0, v_a_2501_);
v___x_2506_ = v_reuseFailAlloc_2507_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
v___y_2445_ = v_a_2479_;
v___y_2446_ = v___y_2470_;
v___y_2447_ = v___y_2464_;
v___y_2448_ = v___y_2471_;
v___y_2449_ = v___y_2473_;
v___y_2450_ = v___y_2467_;
v___y_2451_ = v___y_2474_;
v___y_2452_ = v___y_2476_;
v___y_2453_ = v___x_2499_;
v_a_2454_ = v___x_2506_;
goto v___jp_2444_;
}
}
}
else
{
lean_object* v_a_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2516_; 
v_a_2509_ = lean_ctor_get(v___x_2500_, 0);
v_isSharedCheck_2516_ = !lean_is_exclusive(v___x_2500_);
if (v_isSharedCheck_2516_ == 0)
{
v___x_2511_ = v___x_2500_;
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_a_2509_);
lean_dec(v___x_2500_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v___x_2514_; 
if (v_isShared_2512_ == 0)
{
lean_ctor_set_tag(v___x_2511_, 0);
v___x_2514_ = v___x_2511_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v_a_2509_);
v___x_2514_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
v___y_2445_ = v_a_2479_;
v___y_2446_ = v___y_2470_;
v___y_2447_ = v___y_2464_;
v___y_2448_ = v___y_2471_;
v___y_2449_ = v___y_2473_;
v___y_2450_ = v___y_2467_;
v___y_2451_ = v___y_2474_;
v___y_2452_ = v___y_2476_;
v___y_2453_ = v___x_2499_;
v_a_2454_ = v___x_2514_;
goto v___jp_2444_;
}
}
}
}
}
v___jp_2525_:
{
lean_object* v___x_2534_; lean_object* v___x_2535_; uint8_t v___x_2536_; 
v___x_2534_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___y_2531_);
v___x_2535_ = l_Lean_Name_append(v___x_2534_, v___y_2531_);
v___x_2536_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2529_, v_options_2528_, v___x_2535_);
lean_dec(v___x_2535_);
if (v___x_2536_ == 0)
{
lean_object* v___x_2537_; uint8_t v___x_2538_; 
v___x_2537_ = l_Lean_trace_profiler;
v___x_2538_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_2528_, v___x_2537_);
if (v___x_2538_ == 0)
{
lean_object* v___x_2539_; 
lean_dec_ref(v___f_2324_);
lean_dec_ref(v___x_2323_);
lean_inc(v_timeout_2520_);
lean_inc_ref(v_lratPath_2519_);
lean_inc_ref(v_solver_2518_);
v___x_2539_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_a_2533_, v_solver_2518_, v_lratPath_2519_, v_trimProofs_2521_, v_timeout_2520_, v_binaryProofs_2522_, v_solverMode_2524_, v___y_2527_, v___y_2532_);
v___y_2369_ = v___y_2526_;
v___y_2370_ = v___y_2527_;
v___y_2371_ = v___y_2530_;
v___y_2372_ = v___y_2532_;
v___y_2373_ = v___y_2531_;
v___y_2374_ = v___x_2539_;
goto v___jp_2368_;
}
else
{
lean_inc_ref(v_lratPath_2519_);
lean_inc_ref(v_solver_2518_);
lean_inc(v_timeout_2520_);
v___y_2464_ = v___y_2526_;
v___y_2465_ = v_a_2533_;
v___y_2466_ = v_timeout_2520_;
v___y_2467_ = v___y_2532_;
v___y_2468_ = v_solver_2518_;
v___y_2469_ = v_trimProofs_2521_;
v___y_2470_ = v___y_2527_;
v___y_2471_ = v___y_2530_;
v___y_2472_ = v_binaryProofs_2522_;
v___y_2473_ = v___x_2536_;
v___y_2474_ = v___y_2531_;
v___y_2475_ = v_solverMode_2524_;
v___y_2476_ = v_options_2528_;
v___y_2477_ = v_lratPath_2519_;
goto v___jp_2463_;
}
}
else
{
lean_inc_ref(v_lratPath_2519_);
lean_inc_ref(v_solver_2518_);
lean_inc(v_timeout_2520_);
v___y_2464_ = v___y_2526_;
v___y_2465_ = v_a_2533_;
v___y_2466_ = v_timeout_2520_;
v___y_2467_ = v___y_2532_;
v___y_2468_ = v_solver_2518_;
v___y_2469_ = v_trimProofs_2521_;
v___y_2470_ = v___y_2527_;
v___y_2471_ = v___y_2530_;
v___y_2472_ = v_binaryProofs_2522_;
v___y_2473_ = v___x_2536_;
v___y_2474_ = v___y_2531_;
v___y_2475_ = v_solverMode_2524_;
v___y_2476_ = v_options_2528_;
v___y_2477_ = v_lratPath_2519_;
goto v___jp_2463_;
}
}
v___jp_2540_:
{
lean_object* v___x_2547_; 
lean_inc(v_timeout_2520_);
lean_inc_ref(v_lratPath_2519_);
lean_inc_ref(v_solver_2518_);
v___x_2547_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_a_2546_, v_solver_2518_, v_lratPath_2519_, v_trimProofs_2521_, v_timeout_2520_, v_binaryProofs_2522_, v_solverMode_2524_, v___y_2542_, v___y_2545_);
v___y_2369_ = v___y_2541_;
v___y_2370_ = v___y_2542_;
v___y_2371_ = v___y_2543_;
v___y_2372_ = v___y_2545_;
v___y_2373_ = v___y_2544_;
v___y_2374_ = v___x_2547_;
goto v___jp_2368_;
}
v___jp_2548_:
{
if (lean_obj_tag(v___y_2554_) == 0)
{
lean_object* v_toCold_2555_; lean_object* v_options_2556_; uint8_t v_hasTrace_2557_; 
v_toCold_2555_ = lean_ctor_get(v___y_2549_, 0);
v_options_2556_ = lean_ctor_get(v_toCold_2555_, 2);
v_hasTrace_2557_ = lean_ctor_get_uint8(v_options_2556_, sizeof(void*)*1);
if (v_hasTrace_2557_ == 0)
{
lean_object* v_a_2558_; 
lean_dec_ref(v___f_2324_);
lean_dec_ref(v___x_2323_);
v_a_2558_ = lean_ctor_get(v___y_2554_, 0);
lean_inc(v_a_2558_);
lean_dec_ref_known(v___y_2554_, 1);
v___y_2541_ = v___y_2550_;
v___y_2542_ = v___y_2549_;
v___y_2543_ = v___y_2551_;
v___y_2544_ = v___y_2553_;
v___y_2545_ = v___y_2552_;
v_a_2546_ = v_a_2558_;
goto v___jp_2540_;
}
else
{
lean_object* v_a_2559_; lean_object* v_inheritedTraceOptions_2560_; 
v_a_2559_ = lean_ctor_get(v___y_2554_, 0);
lean_inc(v_a_2559_);
lean_dec_ref_known(v___y_2554_, 1);
v_inheritedTraceOptions_2560_ = lean_ctor_get(v_toCold_2555_, 11);
v___y_2526_ = v___y_2550_;
v___y_2527_ = v___y_2549_;
v_options_2528_ = v_options_2556_;
v_inheritedTraceOptions_2529_ = v_inheritedTraceOptions_2560_;
v___y_2530_ = v___y_2551_;
v___y_2531_ = v___y_2553_;
v___y_2532_ = v___y_2552_;
v_a_2533_ = v_a_2559_;
goto v___jp_2525_;
}
}
else
{
lean_object* v_a_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2568_; 
lean_dec(v___y_2553_);
lean_dec_ref(v___f_2324_);
lean_dec_ref(v___x_2323_);
lean_dec_ref(v_reflectionResult_2321_);
lean_dec_ref(v_unusedHypotheses_2320_);
lean_dec(v_goal_2319_);
lean_dec_ref(v_aig_2317_);
lean_dec_ref(v_ctx_2316_);
v_a_2561_ = lean_ctor_get(v___y_2554_, 0);
v_isSharedCheck_2568_ = !lean_is_exclusive(v___y_2554_);
if (v_isSharedCheck_2568_ == 0)
{
v___x_2563_ = v___y_2554_;
v_isShared_2564_ = v_isSharedCheck_2568_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_a_2561_);
lean_dec(v___y_2554_);
v___x_2563_ = lean_box(0);
v_isShared_2564_ = v_isSharedCheck_2568_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
lean_object* v___x_2566_; 
if (v_isShared_2564_ == 0)
{
v___x_2566_ = v___x_2563_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_a_2561_);
v___x_2566_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
return v___x_2566_;
}
}
}
}
v___jp_2569_:
{
lean_object* v___x_2580_; double v___x_2581_; double v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; 
v___x_2580_ = lean_io_get_num_heartbeats();
v___x_2581_ = lean_float_of_nat(v___y_2575_);
v___x_2582_ = lean_float_of_nat(v___x_2580_);
v___x_2583_ = lean_box_float(v___x_2581_);
v___x_2584_ = lean_box_float(v___x_2582_);
v___x_2585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2585_, 0, v___x_2583_);
lean_ctor_set(v___x_2585_, 1, v___x_2584_);
v___x_2586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2586_, 0, v_a_2579_);
lean_ctor_set(v___x_2586_, 1, v___x_2585_);
lean_inc_ref(v___x_2323_);
lean_inc(v___y_2574_);
v___x_2587_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_2574_, v___x_2322_, v___x_2323_, v___y_2578_, v___y_2576_, v___y_2577_, v___f_2326_, v___x_2586_, v___y_2571_, v___y_2572_, v___y_2570_, v___y_2573_);
v___y_2549_ = v___y_2570_;
v___y_2550_ = v___y_2571_;
v___y_2551_ = v___y_2572_;
v___y_2552_ = v___y_2573_;
v___y_2553_ = v___y_2574_;
v___y_2554_ = v___x_2587_;
goto v___jp_2548_;
}
v___jp_2588_:
{
lean_object* v___x_2599_; double v___x_2600_; double v___x_2601_; double v___x_2602_; double v___x_2603_; double v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; 
v___x_2599_ = lean_io_mono_nanos_now();
v___x_2600_ = lean_float_of_nat(v___y_2589_);
v___x_2601_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_2602_ = lean_float_div(v___x_2600_, v___x_2601_);
v___x_2603_ = lean_float_of_nat(v___x_2599_);
v___x_2604_ = lean_float_div(v___x_2603_, v___x_2601_);
v___x_2605_ = lean_box_float(v___x_2602_);
v___x_2606_ = lean_box_float(v___x_2604_);
v___x_2607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2607_, 0, v___x_2605_);
lean_ctor_set(v___x_2607_, 1, v___x_2606_);
v___x_2608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2608_, 0, v_a_2598_);
lean_ctor_set(v___x_2608_, 1, v___x_2607_);
lean_inc_ref(v___x_2323_);
lean_inc(v___y_2594_);
v___x_2609_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_2594_, v___x_2322_, v___x_2323_, v___y_2597_, v___y_2595_, v___y_2596_, v___f_2326_, v___x_2608_, v___y_2591_, v___y_2592_, v___y_2590_, v___y_2593_);
v___y_2549_ = v___y_2590_;
v___y_2550_ = v___y_2591_;
v___y_2551_ = v___y_2592_;
v___y_2552_ = v___y_2593_;
v___y_2553_ = v___y_2594_;
v___y_2554_ = v___x_2609_;
goto v___jp_2548_;
}
v___jp_2610_:
{
lean_object* v___x_2619_; lean_object* v_a_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2673_; 
v___x_2619_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_2616_);
v_a_2620_ = lean_ctor_get(v___x_2619_, 0);
v_isSharedCheck_2673_ = !lean_is_exclusive(v___x_2619_);
if (v_isSharedCheck_2673_ == 0)
{
v___x_2622_ = v___x_2619_;
v_isShared_2623_ = v_isSharedCheck_2673_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_a_2620_);
lean_dec(v___x_2619_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2673_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
uint8_t v___x_2624_; 
v___x_2624_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_2618_, v___x_2325_);
if (v___x_2624_ == 0)
{
lean_object* v___x_2625_; lean_object* v___x_2626_; 
v___x_2625_ = lean_io_mono_nanos_now();
v___x_2626_ = l_IO_lazyPure___redArg(v___f_2327_);
if (lean_obj_tag(v___x_2626_) == 0)
{
lean_object* v_a_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2634_; 
lean_del_object(v___x_2622_);
v_a_2627_ = lean_ctor_get(v___x_2626_, 0);
v_isSharedCheck_2634_ = !lean_is_exclusive(v___x_2626_);
if (v_isSharedCheck_2634_ == 0)
{
v___x_2629_ = v___x_2626_;
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_a_2627_);
lean_dec(v___x_2626_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v___x_2632_; 
if (v_isShared_2630_ == 0)
{
lean_ctor_set_tag(v___x_2629_, 1);
v___x_2632_ = v___x_2629_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_a_2627_);
v___x_2632_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
v___y_2589_ = v___x_2625_;
v___y_2590_ = v___y_2612_;
v___y_2591_ = v___y_2611_;
v___y_2592_ = v___y_2613_;
v___y_2593_ = v___y_2616_;
v___y_2594_ = v___y_2615_;
v___y_2595_ = v___y_2617_;
v___y_2596_ = v_a_2620_;
v___y_2597_ = v___y_2618_;
v_a_2598_ = v___x_2632_;
goto v___jp_2588_;
}
}
}
else
{
lean_object* v_a_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2648_; 
v_a_2635_ = lean_ctor_get(v___x_2626_, 0);
v_isSharedCheck_2648_ = !lean_is_exclusive(v___x_2626_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2637_ = v___x_2626_;
v_isShared_2638_ = v_isSharedCheck_2648_;
goto v_resetjp_2636_;
}
else
{
lean_inc(v_a_2635_);
lean_dec(v___x_2626_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2648_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v___x_2639_; lean_object* v___x_2641_; 
v___x_2639_ = lean_io_error_to_string(v_a_2635_);
if (v_isShared_2638_ == 0)
{
lean_ctor_set_tag(v___x_2637_, 3);
lean_ctor_set(v___x_2637_, 0, v___x_2639_);
v___x_2641_ = v___x_2637_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v___x_2639_);
v___x_2641_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2645_; 
v___x_2642_ = l_Lean_MessageData_ofFormat(v___x_2641_);
lean_inc(v___y_2614_);
v___x_2643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2643_, 0, v___y_2614_);
lean_ctor_set(v___x_2643_, 1, v___x_2642_);
if (v_isShared_2623_ == 0)
{
lean_ctor_set(v___x_2622_, 0, v___x_2643_);
v___x_2645_ = v___x_2622_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v___x_2643_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
v___y_2589_ = v___x_2625_;
v___y_2590_ = v___y_2612_;
v___y_2591_ = v___y_2611_;
v___y_2592_ = v___y_2613_;
v___y_2593_ = v___y_2616_;
v___y_2594_ = v___y_2615_;
v___y_2595_ = v___y_2617_;
v___y_2596_ = v_a_2620_;
v___y_2597_ = v___y_2618_;
v_a_2598_ = v___x_2645_;
goto v___jp_2588_;
}
}
}
}
}
else
{
lean_object* v___x_2649_; lean_object* v___x_2650_; 
v___x_2649_ = lean_io_get_num_heartbeats();
v___x_2650_ = l_IO_lazyPure___redArg(v___f_2327_);
if (lean_obj_tag(v___x_2650_) == 0)
{
lean_object* v_a_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2658_; 
lean_del_object(v___x_2622_);
v_a_2651_ = lean_ctor_get(v___x_2650_, 0);
v_isSharedCheck_2658_ = !lean_is_exclusive(v___x_2650_);
if (v_isSharedCheck_2658_ == 0)
{
v___x_2653_ = v___x_2650_;
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_a_2651_);
lean_dec(v___x_2650_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
lean_object* v___x_2656_; 
if (v_isShared_2654_ == 0)
{
lean_ctor_set_tag(v___x_2653_, 1);
v___x_2656_ = v___x_2653_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v_a_2651_);
v___x_2656_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
v___y_2570_ = v___y_2612_;
v___y_2571_ = v___y_2611_;
v___y_2572_ = v___y_2613_;
v___y_2573_ = v___y_2616_;
v___y_2574_ = v___y_2615_;
v___y_2575_ = v___x_2649_;
v___y_2576_ = v___y_2617_;
v___y_2577_ = v_a_2620_;
v___y_2578_ = v___y_2618_;
v_a_2579_ = v___x_2656_;
goto v___jp_2569_;
}
}
}
else
{
lean_object* v_a_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2672_; 
v_a_2659_ = lean_ctor_get(v___x_2650_, 0);
v_isSharedCheck_2672_ = !lean_is_exclusive(v___x_2650_);
if (v_isSharedCheck_2672_ == 0)
{
v___x_2661_ = v___x_2650_;
v_isShared_2662_ = v_isSharedCheck_2672_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_a_2659_);
lean_dec(v___x_2650_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2672_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v___x_2663_; lean_object* v___x_2665_; 
v___x_2663_ = lean_io_error_to_string(v_a_2659_);
if (v_isShared_2662_ == 0)
{
lean_ctor_set_tag(v___x_2661_, 3);
lean_ctor_set(v___x_2661_, 0, v___x_2663_);
v___x_2665_ = v___x_2661_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v___x_2663_);
v___x_2665_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2669_; 
v___x_2666_ = l_Lean_MessageData_ofFormat(v___x_2665_);
lean_inc(v___y_2614_);
v___x_2667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2667_, 0, v___y_2614_);
lean_ctor_set(v___x_2667_, 1, v___x_2666_);
if (v_isShared_2623_ == 0)
{
lean_ctor_set(v___x_2622_, 0, v___x_2667_);
v___x_2669_ = v___x_2622_;
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
v___y_2570_ = v___y_2612_;
v___y_2571_ = v___y_2611_;
v___y_2572_ = v___y_2613_;
v___y_2573_ = v___y_2616_;
v___y_2574_ = v___y_2615_;
v___y_2575_ = v___x_2649_;
v___y_2576_ = v___y_2617_;
v___y_2577_ = v_a_2620_;
v___y_2578_ = v___y_2618_;
v_a_2579_ = v___x_2669_;
goto v___jp_2569_;
}
}
}
}
}
}
}
v___jp_2674_:
{
lean_object* v_options_2681_; lean_object* v_inheritedTraceOptions_2682_; uint8_t v_hasTrace_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; 
v_options_2681_ = lean_ctor_get(v_toCold_2678_, 2);
v_inheritedTraceOptions_2682_ = lean_ctor_get(v_toCold_2678_, 11);
v_hasTrace_2683_ = lean_ctor_get_uint8(v_options_2681_, sizeof(void*)*1);
v___x_2684_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__2));
v___x_2685_ = l_Lean_Name_mkStr3(v___x_2328_, v___x_2329_, v___x_2684_);
if (v_hasTrace_2683_ == 0)
{
lean_object* v___x_2686_; 
lean_dec_ref(v___f_2326_);
lean_dec_ref(v___f_2324_);
lean_dec_ref(v___x_2323_);
v___x_2686_ = l_IO_lazyPure___redArg(v___f_2327_);
if (lean_obj_tag(v___x_2686_) == 0)
{
lean_object* v_a_2687_; 
v_a_2687_ = lean_ctor_get(v___x_2686_, 0);
lean_inc(v_a_2687_);
lean_dec_ref_known(v___x_2686_, 1);
v___y_2541_ = v___y_2675_;
v___y_2542_ = v___y_2677_;
v___y_2543_ = v___y_2676_;
v___y_2544_ = v___x_2685_;
v___y_2545_ = v___y_2680_;
v_a_2546_ = v_a_2687_;
goto v___jp_2540_;
}
else
{
lean_object* v_a_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2699_; 
lean_dec(v___x_2685_);
lean_dec_ref(v_reflectionResult_2321_);
lean_dec_ref(v_unusedHypotheses_2320_);
lean_dec(v_goal_2319_);
lean_dec_ref(v_aig_2317_);
lean_dec_ref(v_ctx_2316_);
v_a_2688_ = lean_ctor_get(v___x_2686_, 0);
v_isSharedCheck_2699_ = !lean_is_exclusive(v___x_2686_);
if (v_isSharedCheck_2699_ == 0)
{
v___x_2690_ = v___x_2686_;
v_isShared_2691_ = v_isSharedCheck_2699_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_a_2688_);
lean_dec(v___x_2686_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2699_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2697_; 
v___x_2692_ = lean_io_error_to_string(v_a_2688_);
v___x_2693_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2693_, 0, v___x_2692_);
v___x_2694_ = l_Lean_MessageData_ofFormat(v___x_2693_);
lean_inc(v_ref_2679_);
v___x_2695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2695_, 0, v_ref_2679_);
lean_ctor_set(v___x_2695_, 1, v___x_2694_);
if (v_isShared_2691_ == 0)
{
lean_ctor_set(v___x_2690_, 0, v___x_2695_);
v___x_2697_ = v___x_2690_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v___x_2695_);
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
else
{
lean_object* v___x_2700_; lean_object* v___x_2701_; uint8_t v___x_2702_; 
v___x_2700_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___x_2685_);
v___x_2701_ = l_Lean_Name_append(v___x_2700_, v___x_2685_);
v___x_2702_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2682_, v_options_2681_, v___x_2701_);
lean_dec(v___x_2701_);
if (v___x_2702_ == 0)
{
lean_object* v___x_2703_; uint8_t v___x_2704_; 
v___x_2703_ = l_Lean_trace_profiler;
v___x_2704_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_2681_, v___x_2703_);
if (v___x_2704_ == 0)
{
lean_object* v___x_2705_; 
lean_dec_ref(v___f_2326_);
v___x_2705_ = l_IO_lazyPure___redArg(v___f_2327_);
if (lean_obj_tag(v___x_2705_) == 0)
{
lean_object* v_a_2706_; 
v_a_2706_ = lean_ctor_get(v___x_2705_, 0);
lean_inc(v_a_2706_);
lean_dec_ref_known(v___x_2705_, 1);
v___y_2526_ = v___y_2675_;
v___y_2527_ = v___y_2677_;
v_options_2528_ = v_options_2681_;
v_inheritedTraceOptions_2529_ = v_inheritedTraceOptions_2682_;
v___y_2530_ = v___y_2676_;
v___y_2531_ = v___x_2685_;
v___y_2532_ = v___y_2680_;
v_a_2533_ = v_a_2706_;
goto v___jp_2525_;
}
else
{
lean_object* v_a_2707_; lean_object* v___x_2709_; uint8_t v_isShared_2710_; uint8_t v_isSharedCheck_2718_; 
lean_dec(v___x_2685_);
lean_dec_ref(v___f_2324_);
lean_dec_ref(v___x_2323_);
lean_dec_ref(v_reflectionResult_2321_);
lean_dec_ref(v_unusedHypotheses_2320_);
lean_dec(v_goal_2319_);
lean_dec_ref(v_aig_2317_);
lean_dec_ref(v_ctx_2316_);
v_a_2707_ = lean_ctor_get(v___x_2705_, 0);
v_isSharedCheck_2718_ = !lean_is_exclusive(v___x_2705_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2709_ = v___x_2705_;
v_isShared_2710_ = v_isSharedCheck_2718_;
goto v_resetjp_2708_;
}
else
{
lean_inc(v_a_2707_);
lean_dec(v___x_2705_);
v___x_2709_ = lean_box(0);
v_isShared_2710_ = v_isSharedCheck_2718_;
goto v_resetjp_2708_;
}
v_resetjp_2708_:
{
lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2716_; 
v___x_2711_ = lean_io_error_to_string(v_a_2707_);
v___x_2712_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2712_, 0, v___x_2711_);
v___x_2713_ = l_Lean_MessageData_ofFormat(v___x_2712_);
lean_inc(v_ref_2679_);
v___x_2714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2714_, 0, v_ref_2679_);
lean_ctor_set(v___x_2714_, 1, v___x_2713_);
if (v_isShared_2710_ == 0)
{
lean_ctor_set(v___x_2709_, 0, v___x_2714_);
v___x_2716_ = v___x_2709_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v___x_2714_);
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
else
{
v___y_2611_ = v___y_2675_;
v___y_2612_ = v___y_2677_;
v___y_2613_ = v___y_2676_;
v___y_2614_ = v_ref_2679_;
v___y_2615_ = v___x_2685_;
v___y_2616_ = v___y_2680_;
v___y_2617_ = v___x_2702_;
v___y_2618_ = v_options_2681_;
goto v___jp_2610_;
}
}
else
{
v___y_2611_ = v___y_2675_;
v___y_2612_ = v___y_2677_;
v___y_2613_ = v___y_2676_;
v___y_2614_ = v_ref_2679_;
v___y_2615_ = v___x_2685_;
v___y_2616_ = v___y_2680_;
v___y_2617_ = v___x_2702_;
v___y_2618_ = v_options_2681_;
goto v___jp_2610_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7___boxed(lean_object** _args){
lean_object* v_ctx_2738_ = _args[0];
lean_object* v_aig_2739_ = _args[1];
lean_object* v_atomsAssignment_2740_ = _args[2];
lean_object* v_goal_2741_ = _args[3];
lean_object* v_unusedHypotheses_2742_ = _args[4];
lean_object* v_reflectionResult_2743_ = _args[5];
lean_object* v___x_2744_ = _args[6];
lean_object* v___x_2745_ = _args[7];
lean_object* v___f_2746_ = _args[8];
lean_object* v___x_2747_ = _args[9];
lean_object* v___f_2748_ = _args[10];
lean_object* v___f_2749_ = _args[11];
lean_object* v___x_2750_ = _args[12];
lean_object* v___x_2751_ = _args[13];
lean_object* v_a_2752_ = _args[14];
lean_object* v_____r_2753_ = _args[15];
lean_object* v___y_2754_ = _args[16];
lean_object* v___y_2755_ = _args[17];
lean_object* v___y_2756_ = _args[18];
lean_object* v___y_2757_ = _args[19];
lean_object* v___y_2758_ = _args[20];
_start:
{
uint8_t v___x_69528__boxed_2759_; lean_object* v_res_2760_; 
v___x_69528__boxed_2759_ = lean_unbox(v___x_2744_);
v_res_2760_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(v_ctx_2738_, v_aig_2739_, v_atomsAssignment_2740_, v_goal_2741_, v_unusedHypotheses_2742_, v_reflectionResult_2743_, v___x_69528__boxed_2759_, v___x_2745_, v___f_2746_, v___x_2747_, v___f_2748_, v___f_2749_, v___x_2750_, v___x_2751_, v_a_2752_, v_____r_2753_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_);
lean_dec(v___y_2757_);
lean_dec_ref(v___y_2756_);
lean_dec(v___y_2755_);
lean_dec_ref(v___y_2754_);
lean_dec_ref(v___x_2747_);
lean_dec_ref(v_atomsAssignment_2740_);
return v_res_2760_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__10(lean_object* v_e_2761_){
_start:
{
if (lean_obj_tag(v_e_2761_) == 0)
{
uint8_t v___x_2762_; 
v___x_2762_ = 2;
return v___x_2762_;
}
else
{
uint8_t v___x_2763_; 
v___x_2763_ = 0;
return v___x_2763_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__10___boxed(lean_object* v_e_2764_){
_start:
{
uint8_t v_res_2765_; lean_object* v_r_2766_; 
v_res_2765_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__10(v_e_2764_);
lean_dec_ref(v_e_2764_);
v_r_2766_ = lean_box(v_res_2765_);
return v_r_2766_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(lean_object* v_cls_2767_, uint8_t v_collapsed_2768_, lean_object* v_tag_2769_, lean_object* v_opts_2770_, uint8_t v_clsEnabled_2771_, lean_object* v_oldTraces_2772_, lean_object* v_msg_2773_, lean_object* v_resStartStop_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_){
_start:
{
lean_object* v_fst_2780_; lean_object* v_snd_2781_; lean_object* v___y_2783_; lean_object* v___y_2784_; lean_object* v_data_2785_; lean_object* v_fst_2796_; lean_object* v_snd_2797_; lean_object* v___x_2798_; uint8_t v___x_2799_; lean_object* v___y_2801_; lean_object* v_a_2802_; uint8_t v___y_2817_; double v___y_2849_; 
v_fst_2780_ = lean_ctor_get(v_resStartStop_2774_, 0);
lean_inc(v_fst_2780_);
v_snd_2781_ = lean_ctor_get(v_resStartStop_2774_, 1);
lean_inc(v_snd_2781_);
lean_dec_ref(v_resStartStop_2774_);
v_fst_2796_ = lean_ctor_get(v_snd_2781_, 0);
lean_inc(v_fst_2796_);
v_snd_2797_ = lean_ctor_get(v_snd_2781_, 1);
lean_inc(v_snd_2797_);
lean_dec(v_snd_2781_);
v___x_2798_ = l_Lean_trace_profiler;
v___x_2799_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_2770_, v___x_2798_);
if (v___x_2799_ == 0)
{
v___y_2817_ = v___x_2799_;
goto v___jp_2816_;
}
else
{
lean_object* v___x_2854_; uint8_t v___x_2855_; 
v___x_2854_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2855_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_2770_, v___x_2854_);
if (v___x_2855_ == 0)
{
lean_object* v___x_2856_; lean_object* v___x_2857_; double v___x_2858_; double v___x_2859_; double v___x_2860_; 
v___x_2856_ = l_Lean_trace_profiler_threshold;
v___x_2857_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_2770_, v___x_2856_);
v___x_2858_ = lean_float_of_nat(v___x_2857_);
v___x_2859_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3);
v___x_2860_ = lean_float_div(v___x_2858_, v___x_2859_);
v___y_2849_ = v___x_2860_;
goto v___jp_2848_;
}
else
{
lean_object* v___x_2861_; lean_object* v___x_2862_; double v___x_2863_; 
v___x_2861_ = l_Lean_trace_profiler_threshold;
v___x_2862_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_2770_, v___x_2861_);
v___x_2863_ = lean_float_of_nat(v___x_2862_);
v___y_2849_ = v___x_2863_;
goto v___jp_2848_;
}
}
v___jp_2782_:
{
lean_object* v___x_2786_; 
lean_inc(v___y_2784_);
v___x_2786_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2(v_oldTraces_2772_, v_data_2785_, v___y_2784_, v___y_2783_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_);
if (lean_obj_tag(v___x_2786_) == 0)
{
lean_object* v___x_2787_; 
lean_dec_ref_known(v___x_2786_, 1);
v___x_2787_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(v_fst_2780_);
return v___x_2787_;
}
else
{
lean_object* v_a_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2795_; 
lean_dec(v_fst_2780_);
v_a_2788_ = lean_ctor_get(v___x_2786_, 0);
v_isSharedCheck_2795_ = !lean_is_exclusive(v___x_2786_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2790_ = v___x_2786_;
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_a_2788_);
lean_dec(v___x_2786_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v___x_2793_; 
if (v_isShared_2791_ == 0)
{
v___x_2793_ = v___x_2790_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v_a_2788_);
v___x_2793_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
return v___x_2793_;
}
}
}
}
v___jp_2800_:
{
uint8_t v_result_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; double v___x_2806_; lean_object* v_data_2807_; 
v_result_2803_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__10(v_fst_2780_);
v___x_2804_ = lean_box(v_result_2803_);
v___x_2805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2805_, 0, v___x_2804_);
v___x_2806_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0);
lean_inc_ref(v_tag_2769_);
lean_inc_ref(v___x_2805_);
lean_inc(v_cls_2767_);
v_data_2807_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2807_, 0, v_cls_2767_);
lean_ctor_set(v_data_2807_, 1, v___x_2805_);
lean_ctor_set(v_data_2807_, 2, v_tag_2769_);
lean_ctor_set_float(v_data_2807_, sizeof(void*)*3, v___x_2806_);
lean_ctor_set_float(v_data_2807_, sizeof(void*)*3 + 8, v___x_2806_);
lean_ctor_set_uint8(v_data_2807_, sizeof(void*)*3 + 16, v_collapsed_2768_);
if (v___x_2799_ == 0)
{
lean_dec_ref_known(v___x_2805_, 1);
lean_dec(v_snd_2797_);
lean_dec(v_fst_2796_);
lean_dec_ref(v_tag_2769_);
lean_dec(v_cls_2767_);
v___y_2783_ = v_a_2802_;
v___y_2784_ = v___y_2801_;
v_data_2785_ = v_data_2807_;
goto v___jp_2782_;
}
else
{
lean_object* v_data_2808_; double v___x_2809_; double v___x_2810_; 
lean_dec_ref_known(v_data_2807_, 3);
v_data_2808_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2808_, 0, v_cls_2767_);
lean_ctor_set(v_data_2808_, 1, v___x_2805_);
lean_ctor_set(v_data_2808_, 2, v_tag_2769_);
v___x_2809_ = lean_unbox_float(v_fst_2796_);
lean_dec(v_fst_2796_);
lean_ctor_set_float(v_data_2808_, sizeof(void*)*3, v___x_2809_);
v___x_2810_ = lean_unbox_float(v_snd_2797_);
lean_dec(v_snd_2797_);
lean_ctor_set_float(v_data_2808_, sizeof(void*)*3 + 8, v___x_2810_);
lean_ctor_set_uint8(v_data_2808_, sizeof(void*)*3 + 16, v_collapsed_2768_);
v___y_2783_ = v_a_2802_;
v___y_2784_ = v___y_2801_;
v_data_2785_ = v_data_2808_;
goto v___jp_2782_;
}
}
v___jp_2811_:
{
lean_object* v_ref_2812_; lean_object* v___x_2813_; 
v_ref_2812_ = lean_ctor_get(v___y_2777_, 2);
lean_inc(v___y_2778_);
lean_inc_ref(v___y_2777_);
lean_inc(v___y_2776_);
lean_inc_ref(v___y_2775_);
lean_inc(v_fst_2780_);
v___x_2813_ = lean_apply_6(v_msg_2773_, v_fst_2780_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_, lean_box(0));
if (lean_obj_tag(v___x_2813_) == 0)
{
lean_object* v_a_2814_; 
v_a_2814_ = lean_ctor_get(v___x_2813_, 0);
lean_inc(v_a_2814_);
lean_dec_ref_known(v___x_2813_, 1);
v___y_2801_ = v_ref_2812_;
v_a_2802_ = v_a_2814_;
goto v___jp_2800_;
}
else
{
lean_object* v___x_2815_; 
lean_dec_ref_known(v___x_2813_, 1);
v___x_2815_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2);
v___y_2801_ = v_ref_2812_;
v_a_2802_ = v___x_2815_;
goto v___jp_2800_;
}
}
v___jp_2816_:
{
if (v_clsEnabled_2771_ == 0)
{
if (v___y_2817_ == 0)
{
lean_object* v___x_2818_; lean_object* v_traceState_2819_; lean_object* v_env_2820_; lean_object* v_nextMacroScope_2821_; lean_object* v_ngen_2822_; lean_object* v_auxDeclNGen_2823_; lean_object* v_cache_2824_; lean_object* v_recordedDeps_2825_; lean_object* v_messages_2826_; lean_object* v_infoState_2827_; lean_object* v_snapshotTasks_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2847_; 
lean_dec(v_snd_2797_);
lean_dec(v_fst_2796_);
lean_dec_ref(v_msg_2773_);
lean_dec_ref(v_tag_2769_);
lean_dec(v_cls_2767_);
v___x_2818_ = lean_st_ref_take(v___y_2778_);
v_traceState_2819_ = lean_ctor_get(v___x_2818_, 4);
v_env_2820_ = lean_ctor_get(v___x_2818_, 0);
v_nextMacroScope_2821_ = lean_ctor_get(v___x_2818_, 1);
v_ngen_2822_ = lean_ctor_get(v___x_2818_, 2);
v_auxDeclNGen_2823_ = lean_ctor_get(v___x_2818_, 3);
v_cache_2824_ = lean_ctor_get(v___x_2818_, 5);
v_recordedDeps_2825_ = lean_ctor_get(v___x_2818_, 6);
v_messages_2826_ = lean_ctor_get(v___x_2818_, 7);
v_infoState_2827_ = lean_ctor_get(v___x_2818_, 8);
v_snapshotTasks_2828_ = lean_ctor_get(v___x_2818_, 9);
v_isSharedCheck_2847_ = !lean_is_exclusive(v___x_2818_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2830_ = v___x_2818_;
v_isShared_2831_ = v_isSharedCheck_2847_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_snapshotTasks_2828_);
lean_inc(v_infoState_2827_);
lean_inc(v_messages_2826_);
lean_inc(v_recordedDeps_2825_);
lean_inc(v_cache_2824_);
lean_inc(v_traceState_2819_);
lean_inc(v_auxDeclNGen_2823_);
lean_inc(v_ngen_2822_);
lean_inc(v_nextMacroScope_2821_);
lean_inc(v_env_2820_);
lean_dec(v___x_2818_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2847_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
uint64_t v_tid_2832_; lean_object* v_traces_2833_; lean_object* v___x_2835_; uint8_t v_isShared_2836_; uint8_t v_isSharedCheck_2846_; 
v_tid_2832_ = lean_ctor_get_uint64(v_traceState_2819_, sizeof(void*)*1);
v_traces_2833_ = lean_ctor_get(v_traceState_2819_, 0);
v_isSharedCheck_2846_ = !lean_is_exclusive(v_traceState_2819_);
if (v_isSharedCheck_2846_ == 0)
{
v___x_2835_ = v_traceState_2819_;
v_isShared_2836_ = v_isSharedCheck_2846_;
goto v_resetjp_2834_;
}
else
{
lean_inc(v_traces_2833_);
lean_dec(v_traceState_2819_);
v___x_2835_ = lean_box(0);
v_isShared_2836_ = v_isSharedCheck_2846_;
goto v_resetjp_2834_;
}
v_resetjp_2834_:
{
lean_object* v___x_2837_; lean_object* v___x_2839_; 
v___x_2837_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2772_, v_traces_2833_);
lean_dec_ref(v_traces_2833_);
if (v_isShared_2836_ == 0)
{
lean_ctor_set(v___x_2835_, 0, v___x_2837_);
v___x_2839_ = v___x_2835_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v___x_2837_);
lean_ctor_set_uint64(v_reuseFailAlloc_2845_, sizeof(void*)*1, v_tid_2832_);
v___x_2839_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
lean_object* v___x_2841_; 
if (v_isShared_2831_ == 0)
{
lean_ctor_set(v___x_2830_, 4, v___x_2839_);
v___x_2841_ = v___x_2830_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v_env_2820_);
lean_ctor_set(v_reuseFailAlloc_2844_, 1, v_nextMacroScope_2821_);
lean_ctor_set(v_reuseFailAlloc_2844_, 2, v_ngen_2822_);
lean_ctor_set(v_reuseFailAlloc_2844_, 3, v_auxDeclNGen_2823_);
lean_ctor_set(v_reuseFailAlloc_2844_, 4, v___x_2839_);
lean_ctor_set(v_reuseFailAlloc_2844_, 5, v_cache_2824_);
lean_ctor_set(v_reuseFailAlloc_2844_, 6, v_recordedDeps_2825_);
lean_ctor_set(v_reuseFailAlloc_2844_, 7, v_messages_2826_);
lean_ctor_set(v_reuseFailAlloc_2844_, 8, v_infoState_2827_);
lean_ctor_set(v_reuseFailAlloc_2844_, 9, v_snapshotTasks_2828_);
v___x_2841_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
lean_object* v___x_2842_; lean_object* v___x_2843_; 
v___x_2842_ = lean_st_ref_put(v___y_2778_, v___x_2841_);
v___x_2843_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(v_fst_2780_);
return v___x_2843_;
}
}
}
}
}
else
{
goto v___jp_2811_;
}
}
else
{
goto v___jp_2811_;
}
}
v___jp_2848_:
{
double v___x_2850_; double v___x_2851_; double v___x_2852_; uint8_t v___x_2853_; 
v___x_2850_ = lean_unbox_float(v_snd_2797_);
v___x_2851_ = lean_unbox_float(v_fst_2796_);
v___x_2852_ = lean_float_sub(v___x_2850_, v___x_2851_);
v___x_2853_ = lean_float_decLt(v___y_2849_, v___x_2852_);
v___y_2817_ = v___x_2853_;
goto v___jp_2816_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___boxed(lean_object* v_cls_2864_, lean_object* v_collapsed_2865_, lean_object* v_tag_2866_, lean_object* v_opts_2867_, lean_object* v_clsEnabled_2868_, lean_object* v_oldTraces_2869_, lean_object* v_msg_2870_, lean_object* v_resStartStop_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_){
_start:
{
uint8_t v_collapsed_boxed_2877_; uint8_t v_clsEnabled_boxed_2878_; lean_object* v_res_2879_; 
v_collapsed_boxed_2877_ = lean_unbox(v_collapsed_2865_);
v_clsEnabled_boxed_2878_ = lean_unbox(v_clsEnabled_2868_);
v_res_2879_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(v_cls_2864_, v_collapsed_boxed_2877_, v_tag_2866_, v_opts_2867_, v_clsEnabled_boxed_2878_, v_oldTraces_2869_, v_msg_2870_, v_resStartStop_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec_ref(v_opts_2867_);
return v_res_2879_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__12(lean_object* v_e_2880_){
_start:
{
if (lean_obj_tag(v_e_2880_) == 0)
{
uint8_t v___x_2881_; 
v___x_2881_ = 2;
return v___x_2881_;
}
else
{
uint8_t v___x_2882_; 
v___x_2882_ = 0;
return v___x_2882_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__12___boxed(lean_object* v_e_2883_){
_start:
{
uint8_t v_res_2884_; lean_object* v_r_2885_; 
v_res_2884_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__12(v_e_2883_);
lean_dec_ref(v_e_2883_);
v_r_2885_ = lean_box(v_res_2884_);
return v_r_2885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(lean_object* v_cls_2886_, uint8_t v_collapsed_2887_, lean_object* v_tag_2888_, lean_object* v_opts_2889_, uint8_t v_clsEnabled_2890_, lean_object* v_oldTraces_2891_, lean_object* v_msg_2892_, lean_object* v_resStartStop_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_){
_start:
{
lean_object* v_fst_2899_; lean_object* v_snd_2900_; lean_object* v___y_2902_; lean_object* v___y_2903_; lean_object* v_data_2904_; lean_object* v_fst_2915_; lean_object* v_snd_2916_; lean_object* v___x_2917_; uint8_t v___x_2918_; lean_object* v___y_2920_; lean_object* v_a_2921_; uint8_t v___y_2936_; double v___y_2968_; 
v_fst_2899_ = lean_ctor_get(v_resStartStop_2893_, 0);
lean_inc(v_fst_2899_);
v_snd_2900_ = lean_ctor_get(v_resStartStop_2893_, 1);
lean_inc(v_snd_2900_);
lean_dec_ref(v_resStartStop_2893_);
v_fst_2915_ = lean_ctor_get(v_snd_2900_, 0);
lean_inc(v_fst_2915_);
v_snd_2916_ = lean_ctor_get(v_snd_2900_, 1);
lean_inc(v_snd_2916_);
lean_dec(v_snd_2900_);
v___x_2917_ = l_Lean_trace_profiler;
v___x_2918_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_2889_, v___x_2917_);
if (v___x_2918_ == 0)
{
v___y_2936_ = v___x_2918_;
goto v___jp_2935_;
}
else
{
lean_object* v___x_2973_; uint8_t v___x_2974_; 
v___x_2973_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2974_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_2889_, v___x_2973_);
if (v___x_2974_ == 0)
{
lean_object* v___x_2975_; lean_object* v___x_2976_; double v___x_2977_; double v___x_2978_; double v___x_2979_; 
v___x_2975_ = l_Lean_trace_profiler_threshold;
v___x_2976_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_2889_, v___x_2975_);
v___x_2977_ = lean_float_of_nat(v___x_2976_);
v___x_2978_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3);
v___x_2979_ = lean_float_div(v___x_2977_, v___x_2978_);
v___y_2968_ = v___x_2979_;
goto v___jp_2967_;
}
else
{
lean_object* v___x_2980_; lean_object* v___x_2981_; double v___x_2982_; 
v___x_2980_ = l_Lean_trace_profiler_threshold;
v___x_2981_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_2889_, v___x_2980_);
v___x_2982_ = lean_float_of_nat(v___x_2981_);
v___y_2968_ = v___x_2982_;
goto v___jp_2967_;
}
}
v___jp_2901_:
{
lean_object* v___x_2905_; 
lean_inc(v___y_2903_);
v___x_2905_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2(v_oldTraces_2891_, v_data_2904_, v___y_2903_, v___y_2902_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_);
if (lean_obj_tag(v___x_2905_) == 0)
{
lean_object* v___x_2906_; 
lean_dec_ref_known(v___x_2905_, 1);
v___x_2906_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(v_fst_2899_);
return v___x_2906_;
}
else
{
lean_object* v_a_2907_; lean_object* v___x_2909_; uint8_t v_isShared_2910_; uint8_t v_isSharedCheck_2914_; 
lean_dec(v_fst_2899_);
v_a_2907_ = lean_ctor_get(v___x_2905_, 0);
v_isSharedCheck_2914_ = !lean_is_exclusive(v___x_2905_);
if (v_isSharedCheck_2914_ == 0)
{
v___x_2909_ = v___x_2905_;
v_isShared_2910_ = v_isSharedCheck_2914_;
goto v_resetjp_2908_;
}
else
{
lean_inc(v_a_2907_);
lean_dec(v___x_2905_);
v___x_2909_ = lean_box(0);
v_isShared_2910_ = v_isSharedCheck_2914_;
goto v_resetjp_2908_;
}
v_resetjp_2908_:
{
lean_object* v___x_2912_; 
if (v_isShared_2910_ == 0)
{
v___x_2912_ = v___x_2909_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v_a_2907_);
v___x_2912_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
return v___x_2912_;
}
}
}
}
v___jp_2919_:
{
uint8_t v_result_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; double v___x_2925_; lean_object* v_data_2926_; 
v_result_2922_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__12(v_fst_2899_);
v___x_2923_ = lean_box(v_result_2922_);
v___x_2924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2924_, 0, v___x_2923_);
v___x_2925_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0);
lean_inc_ref(v_tag_2888_);
lean_inc_ref(v___x_2924_);
lean_inc(v_cls_2886_);
v_data_2926_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2926_, 0, v_cls_2886_);
lean_ctor_set(v_data_2926_, 1, v___x_2924_);
lean_ctor_set(v_data_2926_, 2, v_tag_2888_);
lean_ctor_set_float(v_data_2926_, sizeof(void*)*3, v___x_2925_);
lean_ctor_set_float(v_data_2926_, sizeof(void*)*3 + 8, v___x_2925_);
lean_ctor_set_uint8(v_data_2926_, sizeof(void*)*3 + 16, v_collapsed_2887_);
if (v___x_2918_ == 0)
{
lean_dec_ref_known(v___x_2924_, 1);
lean_dec(v_snd_2916_);
lean_dec(v_fst_2915_);
lean_dec_ref(v_tag_2888_);
lean_dec(v_cls_2886_);
v___y_2902_ = v_a_2921_;
v___y_2903_ = v___y_2920_;
v_data_2904_ = v_data_2926_;
goto v___jp_2901_;
}
else
{
lean_object* v_data_2927_; double v___x_2928_; double v___x_2929_; 
lean_dec_ref_known(v_data_2926_, 3);
v_data_2927_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2927_, 0, v_cls_2886_);
lean_ctor_set(v_data_2927_, 1, v___x_2924_);
lean_ctor_set(v_data_2927_, 2, v_tag_2888_);
v___x_2928_ = lean_unbox_float(v_fst_2915_);
lean_dec(v_fst_2915_);
lean_ctor_set_float(v_data_2927_, sizeof(void*)*3, v___x_2928_);
v___x_2929_ = lean_unbox_float(v_snd_2916_);
lean_dec(v_snd_2916_);
lean_ctor_set_float(v_data_2927_, sizeof(void*)*3 + 8, v___x_2929_);
lean_ctor_set_uint8(v_data_2927_, sizeof(void*)*3 + 16, v_collapsed_2887_);
v___y_2902_ = v_a_2921_;
v___y_2903_ = v___y_2920_;
v_data_2904_ = v_data_2927_;
goto v___jp_2901_;
}
}
v___jp_2930_:
{
lean_object* v_ref_2931_; lean_object* v___x_2932_; 
v_ref_2931_ = lean_ctor_get(v___y_2896_, 2);
lean_inc(v___y_2897_);
lean_inc_ref(v___y_2896_);
lean_inc(v___y_2895_);
lean_inc_ref(v___y_2894_);
lean_inc(v_fst_2899_);
v___x_2932_ = lean_apply_6(v_msg_2892_, v_fst_2899_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_, lean_box(0));
if (lean_obj_tag(v___x_2932_) == 0)
{
lean_object* v_a_2933_; 
v_a_2933_ = lean_ctor_get(v___x_2932_, 0);
lean_inc(v_a_2933_);
lean_dec_ref_known(v___x_2932_, 1);
v___y_2920_ = v_ref_2931_;
v_a_2921_ = v_a_2933_;
goto v___jp_2919_;
}
else
{
lean_object* v___x_2934_; 
lean_dec_ref_known(v___x_2932_, 1);
v___x_2934_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2);
v___y_2920_ = v_ref_2931_;
v_a_2921_ = v___x_2934_;
goto v___jp_2919_;
}
}
v___jp_2935_:
{
if (v_clsEnabled_2890_ == 0)
{
if (v___y_2936_ == 0)
{
lean_object* v___x_2937_; lean_object* v_traceState_2938_; lean_object* v_env_2939_; lean_object* v_nextMacroScope_2940_; lean_object* v_ngen_2941_; lean_object* v_auxDeclNGen_2942_; lean_object* v_cache_2943_; lean_object* v_recordedDeps_2944_; lean_object* v_messages_2945_; lean_object* v_infoState_2946_; lean_object* v_snapshotTasks_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_2966_; 
lean_dec(v_snd_2916_);
lean_dec(v_fst_2915_);
lean_dec_ref(v_msg_2892_);
lean_dec_ref(v_tag_2888_);
lean_dec(v_cls_2886_);
v___x_2937_ = lean_st_ref_take(v___y_2897_);
v_traceState_2938_ = lean_ctor_get(v___x_2937_, 4);
v_env_2939_ = lean_ctor_get(v___x_2937_, 0);
v_nextMacroScope_2940_ = lean_ctor_get(v___x_2937_, 1);
v_ngen_2941_ = lean_ctor_get(v___x_2937_, 2);
v_auxDeclNGen_2942_ = lean_ctor_get(v___x_2937_, 3);
v_cache_2943_ = lean_ctor_get(v___x_2937_, 5);
v_recordedDeps_2944_ = lean_ctor_get(v___x_2937_, 6);
v_messages_2945_ = lean_ctor_get(v___x_2937_, 7);
v_infoState_2946_ = lean_ctor_get(v___x_2937_, 8);
v_snapshotTasks_2947_ = lean_ctor_get(v___x_2937_, 9);
v_isSharedCheck_2966_ = !lean_is_exclusive(v___x_2937_);
if (v_isSharedCheck_2966_ == 0)
{
v___x_2949_ = v___x_2937_;
v_isShared_2950_ = v_isSharedCheck_2966_;
goto v_resetjp_2948_;
}
else
{
lean_inc(v_snapshotTasks_2947_);
lean_inc(v_infoState_2946_);
lean_inc(v_messages_2945_);
lean_inc(v_recordedDeps_2944_);
lean_inc(v_cache_2943_);
lean_inc(v_traceState_2938_);
lean_inc(v_auxDeclNGen_2942_);
lean_inc(v_ngen_2941_);
lean_inc(v_nextMacroScope_2940_);
lean_inc(v_env_2939_);
lean_dec(v___x_2937_);
v___x_2949_ = lean_box(0);
v_isShared_2950_ = v_isSharedCheck_2966_;
goto v_resetjp_2948_;
}
v_resetjp_2948_:
{
uint64_t v_tid_2951_; lean_object* v_traces_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2965_; 
v_tid_2951_ = lean_ctor_get_uint64(v_traceState_2938_, sizeof(void*)*1);
v_traces_2952_ = lean_ctor_get(v_traceState_2938_, 0);
v_isSharedCheck_2965_ = !lean_is_exclusive(v_traceState_2938_);
if (v_isSharedCheck_2965_ == 0)
{
v___x_2954_ = v_traceState_2938_;
v_isShared_2955_ = v_isSharedCheck_2965_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_traces_2952_);
lean_dec(v_traceState_2938_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2965_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v___x_2956_; lean_object* v___x_2958_; 
v___x_2956_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2891_, v_traces_2952_);
lean_dec_ref(v_traces_2952_);
if (v_isShared_2955_ == 0)
{
lean_ctor_set(v___x_2954_, 0, v___x_2956_);
v___x_2958_ = v___x_2954_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v___x_2956_);
lean_ctor_set_uint64(v_reuseFailAlloc_2964_, sizeof(void*)*1, v_tid_2951_);
v___x_2958_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
lean_object* v___x_2960_; 
if (v_isShared_2950_ == 0)
{
lean_ctor_set(v___x_2949_, 4, v___x_2958_);
v___x_2960_ = v___x_2949_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_2963_; 
v_reuseFailAlloc_2963_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2963_, 0, v_env_2939_);
lean_ctor_set(v_reuseFailAlloc_2963_, 1, v_nextMacroScope_2940_);
lean_ctor_set(v_reuseFailAlloc_2963_, 2, v_ngen_2941_);
lean_ctor_set(v_reuseFailAlloc_2963_, 3, v_auxDeclNGen_2942_);
lean_ctor_set(v_reuseFailAlloc_2963_, 4, v___x_2958_);
lean_ctor_set(v_reuseFailAlloc_2963_, 5, v_cache_2943_);
lean_ctor_set(v_reuseFailAlloc_2963_, 6, v_recordedDeps_2944_);
lean_ctor_set(v_reuseFailAlloc_2963_, 7, v_messages_2945_);
lean_ctor_set(v_reuseFailAlloc_2963_, 8, v_infoState_2946_);
lean_ctor_set(v_reuseFailAlloc_2963_, 9, v_snapshotTasks_2947_);
v___x_2960_ = v_reuseFailAlloc_2963_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
lean_object* v___x_2961_; lean_object* v___x_2962_; 
v___x_2961_ = lean_st_ref_put(v___y_2897_, v___x_2960_);
v___x_2962_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(v_fst_2899_);
return v___x_2962_;
}
}
}
}
}
else
{
goto v___jp_2930_;
}
}
else
{
goto v___jp_2930_;
}
}
v___jp_2967_:
{
double v___x_2969_; double v___x_2970_; double v___x_2971_; uint8_t v___x_2972_; 
v___x_2969_ = lean_unbox_float(v_snd_2916_);
v___x_2970_ = lean_unbox_float(v_fst_2915_);
v___x_2971_ = lean_float_sub(v___x_2969_, v___x_2970_);
v___x_2972_ = lean_float_decLt(v___y_2968_, v___x_2971_);
v___y_2936_ = v___x_2972_;
goto v___jp_2935_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5___boxed(lean_object* v_cls_2983_, lean_object* v_collapsed_2984_, lean_object* v_tag_2985_, lean_object* v_opts_2986_, lean_object* v_clsEnabled_2987_, lean_object* v_oldTraces_2988_, lean_object* v_msg_2989_, lean_object* v_resStartStop_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_){
_start:
{
uint8_t v_collapsed_boxed_2996_; uint8_t v_clsEnabled_boxed_2997_; lean_object* v_res_2998_; 
v_collapsed_boxed_2996_ = lean_unbox(v_collapsed_2984_);
v_clsEnabled_boxed_2997_ = lean_unbox(v_clsEnabled_2987_);
v_res_2998_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v_cls_2983_, v_collapsed_boxed_2996_, v_tag_2985_, v_opts_2986_, v_clsEnabled_boxed_2997_, v_oldTraces_2988_, v_msg_2989_, v_resStartStop_2990_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_);
lean_dec(v___y_2994_);
lean_dec_ref(v___y_2993_);
lean_dec(v___y_2992_);
lean_dec_ref(v___y_2991_);
lean_dec_ref(v_opts_2986_);
return v_res_2998_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7(void){
_start:
{
lean_object* v_cls_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; 
v_cls_3009_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__4));
v___x_3010_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
v___x_3011_ = l_Lean_Name_append(v___x_3010_, v_cls_3009_);
return v___x_3011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster(lean_object* v_ctx_3014_, lean_object* v_goal_3015_, lean_object* v_reflectionResult_3016_, lean_object* v_atomsAssignment_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_){
_start:
{
lean_object* v___y_3024_; lean_object* v___y_3025_; lean_object* v___y_3026_; lean_object* v___y_3027_; lean_object* v___y_3028_; lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v_bvExpr_3073_; lean_object* v_unusedHypotheses_3074_; lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v_toCold_3137_; lean_object* v_options_3138_; lean_object* v_ref_3139_; lean_object* v_inheritedTraceOptions_3140_; uint8_t v_hasTrace_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___f_3145_; uint8_t v___x_3146_; lean_object* v___x_3147_; 
v_bvExpr_3073_ = lean_ctor_get(v_reflectionResult_3016_, 0);
v_unusedHypotheses_3074_ = lean_ctor_get(v_reflectionResult_3016_, 2);
v_toCold_3137_ = lean_ctor_get(v_a_3020_, 0);
v_options_3138_ = lean_ctor_get(v_toCold_3137_, 2);
v_ref_3139_ = lean_ctor_get(v_a_3020_, 2);
v_inheritedTraceOptions_3140_ = lean_ctor_get(v_toCold_3137_, 11);
v_hasTrace_3141_ = lean_ctor_get_uint8(v_options_3138_, sizeof(void*)*1);
v___x_3142_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__0));
v___x_3143_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__0));
v___x_3144_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__1));
lean_inc_ref(v_bvExpr_3073_);
v___f_3145_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0), 2, 1);
lean_closure_set(v___f_3145_, 0, v_bvExpr_3073_);
v___x_3146_ = 1;
v___x_3147_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
if (v_hasTrace_3141_ == 0)
{
lean_object* v___f_3148_; lean_object* v___f_3149_; lean_object* v___x_3150_; 
v___f_3148_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__1));
v___f_3149_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__2));
v___x_3150_ = l_IO_lazyPure___redArg(v___f_3145_);
if (lean_obj_tag(v___x_3150_) == 0)
{
lean_object* v_a_3151_; lean_object* v___x_3153_; uint8_t v_isShared_3154_; uint8_t v_isSharedCheck_3528_; 
v_a_3151_ = lean_ctor_get(v___x_3150_, 0);
v_isSharedCheck_3528_ = !lean_is_exclusive(v___x_3150_);
if (v_isSharedCheck_3528_ == 0)
{
v___x_3153_ = v___x_3150_;
v_isShared_3154_ = v_isSharedCheck_3528_;
goto v_resetjp_3152_;
}
else
{
lean_inc(v_a_3151_);
lean_dec(v___x_3150_);
v___x_3153_ = lean_box(0);
v_isShared_3154_ = v_isSharedCheck_3528_;
goto v_resetjp_3152_;
}
v_resetjp_3152_:
{
lean_object* v_aig_3155_; lean_object* v___y_3157_; lean_object* v___y_3165_; lean_object* v___y_3166_; lean_object* v___y_3167_; lean_object* v___y_3168_; lean_object* v___y_3169_; lean_object* v___y_3170_; lean_object* v___y_3219_; lean_object* v___y_3220_; lean_object* v___y_3221_; uint8_t v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v_a_3228_; lean_object* v___y_3238_; lean_object* v___y_3239_; lean_object* v___y_3240_; uint8_t v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v_a_3247_; uint8_t v___y_3260_; lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; uint8_t v___y_3264_; lean_object* v___y_3265_; uint8_t v___y_3266_; lean_object* v___y_3267_; lean_object* v___y_3268_; lean_object* v___y_3269_; lean_object* v___y_3270_; uint8_t v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3315_; lean_object* v___y_3316_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v_a_3320_; lean_object* v___y_3347_; lean_object* v___y_3348_; lean_object* v___y_3349_; lean_object* v___y_3350_; lean_object* v___y_3351_; lean_object* v___y_3352_; lean_object* v___y_3363_; uint8_t v___y_3364_; lean_object* v___y_3365_; lean_object* v___y_3366_; lean_object* v___y_3367_; lean_object* v___y_3368_; lean_object* v___y_3369_; lean_object* v___y_3370_; lean_object* v___y_3371_; lean_object* v_a_3372_; lean_object* v___y_3385_; uint8_t v___y_3386_; lean_object* v___y_3387_; lean_object* v___y_3388_; lean_object* v___y_3389_; lean_object* v___y_3390_; lean_object* v___y_3391_; lean_object* v___y_3392_; lean_object* v___y_3393_; lean_object* v_a_3394_; lean_object* v_config_3403_; uint8_t v_graphviz_3404_; lean_object* v___f_3405_; uint8_t v___y_3407_; lean_object* v___y_3408_; lean_object* v___y_3409_; lean_object* v___y_3410_; lean_object* v___y_3411_; lean_object* v___y_3412_; lean_object* v___y_3413_; lean_object* v___y_3414_; lean_object* v___y_3472_; lean_object* v___y_3473_; lean_object* v___y_3474_; lean_object* v_options_3475_; uint8_t v_hasTrace_3476_; lean_object* v_inheritedTraceOptions_3477_; lean_object* v_ref_3478_; lean_object* v___y_3479_; 
v_aig_3155_ = lean_ctor_get(v_a_3151_, 0);
lean_inc_ref(v_aig_3155_);
v_config_3403_ = lean_ctor_get(v_ctx_3014_, 5);
v_graphviz_3404_ = lean_ctor_get_uint8(v_config_3403_, sizeof(void*)*2 + 8);
lean_inc(v_a_3151_);
v___f_3405_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3___boxed), 3, 2);
lean_closure_set(v___f_3405_, 0, v___x_3142_);
lean_closure_set(v___f_3405_, 1, v_a_3151_);
if (v_graphviz_3404_ == 0)
{
lean_dec(v_a_3151_);
v___y_3472_ = v_a_3018_;
v___y_3473_ = v_a_3019_;
v___y_3474_ = v_a_3020_;
v_options_3475_ = v_options_3138_;
v_hasTrace_3476_ = v_hasTrace_3141_;
v_inheritedTraceOptions_3477_ = v_inheritedTraceOptions_3140_;
v_ref_3478_ = v_ref_3139_;
v___y_3479_ = v_a_3021_;
goto v___jp_3471_;
}
else
{
lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; 
v___x_3513_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6);
v___x_3514_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v_a_3151_);
v___x_3515_ = l_IO_FS_writeFile(v___x_3513_, v___x_3514_);
lean_dec_ref(v___x_3514_);
if (lean_obj_tag(v___x_3515_) == 0)
{
lean_dec_ref_known(v___x_3515_, 1);
v___y_3472_ = v_a_3018_;
v___y_3473_ = v_a_3019_;
v___y_3474_ = v_a_3020_;
v_options_3475_ = v_options_3138_;
v_hasTrace_3476_ = v_hasTrace_3141_;
v_inheritedTraceOptions_3477_ = v_inheritedTraceOptions_3140_;
v_ref_3478_ = v_ref_3139_;
v___y_3479_ = v_a_3021_;
goto v___jp_3471_;
}
else
{
lean_object* v_a_3516_; lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3527_; 
lean_dec_ref(v___f_3405_);
lean_dec_ref(v_aig_3155_);
lean_del_object(v___x_3153_);
lean_dec_ref(v_reflectionResult_3016_);
lean_dec(v_goal_3015_);
lean_dec_ref(v_ctx_3014_);
v_a_3516_ = lean_ctor_get(v___x_3515_, 0);
v_isSharedCheck_3527_ = !lean_is_exclusive(v___x_3515_);
if (v_isSharedCheck_3527_ == 0)
{
v___x_3518_ = v___x_3515_;
v_isShared_3519_ = v_isSharedCheck_3527_;
goto v_resetjp_3517_;
}
else
{
lean_inc(v_a_3516_);
lean_dec(v___x_3515_);
v___x_3518_ = lean_box(0);
v_isShared_3519_ = v_isSharedCheck_3527_;
goto v_resetjp_3517_;
}
v_resetjp_3517_:
{
lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3525_; 
v___x_3520_ = lean_io_error_to_string(v_a_3516_);
v___x_3521_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3521_, 0, v___x_3520_);
v___x_3522_ = l_Lean_MessageData_ofFormat(v___x_3521_);
lean_inc(v_ref_3139_);
v___x_3523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3523_, 0, v_ref_3139_);
lean_ctor_set(v___x_3523_, 1, v___x_3522_);
if (v_isShared_3519_ == 0)
{
lean_ctor_set(v___x_3518_, 0, v___x_3523_);
v___x_3525_ = v___x_3518_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v___x_3523_);
v___x_3525_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
return v___x_3525_;
}
}
}
}
v___jp_3156_:
{
lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3162_; 
v___x_3158_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v_aig_3155_, v___y_3157_, v_atomsAssignment_3017_);
lean_dec_ref(v___y_3157_);
v___x_3159_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3159_, 0, v_goal_3015_);
lean_ctor_set(v___x_3159_, 1, v_unusedHypotheses_3074_);
lean_ctor_set(v___x_3159_, 2, v___x_3158_);
v___x_3160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3160_, 0, v___x_3159_);
if (v_isShared_3154_ == 0)
{
lean_ctor_set(v___x_3153_, 0, v___x_3160_);
v___x_3162_ = v___x_3153_;
goto v_reusejp_3161_;
}
else
{
lean_object* v_reuseFailAlloc_3163_; 
v_reuseFailAlloc_3163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3163_, 0, v___x_3160_);
v___x_3162_ = v_reuseFailAlloc_3163_;
goto v_reusejp_3161_;
}
v_reusejp_3161_:
{
return v___x_3162_;
}
}
v___jp_3164_:
{
if (lean_obj_tag(v___y_3170_) == 0)
{
lean_object* v_a_3171_; 
v_a_3171_ = lean_ctor_get(v___y_3170_, 0);
lean_inc(v_a_3171_);
lean_dec_ref_known(v___y_3170_, 1);
if (lean_obj_tag(v_a_3171_) == 0)
{
lean_object* v_toCold_3172_; lean_object* v_options_3173_; uint8_t v_hasTrace_3174_; 
lean_inc_ref(v_unusedHypotheses_3074_);
lean_dec_ref(v_reflectionResult_3016_);
lean_dec_ref(v_ctx_3014_);
v_toCold_3172_ = lean_ctor_get(v___y_3165_, 0);
v_options_3173_ = lean_ctor_get(v_toCold_3172_, 2);
v_hasTrace_3174_ = lean_ctor_get_uint8(v_options_3173_, sizeof(void*)*1);
if (v_hasTrace_3174_ == 0)
{
lean_object* v_a_3175_; 
v_a_3175_ = lean_ctor_get(v_a_3171_, 0);
lean_inc(v_a_3175_);
lean_dec_ref_known(v_a_3171_, 1);
v___y_3157_ = v_a_3175_;
goto v___jp_3156_;
}
else
{
lean_object* v_a_3176_; lean_object* v_inheritedTraceOptions_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; uint8_t v___x_3180_; 
v_a_3176_ = lean_ctor_get(v_a_3171_, 0);
lean_inc(v_a_3176_);
lean_dec_ref_known(v_a_3171_, 1);
v_inheritedTraceOptions_3177_ = lean_ctor_get(v_toCold_3172_, 11);
v___x_3178_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___y_3168_);
v___x_3179_ = l_Lean_Name_append(v___x_3178_, v___y_3168_);
v___x_3180_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3177_, v_options_3173_, v___x_3179_);
lean_dec(v___x_3179_);
if (v___x_3180_ == 0)
{
v___y_3157_ = v_a_3176_;
goto v___jp_3156_;
}
else
{
lean_object* v___x_3181_; lean_object* v___x_3182_; 
v___x_3181_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1);
lean_inc(v___y_3168_);
v___x_3182_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v___y_3168_, v___x_3181_, v___y_3166_, v___y_3167_, v___y_3165_, v___y_3169_);
if (lean_obj_tag(v___x_3182_) == 0)
{
lean_dec_ref_known(v___x_3182_, 1);
v___y_3157_ = v_a_3176_;
goto v___jp_3156_;
}
else
{
lean_object* v_a_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3190_; 
lean_dec(v_a_3176_);
lean_dec_ref(v_aig_3155_);
lean_del_object(v___x_3153_);
lean_dec_ref(v_unusedHypotheses_3074_);
lean_dec(v_goal_3015_);
v_a_3183_ = lean_ctor_get(v___x_3182_, 0);
v_isSharedCheck_3190_ = !lean_is_exclusive(v___x_3182_);
if (v_isSharedCheck_3190_ == 0)
{
v___x_3185_ = v___x_3182_;
v_isShared_3186_ = v_isSharedCheck_3190_;
goto v_resetjp_3184_;
}
else
{
lean_inc(v_a_3183_);
lean_dec(v___x_3182_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3190_;
goto v_resetjp_3184_;
}
v_resetjp_3184_:
{
lean_object* v___x_3188_; 
if (v_isShared_3186_ == 0)
{
v___x_3188_ = v___x_3185_;
goto v_reusejp_3187_;
}
else
{
lean_object* v_reuseFailAlloc_3189_; 
v_reuseFailAlloc_3189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3189_, 0, v_a_3183_);
v___x_3188_ = v_reuseFailAlloc_3189_;
goto v_reusejp_3187_;
}
v_reusejp_3187_:
{
return v___x_3188_;
}
}
}
}
}
}
else
{
lean_object* v_toCold_3191_; lean_object* v_options_3192_; uint8_t v_hasTrace_3193_; 
lean_dec_ref(v_aig_3155_);
lean_del_object(v___x_3153_);
lean_dec(v_goal_3015_);
v_toCold_3191_ = lean_ctor_get(v___y_3165_, 0);
v_options_3192_ = lean_ctor_get(v_toCold_3191_, 2);
v_hasTrace_3193_ = lean_ctor_get_uint8(v_options_3192_, sizeof(void*)*1);
if (v_hasTrace_3193_ == 0)
{
lean_object* v_a_3194_; 
v_a_3194_ = lean_ctor_get(v_a_3171_, 0);
lean_inc(v_a_3194_);
lean_dec_ref_known(v_a_3171_, 1);
v___y_3049_ = v_a_3194_;
v___y_3050_ = v___y_3166_;
v___y_3051_ = v___y_3167_;
v___y_3052_ = v___y_3165_;
v___y_3053_ = v___y_3169_;
goto v___jp_3048_;
}
else
{
lean_object* v_a_3195_; lean_object* v_inheritedTraceOptions_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; uint8_t v___x_3199_; 
v_a_3195_ = lean_ctor_get(v_a_3171_, 0);
lean_inc(v_a_3195_);
lean_dec_ref_known(v_a_3171_, 1);
v_inheritedTraceOptions_3196_ = lean_ctor_get(v_toCold_3191_, 11);
v___x_3197_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___y_3168_);
v___x_3198_ = l_Lean_Name_append(v___x_3197_, v___y_3168_);
v___x_3199_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3196_, v_options_3192_, v___x_3198_);
lean_dec(v___x_3198_);
if (v___x_3199_ == 0)
{
v___y_3049_ = v_a_3195_;
v___y_3050_ = v___y_3166_;
v___y_3051_ = v___y_3167_;
v___y_3052_ = v___y_3165_;
v___y_3053_ = v___y_3169_;
goto v___jp_3048_;
}
else
{
lean_object* v___x_3200_; lean_object* v___x_3201_; 
v___x_3200_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3);
lean_inc(v___y_3168_);
v___x_3201_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v___y_3168_, v___x_3200_, v___y_3166_, v___y_3167_, v___y_3165_, v___y_3169_);
if (lean_obj_tag(v___x_3201_) == 0)
{
lean_dec_ref_known(v___x_3201_, 1);
v___y_3049_ = v_a_3195_;
v___y_3050_ = v___y_3166_;
v___y_3051_ = v___y_3167_;
v___y_3052_ = v___y_3165_;
v___y_3053_ = v___y_3169_;
goto v___jp_3048_;
}
else
{
lean_object* v_a_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3209_; 
lean_dec(v_a_3195_);
lean_dec_ref(v_reflectionResult_3016_);
lean_dec_ref(v_ctx_3014_);
v_a_3202_ = lean_ctor_get(v___x_3201_, 0);
v_isSharedCheck_3209_ = !lean_is_exclusive(v___x_3201_);
if (v_isSharedCheck_3209_ == 0)
{
v___x_3204_ = v___x_3201_;
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_a_3202_);
lean_dec(v___x_3201_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3207_; 
if (v_isShared_3205_ == 0)
{
v___x_3207_ = v___x_3204_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v_a_3202_);
v___x_3207_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
return v___x_3207_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3210_; lean_object* v___x_3212_; uint8_t v_isShared_3213_; uint8_t v_isSharedCheck_3217_; 
lean_dec_ref(v_aig_3155_);
lean_del_object(v___x_3153_);
lean_dec_ref(v_reflectionResult_3016_);
lean_dec(v_goal_3015_);
lean_dec_ref(v_ctx_3014_);
v_a_3210_ = lean_ctor_get(v___y_3170_, 0);
v_isSharedCheck_3217_ = !lean_is_exclusive(v___y_3170_);
if (v_isSharedCheck_3217_ == 0)
{
v___x_3212_ = v___y_3170_;
v_isShared_3213_ = v_isSharedCheck_3217_;
goto v_resetjp_3211_;
}
else
{
lean_inc(v_a_3210_);
lean_dec(v___y_3170_);
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
v___jp_3218_:
{
lean_object* v___x_3229_; double v___x_3230_; double v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; 
v___x_3229_ = lean_io_get_num_heartbeats();
v___x_3230_ = lean_float_of_nat(v___y_3227_);
v___x_3231_ = lean_float_of_nat(v___x_3229_);
v___x_3232_ = lean_box_float(v___x_3230_);
v___x_3233_ = lean_box_float(v___x_3231_);
v___x_3234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3234_, 0, v___x_3232_);
lean_ctor_set(v___x_3234_, 1, v___x_3233_);
v___x_3235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3235_, 0, v_a_3228_);
lean_ctor_set(v___x_3235_, 1, v___x_3234_);
lean_inc(v___y_3225_);
v___x_3236_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_3225_, v___x_3146_, v___x_3147_, v___y_3219_, v___y_3222_, v___y_3221_, v___f_3149_, v___x_3235_, v___y_3223_, v___y_3224_, v___y_3220_, v___y_3226_);
v___y_3165_ = v___y_3220_;
v___y_3166_ = v___y_3223_;
v___y_3167_ = v___y_3224_;
v___y_3168_ = v___y_3225_;
v___y_3169_ = v___y_3226_;
v___y_3170_ = v___x_3236_;
goto v___jp_3164_;
}
v___jp_3237_:
{
lean_object* v___x_3248_; double v___x_3249_; double v___x_3250_; double v___x_3251_; double v___x_3252_; double v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; 
v___x_3248_ = lean_io_mono_nanos_now();
v___x_3249_ = lean_float_of_nat(v___y_3244_);
v___x_3250_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3251_ = lean_float_div(v___x_3249_, v___x_3250_);
v___x_3252_ = lean_float_of_nat(v___x_3248_);
v___x_3253_ = lean_float_div(v___x_3252_, v___x_3250_);
v___x_3254_ = lean_box_float(v___x_3251_);
v___x_3255_ = lean_box_float(v___x_3253_);
v___x_3256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3256_, 0, v___x_3254_);
lean_ctor_set(v___x_3256_, 1, v___x_3255_);
v___x_3257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3257_, 0, v_a_3247_);
lean_ctor_set(v___x_3257_, 1, v___x_3256_);
lean_inc(v___y_3245_);
v___x_3258_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_3245_, v___x_3146_, v___x_3147_, v___y_3238_, v___y_3241_, v___y_3240_, v___f_3149_, v___x_3257_, v___y_3242_, v___y_3243_, v___y_3239_, v___y_3246_);
v___y_3165_ = v___y_3239_;
v___y_3166_ = v___y_3242_;
v___y_3167_ = v___y_3243_;
v___y_3168_ = v___y_3245_;
v___y_3169_ = v___y_3246_;
v___y_3170_ = v___x_3258_;
goto v___jp_3164_;
}
v___jp_3259_:
{
lean_object* v___x_3274_; lean_object* v_a_3275_; lean_object* v___x_3276_; uint8_t v___x_3277_; 
v___x_3274_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_3267_);
v_a_3275_ = lean_ctor_get(v___x_3274_, 0);
lean_inc(v_a_3275_);
lean_dec_ref(v___x_3274_);
v___x_3276_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3277_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_3261_, v___x_3276_);
if (v___x_3277_ == 0)
{
lean_object* v___x_3278_; lean_object* v___x_3279_; 
v___x_3278_ = lean_io_mono_nanos_now();
v___x_3279_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_3268_, v___y_3265_, v___y_3262_, v___y_3266_, v___y_3269_, v___y_3260_, v___y_3264_, v___y_3270_, v___y_3267_);
if (lean_obj_tag(v___x_3279_) == 0)
{
lean_object* v_a_3280_; lean_object* v___x_3282_; uint8_t v_isShared_3283_; uint8_t v_isSharedCheck_3287_; 
v_a_3280_ = lean_ctor_get(v___x_3279_, 0);
v_isSharedCheck_3287_ = !lean_is_exclusive(v___x_3279_);
if (v_isSharedCheck_3287_ == 0)
{
v___x_3282_ = v___x_3279_;
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
else
{
lean_inc(v_a_3280_);
lean_dec(v___x_3279_);
v___x_3282_ = lean_box(0);
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
v_resetjp_3281_:
{
lean_object* v___x_3285_; 
if (v_isShared_3283_ == 0)
{
lean_ctor_set_tag(v___x_3282_, 1);
v___x_3285_ = v___x_3282_;
goto v_reusejp_3284_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v_a_3280_);
v___x_3285_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3284_;
}
v_reusejp_3284_:
{
v___y_3238_ = v___y_3261_;
v___y_3239_ = v___y_3270_;
v___y_3240_ = v_a_3275_;
v___y_3241_ = v___y_3271_;
v___y_3242_ = v___y_3272_;
v___y_3243_ = v___y_3263_;
v___y_3244_ = v___x_3278_;
v___y_3245_ = v___y_3273_;
v___y_3246_ = v___y_3267_;
v_a_3247_ = v___x_3285_;
goto v___jp_3237_;
}
}
}
else
{
lean_object* v_a_3288_; lean_object* v___x_3290_; uint8_t v_isShared_3291_; uint8_t v_isSharedCheck_3295_; 
v_a_3288_ = lean_ctor_get(v___x_3279_, 0);
v_isSharedCheck_3295_ = !lean_is_exclusive(v___x_3279_);
if (v_isSharedCheck_3295_ == 0)
{
v___x_3290_ = v___x_3279_;
v_isShared_3291_ = v_isSharedCheck_3295_;
goto v_resetjp_3289_;
}
else
{
lean_inc(v_a_3288_);
lean_dec(v___x_3279_);
v___x_3290_ = lean_box(0);
v_isShared_3291_ = v_isSharedCheck_3295_;
goto v_resetjp_3289_;
}
v_resetjp_3289_:
{
lean_object* v___x_3293_; 
if (v_isShared_3291_ == 0)
{
lean_ctor_set_tag(v___x_3290_, 0);
v___x_3293_ = v___x_3290_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v_a_3288_);
v___x_3293_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3292_;
}
v_reusejp_3292_:
{
v___y_3238_ = v___y_3261_;
v___y_3239_ = v___y_3270_;
v___y_3240_ = v_a_3275_;
v___y_3241_ = v___y_3271_;
v___y_3242_ = v___y_3272_;
v___y_3243_ = v___y_3263_;
v___y_3244_ = v___x_3278_;
v___y_3245_ = v___y_3273_;
v___y_3246_ = v___y_3267_;
v_a_3247_ = v___x_3293_;
goto v___jp_3237_;
}
}
}
}
else
{
lean_object* v___x_3296_; lean_object* v___x_3297_; 
v___x_3296_ = lean_io_get_num_heartbeats();
v___x_3297_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_3268_, v___y_3265_, v___y_3262_, v___y_3266_, v___y_3269_, v___y_3260_, v___y_3264_, v___y_3270_, v___y_3267_);
if (lean_obj_tag(v___x_3297_) == 0)
{
lean_object* v_a_3298_; lean_object* v___x_3300_; uint8_t v_isShared_3301_; uint8_t v_isSharedCheck_3305_; 
v_a_3298_ = lean_ctor_get(v___x_3297_, 0);
v_isSharedCheck_3305_ = !lean_is_exclusive(v___x_3297_);
if (v_isSharedCheck_3305_ == 0)
{
v___x_3300_ = v___x_3297_;
v_isShared_3301_ = v_isSharedCheck_3305_;
goto v_resetjp_3299_;
}
else
{
lean_inc(v_a_3298_);
lean_dec(v___x_3297_);
v___x_3300_ = lean_box(0);
v_isShared_3301_ = v_isSharedCheck_3305_;
goto v_resetjp_3299_;
}
v_resetjp_3299_:
{
lean_object* v___x_3303_; 
if (v_isShared_3301_ == 0)
{
lean_ctor_set_tag(v___x_3300_, 1);
v___x_3303_ = v___x_3300_;
goto v_reusejp_3302_;
}
else
{
lean_object* v_reuseFailAlloc_3304_; 
v_reuseFailAlloc_3304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3304_, 0, v_a_3298_);
v___x_3303_ = v_reuseFailAlloc_3304_;
goto v_reusejp_3302_;
}
v_reusejp_3302_:
{
v___y_3219_ = v___y_3261_;
v___y_3220_ = v___y_3270_;
v___y_3221_ = v_a_3275_;
v___y_3222_ = v___y_3271_;
v___y_3223_ = v___y_3272_;
v___y_3224_ = v___y_3263_;
v___y_3225_ = v___y_3273_;
v___y_3226_ = v___y_3267_;
v___y_3227_ = v___x_3296_;
v_a_3228_ = v___x_3303_;
goto v___jp_3218_;
}
}
}
else
{
lean_object* v_a_3306_; lean_object* v___x_3308_; uint8_t v_isShared_3309_; uint8_t v_isSharedCheck_3313_; 
v_a_3306_ = lean_ctor_get(v___x_3297_, 0);
v_isSharedCheck_3313_ = !lean_is_exclusive(v___x_3297_);
if (v_isSharedCheck_3313_ == 0)
{
v___x_3308_ = v___x_3297_;
v_isShared_3309_ = v_isSharedCheck_3313_;
goto v_resetjp_3307_;
}
else
{
lean_inc(v_a_3306_);
lean_dec(v___x_3297_);
v___x_3308_ = lean_box(0);
v_isShared_3309_ = v_isSharedCheck_3313_;
goto v_resetjp_3307_;
}
v_resetjp_3307_:
{
lean_object* v___x_3311_; 
if (v_isShared_3309_ == 0)
{
lean_ctor_set_tag(v___x_3308_, 0);
v___x_3311_ = v___x_3308_;
goto v_reusejp_3310_;
}
else
{
lean_object* v_reuseFailAlloc_3312_; 
v_reuseFailAlloc_3312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3312_, 0, v_a_3306_);
v___x_3311_ = v_reuseFailAlloc_3312_;
goto v_reusejp_3310_;
}
v_reusejp_3310_:
{
v___y_3219_ = v___y_3261_;
v___y_3220_ = v___y_3270_;
v___y_3221_ = v_a_3275_;
v___y_3222_ = v___y_3271_;
v___y_3223_ = v___y_3272_;
v___y_3224_ = v___y_3263_;
v___y_3225_ = v___y_3273_;
v___y_3226_ = v___y_3267_;
v___y_3227_ = v___x_3296_;
v_a_3228_ = v___x_3311_;
goto v___jp_3218_;
}
}
}
}
}
v___jp_3314_:
{
lean_object* v_toCold_3321_; lean_object* v_options_3322_; uint8_t v_hasTrace_3323_; 
v_toCold_3321_ = lean_ctor_get(v___y_3315_, 0);
v_options_3322_ = lean_ctor_get(v_toCold_3321_, 2);
v_hasTrace_3323_ = lean_ctor_get_uint8(v_options_3322_, sizeof(void*)*1);
if (v_hasTrace_3323_ == 0)
{
lean_object* v_config_3324_; lean_object* v_solver_3325_; lean_object* v_lratPath_3326_; lean_object* v_timeout_3327_; uint8_t v_trimProofs_3328_; uint8_t v_binaryProofs_3329_; uint8_t v_solverMode_3330_; lean_object* v___x_3331_; 
v_config_3324_ = lean_ctor_get(v_ctx_3014_, 5);
v_solver_3325_ = lean_ctor_get(v_ctx_3014_, 3);
v_lratPath_3326_ = lean_ctor_get(v_ctx_3014_, 4);
v_timeout_3327_ = lean_ctor_get(v_config_3324_, 0);
v_trimProofs_3328_ = lean_ctor_get_uint8(v_config_3324_, sizeof(void*)*2);
v_binaryProofs_3329_ = lean_ctor_get_uint8(v_config_3324_, sizeof(void*)*2 + 1);
v_solverMode_3330_ = lean_ctor_get_uint8(v_config_3324_, sizeof(void*)*2 + 10);
lean_inc(v_timeout_3327_);
lean_inc_ref(v_lratPath_3326_);
lean_inc_ref(v_solver_3325_);
v___x_3331_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_a_3320_, v_solver_3325_, v_lratPath_3326_, v_trimProofs_3328_, v_timeout_3327_, v_binaryProofs_3329_, v_solverMode_3330_, v___y_3315_, v___y_3319_);
v___y_3165_ = v___y_3315_;
v___y_3166_ = v___y_3316_;
v___y_3167_ = v___y_3317_;
v___y_3168_ = v___y_3318_;
v___y_3169_ = v___y_3319_;
v___y_3170_ = v___x_3331_;
goto v___jp_3164_;
}
else
{
lean_object* v_config_3332_; lean_object* v_solver_3333_; lean_object* v_lratPath_3334_; lean_object* v_timeout_3335_; uint8_t v_trimProofs_3336_; uint8_t v_binaryProofs_3337_; uint8_t v_solverMode_3338_; lean_object* v_inheritedTraceOptions_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; uint8_t v___x_3342_; 
v_config_3332_ = lean_ctor_get(v_ctx_3014_, 5);
v_solver_3333_ = lean_ctor_get(v_ctx_3014_, 3);
v_lratPath_3334_ = lean_ctor_get(v_ctx_3014_, 4);
v_timeout_3335_ = lean_ctor_get(v_config_3332_, 0);
v_trimProofs_3336_ = lean_ctor_get_uint8(v_config_3332_, sizeof(void*)*2);
v_binaryProofs_3337_ = lean_ctor_get_uint8(v_config_3332_, sizeof(void*)*2 + 1);
v_solverMode_3338_ = lean_ctor_get_uint8(v_config_3332_, sizeof(void*)*2 + 10);
v_inheritedTraceOptions_3339_ = lean_ctor_get(v_toCold_3321_, 11);
v___x_3340_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___y_3318_);
v___x_3341_ = l_Lean_Name_append(v___x_3340_, v___y_3318_);
v___x_3342_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3339_, v_options_3322_, v___x_3341_);
lean_dec(v___x_3341_);
if (v___x_3342_ == 0)
{
lean_object* v___x_3343_; uint8_t v___x_3344_; 
v___x_3343_ = l_Lean_trace_profiler;
v___x_3344_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_3322_, v___x_3343_);
if (v___x_3344_ == 0)
{
lean_object* v___x_3345_; 
lean_inc(v_timeout_3335_);
lean_inc_ref(v_lratPath_3334_);
lean_inc_ref(v_solver_3333_);
v___x_3345_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_a_3320_, v_solver_3333_, v_lratPath_3334_, v_trimProofs_3336_, v_timeout_3335_, v_binaryProofs_3337_, v_solverMode_3338_, v___y_3315_, v___y_3319_);
v___y_3165_ = v___y_3315_;
v___y_3166_ = v___y_3316_;
v___y_3167_ = v___y_3317_;
v___y_3168_ = v___y_3318_;
v___y_3169_ = v___y_3319_;
v___y_3170_ = v___x_3345_;
goto v___jp_3164_;
}
else
{
lean_inc(v_timeout_3335_);
lean_inc_ref(v_solver_3333_);
lean_inc_ref(v_lratPath_3334_);
v___y_3260_ = v_binaryProofs_3337_;
v___y_3261_ = v_options_3322_;
v___y_3262_ = v_lratPath_3334_;
v___y_3263_ = v___y_3317_;
v___y_3264_ = v_solverMode_3338_;
v___y_3265_ = v_solver_3333_;
v___y_3266_ = v_trimProofs_3336_;
v___y_3267_ = v___y_3319_;
v___y_3268_ = v_a_3320_;
v___y_3269_ = v_timeout_3335_;
v___y_3270_ = v___y_3315_;
v___y_3271_ = v___x_3342_;
v___y_3272_ = v___y_3316_;
v___y_3273_ = v___y_3318_;
goto v___jp_3259_;
}
}
else
{
lean_inc(v_timeout_3335_);
lean_inc_ref(v_solver_3333_);
lean_inc_ref(v_lratPath_3334_);
v___y_3260_ = v_binaryProofs_3337_;
v___y_3261_ = v_options_3322_;
v___y_3262_ = v_lratPath_3334_;
v___y_3263_ = v___y_3317_;
v___y_3264_ = v_solverMode_3338_;
v___y_3265_ = v_solver_3333_;
v___y_3266_ = v_trimProofs_3336_;
v___y_3267_ = v___y_3319_;
v___y_3268_ = v_a_3320_;
v___y_3269_ = v_timeout_3335_;
v___y_3270_ = v___y_3315_;
v___y_3271_ = v___x_3342_;
v___y_3272_ = v___y_3316_;
v___y_3273_ = v___y_3318_;
goto v___jp_3259_;
}
}
}
v___jp_3346_:
{
if (lean_obj_tag(v___y_3352_) == 0)
{
lean_object* v_a_3353_; 
v_a_3353_ = lean_ctor_get(v___y_3352_, 0);
lean_inc(v_a_3353_);
lean_dec_ref_known(v___y_3352_, 1);
v___y_3315_ = v___y_3347_;
v___y_3316_ = v___y_3348_;
v___y_3317_ = v___y_3349_;
v___y_3318_ = v___y_3350_;
v___y_3319_ = v___y_3351_;
v_a_3320_ = v_a_3353_;
goto v___jp_3314_;
}
else
{
lean_object* v_a_3354_; lean_object* v___x_3356_; uint8_t v_isShared_3357_; uint8_t v_isSharedCheck_3361_; 
lean_dec_ref(v_aig_3155_);
lean_del_object(v___x_3153_);
lean_dec_ref(v_reflectionResult_3016_);
lean_dec(v_goal_3015_);
lean_dec_ref(v_ctx_3014_);
v_a_3354_ = lean_ctor_get(v___y_3352_, 0);
v_isSharedCheck_3361_ = !lean_is_exclusive(v___y_3352_);
if (v_isSharedCheck_3361_ == 0)
{
v___x_3356_ = v___y_3352_;
v_isShared_3357_ = v_isSharedCheck_3361_;
goto v_resetjp_3355_;
}
else
{
lean_inc(v_a_3354_);
lean_dec(v___y_3352_);
v___x_3356_ = lean_box(0);
v_isShared_3357_ = v_isSharedCheck_3361_;
goto v_resetjp_3355_;
}
v_resetjp_3355_:
{
lean_object* v___x_3359_; 
if (v_isShared_3357_ == 0)
{
v___x_3359_ = v___x_3356_;
goto v_reusejp_3358_;
}
else
{
lean_object* v_reuseFailAlloc_3360_; 
v_reuseFailAlloc_3360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3360_, 0, v_a_3354_);
v___x_3359_ = v_reuseFailAlloc_3360_;
goto v_reusejp_3358_;
}
v_reusejp_3358_:
{
return v___x_3359_;
}
}
}
}
v___jp_3362_:
{
lean_object* v___x_3373_; double v___x_3374_; double v___x_3375_; double v___x_3376_; double v___x_3377_; double v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; 
v___x_3373_ = lean_io_mono_nanos_now();
v___x_3374_ = lean_float_of_nat(v___y_3367_);
v___x_3375_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3376_ = lean_float_div(v___x_3374_, v___x_3375_);
v___x_3377_ = lean_float_of_nat(v___x_3373_);
v___x_3378_ = lean_float_div(v___x_3377_, v___x_3375_);
v___x_3379_ = lean_box_float(v___x_3376_);
v___x_3380_ = lean_box_float(v___x_3378_);
v___x_3381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3381_, 0, v___x_3379_);
lean_ctor_set(v___x_3381_, 1, v___x_3380_);
v___x_3382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3382_, 0, v_a_3372_);
lean_ctor_set(v___x_3382_, 1, v___x_3381_);
lean_inc(v___y_3370_);
v___x_3383_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_3370_, v___x_3146_, v___x_3147_, v___y_3366_, v___y_3364_, v___y_3363_, v___f_3148_, v___x_3382_, v___y_3368_, v___y_3369_, v___y_3365_, v___y_3371_);
v___y_3347_ = v___y_3365_;
v___y_3348_ = v___y_3368_;
v___y_3349_ = v___y_3369_;
v___y_3350_ = v___y_3370_;
v___y_3351_ = v___y_3371_;
v___y_3352_ = v___x_3383_;
goto v___jp_3346_;
}
v___jp_3384_:
{
lean_object* v___x_3395_; double v___x_3396_; double v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; 
v___x_3395_ = lean_io_get_num_heartbeats();
v___x_3396_ = lean_float_of_nat(v___y_3393_);
v___x_3397_ = lean_float_of_nat(v___x_3395_);
v___x_3398_ = lean_box_float(v___x_3396_);
v___x_3399_ = lean_box_float(v___x_3397_);
v___x_3400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3400_, 0, v___x_3398_);
lean_ctor_set(v___x_3400_, 1, v___x_3399_);
v___x_3401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3401_, 0, v_a_3394_);
lean_ctor_set(v___x_3401_, 1, v___x_3400_);
lean_inc(v___y_3391_);
v___x_3402_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_3391_, v___x_3146_, v___x_3147_, v___y_3388_, v___y_3386_, v___y_3385_, v___f_3148_, v___x_3401_, v___y_3389_, v___y_3390_, v___y_3387_, v___y_3392_);
v___y_3347_ = v___y_3387_;
v___y_3348_ = v___y_3389_;
v___y_3349_ = v___y_3390_;
v___y_3350_ = v___y_3391_;
v___y_3351_ = v___y_3392_;
v___y_3352_ = v___x_3402_;
goto v___jp_3346_;
}
v___jp_3406_:
{
lean_object* v___x_3415_; lean_object* v_a_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3470_; 
v___x_3415_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_3414_);
v_a_3416_ = lean_ctor_get(v___x_3415_, 0);
v_isSharedCheck_3470_ = !lean_is_exclusive(v___x_3415_);
if (v_isSharedCheck_3470_ == 0)
{
v___x_3418_ = v___x_3415_;
v_isShared_3419_ = v_isSharedCheck_3470_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_a_3416_);
lean_dec(v___x_3415_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3470_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
lean_object* v___x_3420_; uint8_t v___x_3421_; 
v___x_3420_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3421_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_3410_, v___x_3420_);
if (v___x_3421_ == 0)
{
lean_object* v___x_3422_; lean_object* v___x_3423_; 
v___x_3422_ = lean_io_mono_nanos_now();
v___x_3423_ = l_IO_lazyPure___redArg(v___f_3405_);
if (lean_obj_tag(v___x_3423_) == 0)
{
lean_object* v_a_3424_; lean_object* v___x_3426_; uint8_t v_isShared_3427_; uint8_t v_isSharedCheck_3431_; 
lean_del_object(v___x_3418_);
v_a_3424_ = lean_ctor_get(v___x_3423_, 0);
v_isSharedCheck_3431_ = !lean_is_exclusive(v___x_3423_);
if (v_isSharedCheck_3431_ == 0)
{
v___x_3426_ = v___x_3423_;
v_isShared_3427_ = v_isSharedCheck_3431_;
goto v_resetjp_3425_;
}
else
{
lean_inc(v_a_3424_);
lean_dec(v___x_3423_);
v___x_3426_ = lean_box(0);
v_isShared_3427_ = v_isSharedCheck_3431_;
goto v_resetjp_3425_;
}
v_resetjp_3425_:
{
lean_object* v___x_3429_; 
if (v_isShared_3427_ == 0)
{
lean_ctor_set_tag(v___x_3426_, 1);
v___x_3429_ = v___x_3426_;
goto v_reusejp_3428_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v_a_3424_);
v___x_3429_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3428_;
}
v_reusejp_3428_:
{
v___y_3363_ = v_a_3416_;
v___y_3364_ = v___y_3407_;
v___y_3365_ = v___y_3408_;
v___y_3366_ = v___y_3410_;
v___y_3367_ = v___x_3422_;
v___y_3368_ = v___y_3411_;
v___y_3369_ = v___y_3412_;
v___y_3370_ = v___y_3413_;
v___y_3371_ = v___y_3414_;
v_a_3372_ = v___x_3429_;
goto v___jp_3362_;
}
}
}
else
{
lean_object* v_a_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3445_; 
v_a_3432_ = lean_ctor_get(v___x_3423_, 0);
v_isSharedCheck_3445_ = !lean_is_exclusive(v___x_3423_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3434_ = v___x_3423_;
v_isShared_3435_ = v_isSharedCheck_3445_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_a_3432_);
lean_dec(v___x_3423_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3445_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
lean_object* v___x_3436_; lean_object* v___x_3438_; 
v___x_3436_ = lean_io_error_to_string(v_a_3432_);
if (v_isShared_3435_ == 0)
{
lean_ctor_set_tag(v___x_3434_, 3);
lean_ctor_set(v___x_3434_, 0, v___x_3436_);
v___x_3438_ = v___x_3434_;
goto v_reusejp_3437_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v___x_3436_);
v___x_3438_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3437_;
}
v_reusejp_3437_:
{
lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3442_; 
v___x_3439_ = l_Lean_MessageData_ofFormat(v___x_3438_);
lean_inc(v___y_3409_);
v___x_3440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3440_, 0, v___y_3409_);
lean_ctor_set(v___x_3440_, 1, v___x_3439_);
if (v_isShared_3419_ == 0)
{
lean_ctor_set(v___x_3418_, 0, v___x_3440_);
v___x_3442_ = v___x_3418_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v___x_3440_);
v___x_3442_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
v___y_3363_ = v_a_3416_;
v___y_3364_ = v___y_3407_;
v___y_3365_ = v___y_3408_;
v___y_3366_ = v___y_3410_;
v___y_3367_ = v___x_3422_;
v___y_3368_ = v___y_3411_;
v___y_3369_ = v___y_3412_;
v___y_3370_ = v___y_3413_;
v___y_3371_ = v___y_3414_;
v_a_3372_ = v___x_3442_;
goto v___jp_3362_;
}
}
}
}
}
else
{
lean_object* v___x_3446_; lean_object* v___x_3447_; 
v___x_3446_ = lean_io_get_num_heartbeats();
v___x_3447_ = l_IO_lazyPure___redArg(v___f_3405_);
if (lean_obj_tag(v___x_3447_) == 0)
{
lean_object* v_a_3448_; lean_object* v___x_3450_; uint8_t v_isShared_3451_; uint8_t v_isSharedCheck_3455_; 
lean_del_object(v___x_3418_);
v_a_3448_ = lean_ctor_get(v___x_3447_, 0);
v_isSharedCheck_3455_ = !lean_is_exclusive(v___x_3447_);
if (v_isSharedCheck_3455_ == 0)
{
v___x_3450_ = v___x_3447_;
v_isShared_3451_ = v_isSharedCheck_3455_;
goto v_resetjp_3449_;
}
else
{
lean_inc(v_a_3448_);
lean_dec(v___x_3447_);
v___x_3450_ = lean_box(0);
v_isShared_3451_ = v_isSharedCheck_3455_;
goto v_resetjp_3449_;
}
v_resetjp_3449_:
{
lean_object* v___x_3453_; 
if (v_isShared_3451_ == 0)
{
lean_ctor_set_tag(v___x_3450_, 1);
v___x_3453_ = v___x_3450_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v_a_3448_);
v___x_3453_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
v___y_3385_ = v_a_3416_;
v___y_3386_ = v___y_3407_;
v___y_3387_ = v___y_3408_;
v___y_3388_ = v___y_3410_;
v___y_3389_ = v___y_3411_;
v___y_3390_ = v___y_3412_;
v___y_3391_ = v___y_3413_;
v___y_3392_ = v___y_3414_;
v___y_3393_ = v___x_3446_;
v_a_3394_ = v___x_3453_;
goto v___jp_3384_;
}
}
}
else
{
lean_object* v_a_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3469_; 
v_a_3456_ = lean_ctor_get(v___x_3447_, 0);
v_isSharedCheck_3469_ = !lean_is_exclusive(v___x_3447_);
if (v_isSharedCheck_3469_ == 0)
{
v___x_3458_ = v___x_3447_;
v_isShared_3459_ = v_isSharedCheck_3469_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_a_3456_);
lean_dec(v___x_3447_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3469_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v___x_3460_; lean_object* v___x_3462_; 
v___x_3460_ = lean_io_error_to_string(v_a_3456_);
if (v_isShared_3459_ == 0)
{
lean_ctor_set_tag(v___x_3458_, 3);
lean_ctor_set(v___x_3458_, 0, v___x_3460_);
v___x_3462_ = v___x_3458_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v___x_3460_);
v___x_3462_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3466_; 
v___x_3463_ = l_Lean_MessageData_ofFormat(v___x_3462_);
lean_inc(v___y_3409_);
v___x_3464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3464_, 0, v___y_3409_);
lean_ctor_set(v___x_3464_, 1, v___x_3463_);
if (v_isShared_3419_ == 0)
{
lean_ctor_set(v___x_3418_, 0, v___x_3464_);
v___x_3466_ = v___x_3418_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v___x_3464_);
v___x_3466_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
v___y_3385_ = v_a_3416_;
v___y_3386_ = v___y_3407_;
v___y_3387_ = v___y_3408_;
v___y_3388_ = v___y_3410_;
v___y_3389_ = v___y_3411_;
v___y_3390_ = v___y_3412_;
v___y_3391_ = v___y_3413_;
v___y_3392_ = v___y_3414_;
v___y_3393_ = v___x_3446_;
v_a_3394_ = v___x_3466_;
goto v___jp_3384_;
}
}
}
}
}
}
}
v___jp_3471_:
{
lean_object* v___x_3480_; 
v___x_3480_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
if (v_hasTrace_3476_ == 0)
{
lean_object* v___x_3481_; 
v___x_3481_ = l_IO_lazyPure___redArg(v___f_3405_);
if (lean_obj_tag(v___x_3481_) == 0)
{
lean_object* v_a_3482_; 
v_a_3482_ = lean_ctor_get(v___x_3481_, 0);
lean_inc(v_a_3482_);
lean_dec_ref_known(v___x_3481_, 1);
v___y_3315_ = v___y_3474_;
v___y_3316_ = v___y_3472_;
v___y_3317_ = v___y_3473_;
v___y_3318_ = v___x_3480_;
v___y_3319_ = v___y_3479_;
v_a_3320_ = v_a_3482_;
goto v___jp_3314_;
}
else
{
lean_object* v_a_3483_; lean_object* v___x_3485_; uint8_t v_isShared_3486_; uint8_t v_isSharedCheck_3494_; 
lean_dec_ref(v_aig_3155_);
lean_del_object(v___x_3153_);
lean_dec_ref(v_reflectionResult_3016_);
lean_dec(v_goal_3015_);
lean_dec_ref(v_ctx_3014_);
v_a_3483_ = lean_ctor_get(v___x_3481_, 0);
v_isSharedCheck_3494_ = !lean_is_exclusive(v___x_3481_);
if (v_isSharedCheck_3494_ == 0)
{
v___x_3485_ = v___x_3481_;
v_isShared_3486_ = v_isSharedCheck_3494_;
goto v_resetjp_3484_;
}
else
{
lean_inc(v_a_3483_);
lean_dec(v___x_3481_);
v___x_3485_ = lean_box(0);
v_isShared_3486_ = v_isSharedCheck_3494_;
goto v_resetjp_3484_;
}
v_resetjp_3484_:
{
lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3492_; 
v___x_3487_ = lean_io_error_to_string(v_a_3483_);
v___x_3488_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3488_, 0, v___x_3487_);
v___x_3489_ = l_Lean_MessageData_ofFormat(v___x_3488_);
lean_inc(v_ref_3478_);
v___x_3490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3490_, 0, v_ref_3478_);
lean_ctor_set(v___x_3490_, 1, v___x_3489_);
if (v_isShared_3486_ == 0)
{
lean_ctor_set(v___x_3485_, 0, v___x_3490_);
v___x_3492_ = v___x_3485_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3493_; 
v_reuseFailAlloc_3493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3493_, 0, v___x_3490_);
v___x_3492_ = v_reuseFailAlloc_3493_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
return v___x_3492_;
}
}
}
}
else
{
lean_object* v___x_3495_; uint8_t v___x_3496_; 
v___x_3495_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_3496_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3477_, v_options_3475_, v___x_3495_);
if (v___x_3496_ == 0)
{
lean_object* v___x_3497_; uint8_t v___x_3498_; 
v___x_3497_ = l_Lean_trace_profiler;
v___x_3498_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_3475_, v___x_3497_);
if (v___x_3498_ == 0)
{
lean_object* v___x_3499_; 
v___x_3499_ = l_IO_lazyPure___redArg(v___f_3405_);
if (lean_obj_tag(v___x_3499_) == 0)
{
lean_object* v_a_3500_; 
v_a_3500_ = lean_ctor_get(v___x_3499_, 0);
lean_inc(v_a_3500_);
lean_dec_ref_known(v___x_3499_, 1);
v___y_3315_ = v___y_3474_;
v___y_3316_ = v___y_3472_;
v___y_3317_ = v___y_3473_;
v___y_3318_ = v___x_3480_;
v___y_3319_ = v___y_3479_;
v_a_3320_ = v_a_3500_;
goto v___jp_3314_;
}
else
{
lean_object* v_a_3501_; lean_object* v___x_3503_; uint8_t v_isShared_3504_; uint8_t v_isSharedCheck_3512_; 
lean_dec_ref(v_aig_3155_);
lean_del_object(v___x_3153_);
lean_dec_ref(v_reflectionResult_3016_);
lean_dec(v_goal_3015_);
lean_dec_ref(v_ctx_3014_);
v_a_3501_ = lean_ctor_get(v___x_3499_, 0);
v_isSharedCheck_3512_ = !lean_is_exclusive(v___x_3499_);
if (v_isSharedCheck_3512_ == 0)
{
v___x_3503_ = v___x_3499_;
v_isShared_3504_ = v_isSharedCheck_3512_;
goto v_resetjp_3502_;
}
else
{
lean_inc(v_a_3501_);
lean_dec(v___x_3499_);
v___x_3503_ = lean_box(0);
v_isShared_3504_ = v_isSharedCheck_3512_;
goto v_resetjp_3502_;
}
v_resetjp_3502_:
{
lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3510_; 
v___x_3505_ = lean_io_error_to_string(v_a_3501_);
v___x_3506_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3506_, 0, v___x_3505_);
v___x_3507_ = l_Lean_MessageData_ofFormat(v___x_3506_);
lean_inc(v_ref_3478_);
v___x_3508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3508_, 0, v_ref_3478_);
lean_ctor_set(v___x_3508_, 1, v___x_3507_);
if (v_isShared_3504_ == 0)
{
lean_ctor_set(v___x_3503_, 0, v___x_3508_);
v___x_3510_ = v___x_3503_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v___x_3508_);
v___x_3510_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
return v___x_3510_;
}
}
}
}
else
{
v___y_3407_ = v___x_3496_;
v___y_3408_ = v___y_3474_;
v___y_3409_ = v_ref_3478_;
v___y_3410_ = v_options_3475_;
v___y_3411_ = v___y_3472_;
v___y_3412_ = v___y_3473_;
v___y_3413_ = v___x_3480_;
v___y_3414_ = v___y_3479_;
goto v___jp_3406_;
}
}
else
{
v___y_3407_ = v___x_3496_;
v___y_3408_ = v___y_3474_;
v___y_3409_ = v_ref_3478_;
v___y_3410_ = v_options_3475_;
v___y_3411_ = v___y_3472_;
v___y_3412_ = v___y_3473_;
v___y_3413_ = v___x_3480_;
v___y_3414_ = v___y_3479_;
goto v___jp_3406_;
}
}
}
}
}
else
{
lean_object* v_a_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3540_; 
lean_dec_ref(v_reflectionResult_3016_);
lean_dec(v_goal_3015_);
lean_dec_ref(v_ctx_3014_);
v_a_3529_ = lean_ctor_get(v___x_3150_, 0);
v_isSharedCheck_3540_ = !lean_is_exclusive(v___x_3150_);
if (v_isSharedCheck_3540_ == 0)
{
v___x_3531_ = v___x_3150_;
v_isShared_3532_ = v_isSharedCheck_3540_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_a_3529_);
lean_dec(v___x_3150_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3540_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3538_; 
v___x_3533_ = lean_io_error_to_string(v_a_3529_);
v___x_3534_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3534_, 0, v___x_3533_);
v___x_3535_ = l_Lean_MessageData_ofFormat(v___x_3534_);
lean_inc(v_ref_3139_);
v___x_3536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3536_, 0, v_ref_3139_);
lean_ctor_set(v___x_3536_, 1, v___x_3535_);
if (v_isShared_3532_ == 0)
{
lean_ctor_set(v___x_3531_, 0, v___x_3536_);
v___x_3538_ = v___x_3531_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v___x_3536_);
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
else
{
lean_object* v_cls_3541_; lean_object* v___f_3542_; lean_object* v___f_3543_; lean_object* v___f_3544_; lean_object* v___f_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; uint8_t v___x_3548_; lean_object* v___y_3550_; lean_object* v___y_3551_; lean_object* v_a_3552_; lean_object* v___y_3562_; lean_object* v___y_3563_; lean_object* v_a_3564_; lean_object* v___y_3567_; lean_object* v___y_3568_; lean_object* v___y_3569_; lean_object* v___y_3580_; lean_object* v___y_3581_; lean_object* v___y_3582_; lean_object* v_a_3583_; lean_object* v___y_3602_; lean_object* v___y_3603_; lean_object* v___y_3604_; lean_object* v___y_3605_; lean_object* v___y_3609_; lean_object* v___y_3610_; lean_object* v___y_3611_; lean_object* v___y_3612_; lean_object* v___y_3613_; uint8_t v___y_3614_; lean_object* v_a_3615_; lean_object* v___y_3625_; lean_object* v___y_3626_; lean_object* v___y_3627_; lean_object* v___y_3628_; lean_object* v___y_3629_; uint8_t v___y_3630_; lean_object* v_a_3631_; lean_object* v___y_3644_; lean_object* v___y_3645_; lean_object* v___y_3646_; uint8_t v___y_3647_; uint8_t v___y_3648_; lean_object* v___y_3709_; lean_object* v___y_3710_; lean_object* v_a_3711_; lean_object* v___y_3724_; lean_object* v___y_3725_; lean_object* v_a_3726_; lean_object* v___y_3729_; lean_object* v___y_3730_; lean_object* v___y_3731_; lean_object* v___y_3742_; lean_object* v___y_3743_; lean_object* v___y_3744_; lean_object* v_a_3745_; lean_object* v___y_3764_; lean_object* v___y_3765_; lean_object* v___y_3766_; lean_object* v___y_3767_; lean_object* v___y_3771_; lean_object* v___y_3772_; lean_object* v___y_3773_; uint8_t v___y_3774_; lean_object* v___y_3775_; lean_object* v___y_3776_; lean_object* v_a_3777_; lean_object* v___y_3790_; lean_object* v___y_3791_; lean_object* v___y_3792_; lean_object* v___y_3793_; uint8_t v___y_3794_; lean_object* v___y_3795_; lean_object* v_a_3796_; lean_object* v___y_3806_; lean_object* v___y_3807_; uint8_t v___y_3808_; lean_object* v___y_3809_; uint8_t v___y_3810_; 
v_cls_3541_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__4));
v___f_3542_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__1));
v___f_3543_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__2));
v___f_3544_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5));
v___f_3545_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6));
v___x_3546_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
v___x_3547_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7);
v___x_3548_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3140_, v_options_3138_, v___x_3547_);
if (v___x_3548_ == 0)
{
lean_object* v___x_3907_; uint8_t v___x_3908_; 
v___x_3907_ = l_Lean_trace_profiler;
v___x_3908_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_3138_, v___x_3907_);
if (v___x_3908_ == 0)
{
lean_object* v___y_3910_; lean_object* v___y_3911_; lean_object* v___y_3912_; lean_object* v___y_3913_; lean_object* v___y_3914_; lean_object* v___y_3915_; uint8_t v___y_3916_; lean_object* v___y_3917_; lean_object* v___y_3918_; lean_object* v___y_3919_; lean_object* v_a_3920_; lean_object* v___y_3933_; lean_object* v___y_3934_; lean_object* v___y_3935_; lean_object* v___y_3936_; lean_object* v___y_3937_; uint8_t v___y_3938_; lean_object* v___y_3939_; lean_object* v___y_3940_; lean_object* v___y_3941_; lean_object* v___y_3942_; lean_object* v_a_3943_; lean_object* v___y_3953_; lean_object* v___y_3954_; lean_object* v___y_3955_; lean_object* v___y_3956_; uint8_t v___y_3957_; lean_object* v___y_3958_; lean_object* v___y_3959_; lean_object* v___y_3960_; lean_object* v___y_3961_; uint8_t v___y_3962_; lean_object* v___y_3963_; uint8_t v___y_3964_; lean_object* v___y_3965_; uint8_t v___y_3966_; lean_object* v___y_3967_; lean_object* v___y_4009_; lean_object* v___y_4010_; lean_object* v___y_4011_; lean_object* v___y_4012_; lean_object* v___y_4013_; lean_object* v___y_4014_; lean_object* v_a_4015_; lean_object* v___y_4040_; lean_object* v___y_4041_; lean_object* v___y_4042_; lean_object* v___y_4043_; lean_object* v___y_4044_; lean_object* v___y_4045_; lean_object* v___y_4046_; lean_object* v___y_4057_; lean_object* v___y_4058_; lean_object* v___y_4059_; lean_object* v___y_4060_; lean_object* v___y_4061_; lean_object* v___y_4062_; lean_object* v___y_4063_; lean_object* v___y_4064_; uint8_t v___y_4065_; lean_object* v___y_4066_; lean_object* v_a_4067_; lean_object* v___y_4080_; lean_object* v___y_4081_; lean_object* v___y_4082_; lean_object* v___y_4083_; lean_object* v___y_4084_; lean_object* v___y_4085_; lean_object* v___y_4086_; lean_object* v___y_4087_; uint8_t v___y_4088_; lean_object* v___y_4089_; lean_object* v_a_4090_; lean_object* v___y_4100_; lean_object* v___y_4101_; lean_object* v___y_4102_; lean_object* v___y_4103_; lean_object* v___y_4104_; lean_object* v___y_4105_; lean_object* v___y_4106_; uint8_t v___y_4107_; lean_object* v___y_4108_; lean_object* v___y_4109_; lean_object* v___y_4167_; lean_object* v___y_4168_; lean_object* v___y_4169_; lean_object* v___y_4170_; lean_object* v___y_4171_; lean_object* v_toCold_4172_; lean_object* v_ref_4173_; lean_object* v___y_4174_; lean_object* v___y_4211_; lean_object* v___y_4212_; lean_object* v___y_4213_; lean_object* v___y_4214_; lean_object* v___y_4215_; lean_object* v___y_4216_; lean_object* v___y_4217_; lean_object* v_a_4240_; lean_object* v___y_4262_; lean_object* v___y_4273_; lean_object* v___y_4274_; lean_object* v_a_4275_; lean_object* v___y_4288_; lean_object* v___y_4289_; lean_object* v_a_4290_; 
if (v___x_3548_ == 0)
{
if (v___x_3908_ == 0)
{
lean_object* v___x_4356_; 
v___x_4356_ = l_IO_lazyPure___redArg(v___f_3145_);
if (lean_obj_tag(v___x_4356_) == 0)
{
lean_object* v_a_4357_; 
v_a_4357_ = lean_ctor_get(v___x_4356_, 0);
lean_inc(v_a_4357_);
lean_dec_ref_known(v___x_4356_, 1);
v_a_4240_ = v_a_4357_;
goto v___jp_4239_;
}
else
{
lean_object* v_a_4358_; lean_object* v___x_4360_; uint8_t v_isShared_4361_; uint8_t v_isSharedCheck_4369_; 
lean_dec_ref(v_reflectionResult_3016_);
lean_dec(v_goal_3015_);
lean_dec_ref(v_ctx_3014_);
v_a_4358_ = lean_ctor_get(v___x_4356_, 0);
v_isSharedCheck_4369_ = !lean_is_exclusive(v___x_4356_);
if (v_isSharedCheck_4369_ == 0)
{
v___x_4360_ = v___x_4356_;
v_isShared_4361_ = v_isSharedCheck_4369_;
goto v_resetjp_4359_;
}
else
{
lean_inc(v_a_4358_);
lean_dec(v___x_4356_);
v___x_4360_ = lean_box(0);
v_isShared_4361_ = v_isSharedCheck_4369_;
goto v_resetjp_4359_;
}
v_resetjp_4359_:
{
lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4367_; 
v___x_4362_ = lean_io_error_to_string(v_a_4358_);
v___x_4363_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4363_, 0, v___x_4362_);
v___x_4364_ = l_Lean_MessageData_ofFormat(v___x_4363_);
lean_inc(v_ref_3139_);
v___x_4365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4365_, 0, v_ref_3139_);
lean_ctor_set(v___x_4365_, 1, v___x_4364_);
if (v_isShared_4361_ == 0)
{
lean_ctor_set(v___x_4360_, 0, v___x_4365_);
v___x_4367_ = v___x_4360_;
goto v_reusejp_4366_;
}
else
{
lean_object* v_reuseFailAlloc_4368_; 
v_reuseFailAlloc_4368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4368_, 0, v___x_4365_);
v___x_4367_ = v_reuseFailAlloc_4368_;
goto v_reusejp_4366_;
}
v_reusejp_4366_:
{
return v___x_4367_;
}
}
}
}
else
{
goto v___jp_4299_;
}
}
else
{
goto v___jp_4299_;
}
v___jp_3909_:
{
lean_object* v___x_3921_; double v___x_3922_; double v___x_3923_; double v___x_3924_; double v___x_3925_; double v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; 
v___x_3921_ = lean_io_mono_nanos_now();
v___x_3922_ = lean_float_of_nat(v___y_3915_);
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
lean_inc(v___y_3912_);
v___x_3931_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_3912_, v___x_3146_, v___x_3147_, v___y_3918_, v___y_3916_, v___y_3917_, v___f_3543_, v___x_3930_, v___y_3919_, v___y_3914_, v___y_3913_, v___y_3911_);
v___y_3083_ = v___y_3910_;
v___y_3084_ = v___y_3911_;
v___y_3085_ = v___y_3912_;
v___y_3086_ = v___y_3913_;
v___y_3087_ = v___y_3914_;
v___y_3088_ = v___y_3919_;
v___y_3089_ = v___x_3931_;
goto v___jp_3082_;
}
v___jp_3932_:
{
lean_object* v___x_3944_; double v___x_3945_; double v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; 
v___x_3944_ = lean_io_get_num_heartbeats();
v___x_3945_ = lean_float_of_nat(v___y_3939_);
v___x_3946_ = lean_float_of_nat(v___x_3944_);
v___x_3947_ = lean_box_float(v___x_3945_);
v___x_3948_ = lean_box_float(v___x_3946_);
v___x_3949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3949_, 0, v___x_3947_);
lean_ctor_set(v___x_3949_, 1, v___x_3948_);
v___x_3950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3950_, 0, v_a_3943_);
lean_ctor_set(v___x_3950_, 1, v___x_3949_);
lean_inc(v___y_3935_);
v___x_3951_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_3935_, v___x_3146_, v___x_3147_, v___y_3941_, v___y_3938_, v___y_3940_, v___f_3543_, v___x_3950_, v___y_3942_, v___y_3937_, v___y_3936_, v___y_3934_);
v___y_3083_ = v___y_3933_;
v___y_3084_ = v___y_3934_;
v___y_3085_ = v___y_3935_;
v___y_3086_ = v___y_3936_;
v___y_3087_ = v___y_3937_;
v___y_3088_ = v___y_3942_;
v___y_3089_ = v___x_3951_;
goto v___jp_3082_;
}
v___jp_3952_:
{
lean_object* v___x_3968_; lean_object* v_a_3969_; lean_object* v___x_3970_; uint8_t v___x_3971_; 
v___x_3968_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_3954_);
v_a_3969_ = lean_ctor_get(v___x_3968_, 0);
lean_inc(v_a_3969_);
lean_dec_ref(v___x_3968_);
v___x_3970_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3971_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_3958_, v___x_3970_);
if (v___x_3971_ == 0)
{
lean_object* v___x_3972_; lean_object* v___x_3973_; 
v___x_3972_ = lean_io_mono_nanos_now();
v___x_3973_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_3956_, v___y_3959_, v___y_3965_, v___y_3964_, v___y_3955_, v___y_3966_, v___y_3962_, v___y_3961_, v___y_3954_);
if (lean_obj_tag(v___x_3973_) == 0)
{
lean_object* v_a_3974_; lean_object* v___x_3976_; uint8_t v_isShared_3977_; uint8_t v_isSharedCheck_3981_; 
v_a_3974_ = lean_ctor_get(v___x_3973_, 0);
v_isSharedCheck_3981_ = !lean_is_exclusive(v___x_3973_);
if (v_isSharedCheck_3981_ == 0)
{
v___x_3976_ = v___x_3973_;
v_isShared_3977_ = v_isSharedCheck_3981_;
goto v_resetjp_3975_;
}
else
{
lean_inc(v_a_3974_);
lean_dec(v___x_3973_);
v___x_3976_ = lean_box(0);
v_isShared_3977_ = v_isSharedCheck_3981_;
goto v_resetjp_3975_;
}
v_resetjp_3975_:
{
lean_object* v___x_3979_; 
if (v_isShared_3977_ == 0)
{
lean_ctor_set_tag(v___x_3976_, 1);
v___x_3979_ = v___x_3976_;
goto v_reusejp_3978_;
}
else
{
lean_object* v_reuseFailAlloc_3980_; 
v_reuseFailAlloc_3980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3980_, 0, v_a_3974_);
v___x_3979_ = v_reuseFailAlloc_3980_;
goto v_reusejp_3978_;
}
v_reusejp_3978_:
{
v___y_3910_ = v___y_3953_;
v___y_3911_ = v___y_3954_;
v___y_3912_ = v___y_3960_;
v___y_3913_ = v___y_3961_;
v___y_3914_ = v___y_3963_;
v___y_3915_ = v___x_3972_;
v___y_3916_ = v___y_3957_;
v___y_3917_ = v_a_3969_;
v___y_3918_ = v___y_3958_;
v___y_3919_ = v___y_3967_;
v_a_3920_ = v___x_3979_;
goto v___jp_3909_;
}
}
}
else
{
lean_object* v_a_3982_; lean_object* v___x_3984_; uint8_t v_isShared_3985_; uint8_t v_isSharedCheck_3989_; 
v_a_3982_ = lean_ctor_get(v___x_3973_, 0);
v_isSharedCheck_3989_ = !lean_is_exclusive(v___x_3973_);
if (v_isSharedCheck_3989_ == 0)
{
v___x_3984_ = v___x_3973_;
v_isShared_3985_ = v_isSharedCheck_3989_;
goto v_resetjp_3983_;
}
else
{
lean_inc(v_a_3982_);
lean_dec(v___x_3973_);
v___x_3984_ = lean_box(0);
v_isShared_3985_ = v_isSharedCheck_3989_;
goto v_resetjp_3983_;
}
v_resetjp_3983_:
{
lean_object* v___x_3987_; 
if (v_isShared_3985_ == 0)
{
lean_ctor_set_tag(v___x_3984_, 0);
v___x_3987_ = v___x_3984_;
goto v_reusejp_3986_;
}
else
{
lean_object* v_reuseFailAlloc_3988_; 
v_reuseFailAlloc_3988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3988_, 0, v_a_3982_);
v___x_3987_ = v_reuseFailAlloc_3988_;
goto v_reusejp_3986_;
}
v_reusejp_3986_:
{
v___y_3910_ = v___y_3953_;
v___y_3911_ = v___y_3954_;
v___y_3912_ = v___y_3960_;
v___y_3913_ = v___y_3961_;
v___y_3914_ = v___y_3963_;
v___y_3915_ = v___x_3972_;
v___y_3916_ = v___y_3957_;
v___y_3917_ = v_a_3969_;
v___y_3918_ = v___y_3958_;
v___y_3919_ = v___y_3967_;
v_a_3920_ = v___x_3987_;
goto v___jp_3909_;
}
}
}
}
else
{
lean_object* v___x_3990_; lean_object* v___x_3991_; 
v___x_3990_ = lean_io_get_num_heartbeats();
v___x_3991_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_3956_, v___y_3959_, v___y_3965_, v___y_3964_, v___y_3955_, v___y_3966_, v___y_3962_, v___y_3961_, v___y_3954_);
if (lean_obj_tag(v___x_3991_) == 0)
{
lean_object* v_a_3992_; lean_object* v___x_3994_; uint8_t v_isShared_3995_; uint8_t v_isSharedCheck_3999_; 
v_a_3992_ = lean_ctor_get(v___x_3991_, 0);
v_isSharedCheck_3999_ = !lean_is_exclusive(v___x_3991_);
if (v_isSharedCheck_3999_ == 0)
{
v___x_3994_ = v___x_3991_;
v_isShared_3995_ = v_isSharedCheck_3999_;
goto v_resetjp_3993_;
}
else
{
lean_inc(v_a_3992_);
lean_dec(v___x_3991_);
v___x_3994_ = lean_box(0);
v_isShared_3995_ = v_isSharedCheck_3999_;
goto v_resetjp_3993_;
}
v_resetjp_3993_:
{
lean_object* v___x_3997_; 
if (v_isShared_3995_ == 0)
{
lean_ctor_set_tag(v___x_3994_, 1);
v___x_3997_ = v___x_3994_;
goto v_reusejp_3996_;
}
else
{
lean_object* v_reuseFailAlloc_3998_; 
v_reuseFailAlloc_3998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3998_, 0, v_a_3992_);
v___x_3997_ = v_reuseFailAlloc_3998_;
goto v_reusejp_3996_;
}
v_reusejp_3996_:
{
v___y_3933_ = v___y_3953_;
v___y_3934_ = v___y_3954_;
v___y_3935_ = v___y_3960_;
v___y_3936_ = v___y_3961_;
v___y_3937_ = v___y_3963_;
v___y_3938_ = v___y_3957_;
v___y_3939_ = v___x_3990_;
v___y_3940_ = v_a_3969_;
v___y_3941_ = v___y_3958_;
v___y_3942_ = v___y_3967_;
v_a_3943_ = v___x_3997_;
goto v___jp_3932_;
}
}
}
else
{
lean_object* v_a_4000_; lean_object* v___x_4002_; uint8_t v_isShared_4003_; uint8_t v_isSharedCheck_4007_; 
v_a_4000_ = lean_ctor_get(v___x_3991_, 0);
v_isSharedCheck_4007_ = !lean_is_exclusive(v___x_3991_);
if (v_isSharedCheck_4007_ == 0)
{
v___x_4002_ = v___x_3991_;
v_isShared_4003_ = v_isSharedCheck_4007_;
goto v_resetjp_4001_;
}
else
{
lean_inc(v_a_4000_);
lean_dec(v___x_3991_);
v___x_4002_ = lean_box(0);
v_isShared_4003_ = v_isSharedCheck_4007_;
goto v_resetjp_4001_;
}
v_resetjp_4001_:
{
lean_object* v___x_4005_; 
if (v_isShared_4003_ == 0)
{
lean_ctor_set_tag(v___x_4002_, 0);
v___x_4005_ = v___x_4002_;
goto v_reusejp_4004_;
}
else
{
lean_object* v_reuseFailAlloc_4006_; 
v_reuseFailAlloc_4006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4006_, 0, v_a_4000_);
v___x_4005_ = v_reuseFailAlloc_4006_;
goto v_reusejp_4004_;
}
v_reusejp_4004_:
{
v___y_3933_ = v___y_3953_;
v___y_3934_ = v___y_3954_;
v___y_3935_ = v___y_3960_;
v___y_3936_ = v___y_3961_;
v___y_3937_ = v___y_3963_;
v___y_3938_ = v___y_3957_;
v___y_3939_ = v___x_3990_;
v___y_3940_ = v_a_3969_;
v___y_3941_ = v___y_3958_;
v___y_3942_ = v___y_3967_;
v_a_3943_ = v___x_4005_;
goto v___jp_3932_;
}
}
}
}
}
v___jp_4008_:
{
lean_object* v_toCold_4016_; lean_object* v_options_4017_; uint8_t v_hasTrace_4018_; 
v_toCold_4016_ = lean_ctor_get(v___y_4012_, 0);
v_options_4017_ = lean_ctor_get(v_toCold_4016_, 2);
v_hasTrace_4018_ = lean_ctor_get_uint8(v_options_4017_, sizeof(void*)*1);
if (v_hasTrace_4018_ == 0)
{
lean_object* v_config_4019_; lean_object* v_solver_4020_; lean_object* v_lratPath_4021_; lean_object* v_timeout_4022_; uint8_t v_trimProofs_4023_; uint8_t v_binaryProofs_4024_; uint8_t v_solverMode_4025_; lean_object* v___x_4026_; 
v_config_4019_ = lean_ctor_get(v_ctx_3014_, 5);
v_solver_4020_ = lean_ctor_get(v_ctx_3014_, 3);
v_lratPath_4021_ = lean_ctor_get(v_ctx_3014_, 4);
v_timeout_4022_ = lean_ctor_get(v_config_4019_, 0);
v_trimProofs_4023_ = lean_ctor_get_uint8(v_config_4019_, sizeof(void*)*2);
v_binaryProofs_4024_ = lean_ctor_get_uint8(v_config_4019_, sizeof(void*)*2 + 1);
v_solverMode_4025_ = lean_ctor_get_uint8(v_config_4019_, sizeof(void*)*2 + 10);
lean_inc(v_timeout_4022_);
lean_inc_ref(v_lratPath_4021_);
lean_inc_ref(v_solver_4020_);
v___x_4026_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_a_4015_, v_solver_4020_, v_lratPath_4021_, v_trimProofs_4023_, v_timeout_4022_, v_binaryProofs_4024_, v_solverMode_4025_, v___y_4012_, v___y_4010_);
v___y_3083_ = v___y_4009_;
v___y_3084_ = v___y_4010_;
v___y_3085_ = v___y_4011_;
v___y_3086_ = v___y_4012_;
v___y_3087_ = v___y_4013_;
v___y_3088_ = v___y_4014_;
v___y_3089_ = v___x_4026_;
goto v___jp_3082_;
}
else
{
lean_object* v_config_4027_; lean_object* v_solver_4028_; lean_object* v_lratPath_4029_; lean_object* v_timeout_4030_; uint8_t v_trimProofs_4031_; uint8_t v_binaryProofs_4032_; uint8_t v_solverMode_4033_; lean_object* v_inheritedTraceOptions_4034_; lean_object* v___x_4035_; uint8_t v___x_4036_; 
v_config_4027_ = lean_ctor_get(v_ctx_3014_, 5);
v_solver_4028_ = lean_ctor_get(v_ctx_3014_, 3);
v_lratPath_4029_ = lean_ctor_get(v_ctx_3014_, 4);
v_timeout_4030_ = lean_ctor_get(v_config_4027_, 0);
v_trimProofs_4031_ = lean_ctor_get_uint8(v_config_4027_, sizeof(void*)*2);
v_binaryProofs_4032_ = lean_ctor_get_uint8(v_config_4027_, sizeof(void*)*2 + 1);
v_solverMode_4033_ = lean_ctor_get_uint8(v_config_4027_, sizeof(void*)*2 + 10);
v_inheritedTraceOptions_4034_ = lean_ctor_get(v_toCold_4016_, 11);
lean_inc(v___y_4011_);
v___x_4035_ = l_Lean_Name_append(v___x_3546_, v___y_4011_);
v___x_4036_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4034_, v_options_4017_, v___x_4035_);
lean_dec(v___x_4035_);
if (v___x_4036_ == 0)
{
uint8_t v___x_4037_; 
v___x_4037_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_4017_, v___x_3907_);
if (v___x_4037_ == 0)
{
lean_object* v___x_4038_; 
lean_inc(v_timeout_4030_);
lean_inc_ref(v_lratPath_4029_);
lean_inc_ref(v_solver_4028_);
v___x_4038_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_a_4015_, v_solver_4028_, v_lratPath_4029_, v_trimProofs_4031_, v_timeout_4030_, v_binaryProofs_4032_, v_solverMode_4033_, v___y_4012_, v___y_4010_);
v___y_3083_ = v___y_4009_;
v___y_3084_ = v___y_4010_;
v___y_3085_ = v___y_4011_;
v___y_3086_ = v___y_4012_;
v___y_3087_ = v___y_4013_;
v___y_3088_ = v___y_4014_;
v___y_3089_ = v___x_4038_;
goto v___jp_3082_;
}
else
{
lean_inc_ref(v_lratPath_4029_);
lean_inc_ref(v_solver_4028_);
lean_inc(v_timeout_4030_);
v___y_3953_ = v___y_4009_;
v___y_3954_ = v___y_4010_;
v___y_3955_ = v_timeout_4030_;
v___y_3956_ = v_a_4015_;
v___y_3957_ = v___x_4036_;
v___y_3958_ = v_options_4017_;
v___y_3959_ = v_solver_4028_;
v___y_3960_ = v___y_4011_;
v___y_3961_ = v___y_4012_;
v___y_3962_ = v_solverMode_4033_;
v___y_3963_ = v___y_4013_;
v___y_3964_ = v_trimProofs_4031_;
v___y_3965_ = v_lratPath_4029_;
v___y_3966_ = v_binaryProofs_4032_;
v___y_3967_ = v___y_4014_;
goto v___jp_3952_;
}
}
else
{
lean_inc_ref(v_lratPath_4029_);
lean_inc_ref(v_solver_4028_);
lean_inc(v_timeout_4030_);
v___y_3953_ = v___y_4009_;
v___y_3954_ = v___y_4010_;
v___y_3955_ = v_timeout_4030_;
v___y_3956_ = v_a_4015_;
v___y_3957_ = v___x_4036_;
v___y_3958_ = v_options_4017_;
v___y_3959_ = v_solver_4028_;
v___y_3960_ = v___y_4011_;
v___y_3961_ = v___y_4012_;
v___y_3962_ = v_solverMode_4033_;
v___y_3963_ = v___y_4013_;
v___y_3964_ = v_trimProofs_4031_;
v___y_3965_ = v_lratPath_4029_;
v___y_3966_ = v_binaryProofs_4032_;
v___y_3967_ = v___y_4014_;
goto v___jp_3952_;
}
}
}
v___jp_4039_:
{
if (lean_obj_tag(v___y_4046_) == 0)
{
lean_object* v_a_4047_; 
v_a_4047_ = lean_ctor_get(v___y_4046_, 0);
lean_inc(v_a_4047_);
lean_dec_ref_known(v___y_4046_, 1);
v___y_4009_ = v___y_4040_;
v___y_4010_ = v___y_4041_;
v___y_4011_ = v___y_4042_;
v___y_4012_ = v___y_4043_;
v___y_4013_ = v___y_4044_;
v___y_4014_ = v___y_4045_;
v_a_4015_ = v_a_4047_;
goto v___jp_4008_;
}
else
{
lean_object* v_a_4048_; lean_object* v___x_4050_; uint8_t v_isShared_4051_; uint8_t v_isSharedCheck_4055_; 
lean_dec_ref(v___y_4040_);
lean_dec_ref(v_reflectionResult_3016_);
lean_dec(v_goal_3015_);
lean_dec_ref(v_ctx_3014_);
v_a_4048_ = lean_ctor_get(v___y_4046_, 0);
v_isSharedCheck_4055_ = !lean_is_exclusive(v___y_4046_);
if (v_isSharedCheck_4055_ == 0)
{
v___x_4050_ = v___y_4046_;
v_isShared_4051_ = v_isSharedCheck_4055_;
goto v_resetjp_4049_;
}
else
{
lean_inc(v_a_4048_);
lean_dec(v___y_4046_);
v___x_4050_ = lean_box(0);
v_isShared_4051_ = v_isSharedCheck_4055_;
goto v_resetjp_4049_;
}
v_resetjp_4049_:
{
lean_object* v___x_4053_; 
if (v_isShared_4051_ == 0)
{
v___x_4053_ = v___x_4050_;
goto v_reusejp_4052_;
}
else
{
lean_object* v_reuseFailAlloc_4054_; 
v_reuseFailAlloc_4054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4054_, 0, v_a_4048_);
v___x_4053_ = v_reuseFailAlloc_4054_;
goto v_reusejp_4052_;
}
v_reusejp_4052_:
{
return v___x_4053_;
}
}
}
}
v___jp_4056_:
{
lean_object* v___x_4068_; double v___x_4069_; double v___x_4070_; double v___x_4071_; double v___x_4072_; double v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; 
v___x_4068_ = lean_io_mono_nanos_now();
v___x_4069_ = lean_float_of_nat(v___y_4063_);
v___x_4070_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4071_ = lean_float_div(v___x_4069_, v___x_4070_);
v___x_4072_ = lean_float_of_nat(v___x_4068_);
v___x_4073_ = lean_float_div(v___x_4072_, v___x_4070_);
v___x_4074_ = lean_box_float(v___x_4071_);
v___x_4075_ = lean_box_float(v___x_4073_);
v___x_4076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4076_, 0, v___x_4074_);
lean_ctor_set(v___x_4076_, 1, v___x_4075_);
v___x_4077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4077_, 0, v_a_4067_);
lean_ctor_set(v___x_4077_, 1, v___x_4076_);
lean_inc(v___y_4059_);
v___x_4078_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_4059_, v___x_3146_, v___x_3147_, v___y_4062_, v___y_4065_, v___y_4064_, v___f_3542_, v___x_4077_, v___y_4066_, v___y_4061_, v___y_4060_, v___y_4058_);
v___y_4040_ = v___y_4057_;
v___y_4041_ = v___y_4058_;
v___y_4042_ = v___y_4059_;
v___y_4043_ = v___y_4060_;
v___y_4044_ = v___y_4061_;
v___y_4045_ = v___y_4066_;
v___y_4046_ = v___x_4078_;
goto v___jp_4039_;
}
v___jp_4079_:
{
lean_object* v___x_4091_; double v___x_4092_; double v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; 
v___x_4091_ = lean_io_get_num_heartbeats();
v___x_4092_ = lean_float_of_nat(v___y_4084_);
v___x_4093_ = lean_float_of_nat(v___x_4091_);
v___x_4094_ = lean_box_float(v___x_4092_);
v___x_4095_ = lean_box_float(v___x_4093_);
v___x_4096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4096_, 0, v___x_4094_);
lean_ctor_set(v___x_4096_, 1, v___x_4095_);
v___x_4097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4097_, 0, v_a_4090_);
lean_ctor_set(v___x_4097_, 1, v___x_4096_);
lean_inc(v___y_4082_);
v___x_4098_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_4082_, v___x_3146_, v___x_3147_, v___y_4086_, v___y_4088_, v___y_4087_, v___f_3542_, v___x_4097_, v___y_4089_, v___y_4085_, v___y_4083_, v___y_4081_);
v___y_4040_ = v___y_4080_;
v___y_4041_ = v___y_4081_;
v___y_4042_ = v___y_4082_;
v___y_4043_ = v___y_4083_;
v___y_4044_ = v___y_4085_;
v___y_4045_ = v___y_4089_;
v___y_4046_ = v___x_4098_;
goto v___jp_4039_;
}
v___jp_4099_:
{
lean_object* v___x_4110_; lean_object* v_a_4111_; lean_object* v___x_4113_; uint8_t v_isShared_4114_; uint8_t v_isSharedCheck_4165_; 
v___x_4110_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_4102_);
v_a_4111_ = lean_ctor_get(v___x_4110_, 0);
v_isSharedCheck_4165_ = !lean_is_exclusive(v___x_4110_);
if (v_isSharedCheck_4165_ == 0)
{
v___x_4113_ = v___x_4110_;
v_isShared_4114_ = v_isSharedCheck_4165_;
goto v_resetjp_4112_;
}
else
{
lean_inc(v_a_4111_);
lean_dec(v___x_4110_);
v___x_4113_ = lean_box(0);
v_isShared_4114_ = v_isSharedCheck_4165_;
goto v_resetjp_4112_;
}
v_resetjp_4112_:
{
lean_object* v___x_4115_; uint8_t v___x_4116_; 
v___x_4115_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4116_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_4106_, v___x_4115_);
if (v___x_4116_ == 0)
{
lean_object* v___x_4117_; lean_object* v___x_4118_; 
v___x_4117_ = lean_io_mono_nanos_now();
v___x_4118_ = l_IO_lazyPure___redArg(v___y_4108_);
if (lean_obj_tag(v___x_4118_) == 0)
{
lean_object* v_a_4119_; lean_object* v___x_4121_; uint8_t v_isShared_4122_; uint8_t v_isSharedCheck_4126_; 
lean_del_object(v___x_4113_);
v_a_4119_ = lean_ctor_get(v___x_4118_, 0);
v_isSharedCheck_4126_ = !lean_is_exclusive(v___x_4118_);
if (v_isSharedCheck_4126_ == 0)
{
v___x_4121_ = v___x_4118_;
v_isShared_4122_ = v_isSharedCheck_4126_;
goto v_resetjp_4120_;
}
else
{
lean_inc(v_a_4119_);
lean_dec(v___x_4118_);
v___x_4121_ = lean_box(0);
v_isShared_4122_ = v_isSharedCheck_4126_;
goto v_resetjp_4120_;
}
v_resetjp_4120_:
{
lean_object* v___x_4124_; 
if (v_isShared_4122_ == 0)
{
lean_ctor_set_tag(v___x_4121_, 1);
v___x_4124_ = v___x_4121_;
goto v_reusejp_4123_;
}
else
{
lean_object* v_reuseFailAlloc_4125_; 
v_reuseFailAlloc_4125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4125_, 0, v_a_4119_);
v___x_4124_ = v_reuseFailAlloc_4125_;
goto v_reusejp_4123_;
}
v_reusejp_4123_:
{
v___y_4057_ = v___y_4100_;
v___y_4058_ = v___y_4102_;
v___y_4059_ = v___y_4103_;
v___y_4060_ = v___y_4104_;
v___y_4061_ = v___y_4105_;
v___y_4062_ = v___y_4106_;
v___y_4063_ = v___x_4117_;
v___y_4064_ = v_a_4111_;
v___y_4065_ = v___y_4107_;
v___y_4066_ = v___y_4109_;
v_a_4067_ = v___x_4124_;
goto v___jp_4056_;
}
}
}
else
{
lean_object* v_a_4127_; lean_object* v___x_4129_; uint8_t v_isShared_4130_; uint8_t v_isSharedCheck_4140_; 
v_a_4127_ = lean_ctor_get(v___x_4118_, 0);
v_isSharedCheck_4140_ = !lean_is_exclusive(v___x_4118_);
if (v_isSharedCheck_4140_ == 0)
{
v___x_4129_ = v___x_4118_;
v_isShared_4130_ = v_isSharedCheck_4140_;
goto v_resetjp_4128_;
}
else
{
lean_inc(v_a_4127_);
lean_dec(v___x_4118_);
v___x_4129_ = lean_box(0);
v_isShared_4130_ = v_isSharedCheck_4140_;
goto v_resetjp_4128_;
}
v_resetjp_4128_:
{
lean_object* v___x_4131_; lean_object* v___x_4133_; 
v___x_4131_ = lean_io_error_to_string(v_a_4127_);
if (v_isShared_4130_ == 0)
{
lean_ctor_set_tag(v___x_4129_, 3);
lean_ctor_set(v___x_4129_, 0, v___x_4131_);
v___x_4133_ = v___x_4129_;
goto v_reusejp_4132_;
}
else
{
lean_object* v_reuseFailAlloc_4139_; 
v_reuseFailAlloc_4139_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4139_, 0, v___x_4131_);
v___x_4133_ = v_reuseFailAlloc_4139_;
goto v_reusejp_4132_;
}
v_reusejp_4132_:
{
lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4137_; 
v___x_4134_ = l_Lean_MessageData_ofFormat(v___x_4133_);
lean_inc(v___y_4101_);
v___x_4135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4135_, 0, v___y_4101_);
lean_ctor_set(v___x_4135_, 1, v___x_4134_);
if (v_isShared_4114_ == 0)
{
lean_ctor_set(v___x_4113_, 0, v___x_4135_);
v___x_4137_ = v___x_4113_;
goto v_reusejp_4136_;
}
else
{
lean_object* v_reuseFailAlloc_4138_; 
v_reuseFailAlloc_4138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4138_, 0, v___x_4135_);
v___x_4137_ = v_reuseFailAlloc_4138_;
goto v_reusejp_4136_;
}
v_reusejp_4136_:
{
v___y_4057_ = v___y_4100_;
v___y_4058_ = v___y_4102_;
v___y_4059_ = v___y_4103_;
v___y_4060_ = v___y_4104_;
v___y_4061_ = v___y_4105_;
v___y_4062_ = v___y_4106_;
v___y_4063_ = v___x_4117_;
v___y_4064_ = v_a_4111_;
v___y_4065_ = v___y_4107_;
v___y_4066_ = v___y_4109_;
v_a_4067_ = v___x_4137_;
goto v___jp_4056_;
}
}
}
}
}
else
{
lean_object* v___x_4141_; lean_object* v___x_4142_; 
v___x_4141_ = lean_io_get_num_heartbeats();
v___x_4142_ = l_IO_lazyPure___redArg(v___y_4108_);
if (lean_obj_tag(v___x_4142_) == 0)
{
lean_object* v_a_4143_; lean_object* v___x_4145_; uint8_t v_isShared_4146_; uint8_t v_isSharedCheck_4150_; 
lean_del_object(v___x_4113_);
v_a_4143_ = lean_ctor_get(v___x_4142_, 0);
v_isSharedCheck_4150_ = !lean_is_exclusive(v___x_4142_);
if (v_isSharedCheck_4150_ == 0)
{
v___x_4145_ = v___x_4142_;
v_isShared_4146_ = v_isSharedCheck_4150_;
goto v_resetjp_4144_;
}
else
{
lean_inc(v_a_4143_);
lean_dec(v___x_4142_);
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
v___y_4080_ = v___y_4100_;
v___y_4081_ = v___y_4102_;
v___y_4082_ = v___y_4103_;
v___y_4083_ = v___y_4104_;
v___y_4084_ = v___x_4141_;
v___y_4085_ = v___y_4105_;
v___y_4086_ = v___y_4106_;
v___y_4087_ = v_a_4111_;
v___y_4088_ = v___y_4107_;
v___y_4089_ = v___y_4109_;
v_a_4090_ = v___x_4148_;
goto v___jp_4079_;
}
}
}
else
{
lean_object* v_a_4151_; lean_object* v___x_4153_; uint8_t v_isShared_4154_; uint8_t v_isSharedCheck_4164_; 
v_a_4151_ = lean_ctor_get(v___x_4142_, 0);
v_isSharedCheck_4164_ = !lean_is_exclusive(v___x_4142_);
if (v_isSharedCheck_4164_ == 0)
{
v___x_4153_ = v___x_4142_;
v_isShared_4154_ = v_isSharedCheck_4164_;
goto v_resetjp_4152_;
}
else
{
lean_inc(v_a_4151_);
lean_dec(v___x_4142_);
v___x_4153_ = lean_box(0);
v_isShared_4154_ = v_isSharedCheck_4164_;
goto v_resetjp_4152_;
}
v_resetjp_4152_:
{
lean_object* v___x_4155_; lean_object* v___x_4157_; 
v___x_4155_ = lean_io_error_to_string(v_a_4151_);
if (v_isShared_4154_ == 0)
{
lean_ctor_set_tag(v___x_4153_, 3);
lean_ctor_set(v___x_4153_, 0, v___x_4155_);
v___x_4157_ = v___x_4153_;
goto v_reusejp_4156_;
}
else
{
lean_object* v_reuseFailAlloc_4163_; 
v_reuseFailAlloc_4163_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4163_, 0, v___x_4155_);
v___x_4157_ = v_reuseFailAlloc_4163_;
goto v_reusejp_4156_;
}
v_reusejp_4156_:
{
lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4161_; 
v___x_4158_ = l_Lean_MessageData_ofFormat(v___x_4157_);
lean_inc(v___y_4101_);
v___x_4159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4159_, 0, v___y_4101_);
lean_ctor_set(v___x_4159_, 1, v___x_4158_);
if (v_isShared_4114_ == 0)
{
lean_ctor_set(v___x_4113_, 0, v___x_4159_);
v___x_4161_ = v___x_4113_;
goto v_reusejp_4160_;
}
else
{
lean_object* v_reuseFailAlloc_4162_; 
v_reuseFailAlloc_4162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4162_, 0, v___x_4159_);
v___x_4161_ = v_reuseFailAlloc_4162_;
goto v_reusejp_4160_;
}
v_reusejp_4160_:
{
v___y_4080_ = v___y_4100_;
v___y_4081_ = v___y_4102_;
v___y_4082_ = v___y_4103_;
v___y_4083_ = v___y_4104_;
v___y_4084_ = v___x_4141_;
v___y_4085_ = v___y_4105_;
v___y_4086_ = v___y_4106_;
v___y_4087_ = v_a_4111_;
v___y_4088_ = v___y_4107_;
v___y_4089_ = v___y_4109_;
v_a_4090_ = v___x_4161_;
goto v___jp_4079_;
}
}
}
}
}
}
}
v___jp_4166_:
{
lean_object* v_options_4175_; lean_object* v_inheritedTraceOptions_4176_; uint8_t v_hasTrace_4177_; lean_object* v___x_4178_; 
v_options_4175_ = lean_ctor_get(v_toCold_4172_, 2);
v_inheritedTraceOptions_4176_ = lean_ctor_get(v_toCold_4172_, 11);
v_hasTrace_4177_ = lean_ctor_get_uint8(v_options_4175_, sizeof(void*)*1);
v___x_4178_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
if (v_hasTrace_4177_ == 0)
{
lean_object* v___x_4179_; 
v___x_4179_ = l_IO_lazyPure___redArg(v___y_4168_);
if (lean_obj_tag(v___x_4179_) == 0)
{
lean_object* v_a_4180_; 
v_a_4180_ = lean_ctor_get(v___x_4179_, 0);
lean_inc(v_a_4180_);
lean_dec_ref_known(v___x_4179_, 1);
v___y_4009_ = v___y_4167_;
v___y_4010_ = v___y_4174_;
v___y_4011_ = v___x_4178_;
v___y_4012_ = v___y_4171_;
v___y_4013_ = v___y_4170_;
v___y_4014_ = v___y_4169_;
v_a_4015_ = v_a_4180_;
goto v___jp_4008_;
}
else
{
lean_object* v_a_4181_; lean_object* v___x_4183_; uint8_t v_isShared_4184_; uint8_t v_isSharedCheck_4192_; 
lean_dec_ref(v___y_4167_);
lean_dec_ref(v_reflectionResult_3016_);
lean_dec(v_goal_3015_);
lean_dec_ref(v_ctx_3014_);
v_a_4181_ = lean_ctor_get(v___x_4179_, 0);
v_isSharedCheck_4192_ = !lean_is_exclusive(v___x_4179_);
if (v_isSharedCheck_4192_ == 0)
{
v___x_4183_ = v___x_4179_;
v_isShared_4184_ = v_isSharedCheck_4192_;
goto v_resetjp_4182_;
}
else
{
lean_inc(v_a_4181_);
lean_dec(v___x_4179_);
v___x_4183_ = lean_box(0);
v_isShared_4184_ = v_isSharedCheck_4192_;
goto v_resetjp_4182_;
}
v_resetjp_4182_:
{
lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4190_; 
v___x_4185_ = lean_io_error_to_string(v_a_4181_);
v___x_4186_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4186_, 0, v___x_4185_);
v___x_4187_ = l_Lean_MessageData_ofFormat(v___x_4186_);
lean_inc(v_ref_4173_);
v___x_4188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4188_, 0, v_ref_4173_);
lean_ctor_set(v___x_4188_, 1, v___x_4187_);
if (v_isShared_4184_ == 0)
{
lean_ctor_set(v___x_4183_, 0, v___x_4188_);
v___x_4190_ = v___x_4183_;
goto v_reusejp_4189_;
}
else
{
lean_object* v_reuseFailAlloc_4191_; 
v_reuseFailAlloc_4191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4191_, 0, v___x_4188_);
v___x_4190_ = v_reuseFailAlloc_4191_;
goto v_reusejp_4189_;
}
v_reusejp_4189_:
{
return v___x_4190_;
}
}
}
}
else
{
lean_object* v___x_4193_; uint8_t v___x_4194_; 
v___x_4193_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_4194_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4176_, v_options_4175_, v___x_4193_);
if (v___x_4194_ == 0)
{
uint8_t v___x_4195_; 
v___x_4195_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_4175_, v___x_3907_);
if (v___x_4195_ == 0)
{
lean_object* v___x_4196_; 
v___x_4196_ = l_IO_lazyPure___redArg(v___y_4168_);
if (lean_obj_tag(v___x_4196_) == 0)
{
lean_object* v_a_4197_; 
v_a_4197_ = lean_ctor_get(v___x_4196_, 0);
lean_inc(v_a_4197_);
lean_dec_ref_known(v___x_4196_, 1);
v___y_4009_ = v___y_4167_;
v___y_4010_ = v___y_4174_;
v___y_4011_ = v___x_4178_;
v___y_4012_ = v___y_4171_;
v___y_4013_ = v___y_4170_;
v___y_4014_ = v___y_4169_;
v_a_4015_ = v_a_4197_;
goto v___jp_4008_;
}
else
{
lean_object* v_a_4198_; lean_object* v___x_4200_; uint8_t v_isShared_4201_; uint8_t v_isSharedCheck_4209_; 
lean_dec_ref(v___y_4167_);
lean_dec_ref(v_reflectionResult_3016_);
lean_dec(v_goal_3015_);
lean_dec_ref(v_ctx_3014_);
v_a_4198_ = lean_ctor_get(v___x_4196_, 0);
v_isSharedCheck_4209_ = !lean_is_exclusive(v___x_4196_);
if (v_isSharedCheck_4209_ == 0)
{
v___x_4200_ = v___x_4196_;
v_isShared_4201_ = v_isSharedCheck_4209_;
goto v_resetjp_4199_;
}
else
{
lean_inc(v_a_4198_);
lean_dec(v___x_4196_);
v___x_4200_ = lean_box(0);
v_isShared_4201_ = v_isSharedCheck_4209_;
goto v_resetjp_4199_;
}
v_resetjp_4199_:
{
lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4207_; 
v___x_4202_ = lean_io_error_to_string(v_a_4198_);
v___x_4203_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4203_, 0, v___x_4202_);
v___x_4204_ = l_Lean_MessageData_ofFormat(v___x_4203_);
lean_inc(v_ref_4173_);
v___x_4205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4205_, 0, v_ref_4173_);
lean_ctor_set(v___x_4205_, 1, v___x_4204_);
if (v_isShared_4201_ == 0)
{
lean_ctor_set(v___x_4200_, 0, v___x_4205_);
v___x_4207_ = v___x_4200_;
goto v_reusejp_4206_;
}
else
{
lean_object* v_reuseFailAlloc_4208_; 
v_reuseFailAlloc_4208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4208_, 0, v___x_4205_);
v___x_4207_ = v_reuseFailAlloc_4208_;
goto v_reusejp_4206_;
}
v_reusejp_4206_:
{
return v___x_4207_;
}
}
}
}
else
{
v___y_4100_ = v___y_4167_;
v___y_4101_ = v_ref_4173_;
v___y_4102_ = v___y_4174_;
v___y_4103_ = v___x_4178_;
v___y_4104_ = v___y_4171_;
v___y_4105_ = v___y_4170_;
v___y_4106_ = v_options_4175_;
v___y_4107_ = v___x_4194_;
v___y_4108_ = v___y_4168_;
v___y_4109_ = v___y_4169_;
goto v___jp_4099_;
}
}
else
{
v___y_4100_ = v___y_4167_;
v___y_4101_ = v_ref_4173_;
v___y_4102_ = v___y_4174_;
v___y_4103_ = v___x_4178_;
v___y_4104_ = v___y_4171_;
v___y_4105_ = v___y_4170_;
v___y_4106_ = v_options_4175_;
v___y_4107_ = v___x_4194_;
v___y_4108_ = v___y_4168_;
v___y_4109_ = v___y_4169_;
goto v___jp_4099_;
}
}
}
v___jp_4210_:
{
lean_object* v_config_4218_; uint8_t v_graphviz_4219_; 
v_config_4218_ = lean_ctor_get(v_ctx_3014_, 5);
v_graphviz_4219_ = lean_ctor_get_uint8(v_config_4218_, sizeof(void*)*2 + 8);
if (v_graphviz_4219_ == 0)
{
lean_object* v_toCold_4220_; lean_object* v_ref_4221_; 
lean_dec_ref(v___y_4212_);
v_toCold_4220_ = lean_ctor_get(v___y_4216_, 0);
v_ref_4221_ = lean_ctor_get(v___y_4216_, 2);
v___y_4167_ = v___y_4211_;
v___y_4168_ = v___y_4213_;
v___y_4169_ = v___y_4214_;
v___y_4170_ = v___y_4215_;
v___y_4171_ = v___y_4216_;
v_toCold_4172_ = v_toCold_4220_;
v_ref_4173_ = v_ref_4221_;
v___y_4174_ = v___y_4217_;
goto v___jp_4166_;
}
else
{
lean_object* v_toCold_4222_; lean_object* v_ref_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; 
v_toCold_4222_ = lean_ctor_get(v___y_4216_, 0);
v_ref_4223_ = lean_ctor_get(v___y_4216_, 2);
v___x_4224_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6);
v___x_4225_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_4212_);
v___x_4226_ = l_IO_FS_writeFile(v___x_4224_, v___x_4225_);
lean_dec_ref(v___x_4225_);
if (lean_obj_tag(v___x_4226_) == 0)
{
lean_dec_ref_known(v___x_4226_, 1);
v___y_4167_ = v___y_4211_;
v___y_4168_ = v___y_4213_;
v___y_4169_ = v___y_4214_;
v___y_4170_ = v___y_4215_;
v___y_4171_ = v___y_4216_;
v_toCold_4172_ = v_toCold_4222_;
v_ref_4173_ = v_ref_4223_;
v___y_4174_ = v___y_4217_;
goto v___jp_4166_;
}
else
{
lean_object* v_a_4227_; lean_object* v___x_4229_; uint8_t v_isShared_4230_; uint8_t v_isSharedCheck_4238_; 
lean_dec_ref(v___y_4213_);
lean_dec_ref(v___y_4211_);
lean_dec_ref(v_reflectionResult_3016_);
lean_dec(v_goal_3015_);
lean_dec_ref(v_ctx_3014_);
v_a_4227_ = lean_ctor_get(v___x_4226_, 0);
v_isSharedCheck_4238_ = !lean_is_exclusive(v___x_4226_);
if (v_isSharedCheck_4238_ == 0)
{
v___x_4229_ = v___x_4226_;
v_isShared_4230_ = v_isSharedCheck_4238_;
goto v_resetjp_4228_;
}
else
{
lean_inc(v_a_4227_);
lean_dec(v___x_4226_);
v___x_4229_ = lean_box(0);
v_isShared_4230_ = v_isSharedCheck_4238_;
goto v_resetjp_4228_;
}
v_resetjp_4228_:
{
lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4236_; 
v___x_4231_ = lean_io_error_to_string(v_a_4227_);
v___x_4232_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4232_, 0, v___x_4231_);
v___x_4233_ = l_Lean_MessageData_ofFormat(v___x_4232_);
lean_inc(v_ref_4223_);
v___x_4234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4234_, 0, v_ref_4223_);
lean_ctor_set(v___x_4234_, 1, v___x_4233_);
if (v_isShared_4230_ == 0)
{
lean_ctor_set(v___x_4229_, 0, v___x_4234_);
v___x_4236_ = v___x_4229_;
goto v_reusejp_4235_;
}
else
{
lean_object* v_reuseFailAlloc_4237_; 
v_reuseFailAlloc_4237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4237_, 0, v___x_4234_);
v___x_4236_ = v_reuseFailAlloc_4237_;
goto v_reusejp_4235_;
}
v_reusejp_4235_:
{
return v___x_4236_;
}
}
}
}
}
v___jp_4239_:
{
lean_object* v_aig_4241_; lean_object* v_decls_4242_; lean_object* v___f_4243_; 
v_aig_4241_ = lean_ctor_get(v_a_4240_, 0);
lean_inc_ref(v_aig_4241_);
v_decls_4242_ = lean_ctor_get(v_aig_4241_, 0);
lean_inc_ref(v_a_4240_);
v___f_4243_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3___boxed), 3, 2);
lean_closure_set(v___f_4243_, 0, v___x_3142_);
lean_closure_set(v___f_4243_, 1, v_a_4240_);
if (v___x_3548_ == 0)
{
v___y_4211_ = v_aig_4241_;
v___y_4212_ = v_a_4240_;
v___y_4213_ = v___f_4243_;
v___y_4214_ = v_a_3018_;
v___y_4215_ = v_a_3019_;
v___y_4216_ = v_a_3020_;
v___y_4217_ = v_a_3021_;
goto v___jp_4210_;
}
else
{
lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; 
v___x_4244_ = lean_array_get_size(v_decls_4242_);
v___x_4245_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8));
v___x_4246_ = l_Nat_reprFast(v___x_4244_);
v___x_4247_ = lean_string_append(v___x_4245_, v___x_4246_);
lean_dec_ref(v___x_4246_);
v___x_4248_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__9));
v___x_4249_ = lean_string_append(v___x_4247_, v___x_4248_);
v___x_4250_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4250_, 0, v___x_4249_);
v___x_4251_ = l_Lean_MessageData_ofFormat(v___x_4250_);
v___x_4252_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v_cls_3541_, v___x_4251_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
if (lean_obj_tag(v___x_4252_) == 0)
{
lean_dec_ref_known(v___x_4252_, 1);
v___y_4211_ = v_aig_4241_;
v___y_4212_ = v_a_4240_;
v___y_4213_ = v___f_4243_;
v___y_4214_ = v_a_3018_;
v___y_4215_ = v_a_3019_;
v___y_4216_ = v_a_3020_;
v___y_4217_ = v_a_3021_;
goto v___jp_4210_;
}
else
{
lean_object* v_a_4253_; lean_object* v___x_4255_; uint8_t v_isShared_4256_; uint8_t v_isSharedCheck_4260_; 
lean_dec_ref(v___f_4243_);
lean_dec_ref(v_aig_4241_);
lean_dec_ref(v_a_4240_);
lean_dec_ref(v_reflectionResult_3016_);
lean_dec(v_goal_3015_);
lean_dec_ref(v_ctx_3014_);
v_a_4253_ = lean_ctor_get(v___x_4252_, 0);
v_isSharedCheck_4260_ = !lean_is_exclusive(v___x_4252_);
if (v_isSharedCheck_4260_ == 0)
{
v___x_4255_ = v___x_4252_;
v_isShared_4256_ = v_isSharedCheck_4260_;
goto v_resetjp_4254_;
}
else
{
lean_inc(v_a_4253_);
lean_dec(v___x_4252_);
v___x_4255_ = lean_box(0);
v_isShared_4256_ = v_isSharedCheck_4260_;
goto v_resetjp_4254_;
}
v_resetjp_4254_:
{
lean_object* v___x_4258_; 
if (v_isShared_4256_ == 0)
{
v___x_4258_ = v___x_4255_;
goto v_reusejp_4257_;
}
else
{
lean_object* v_reuseFailAlloc_4259_; 
v_reuseFailAlloc_4259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4259_, 0, v_a_4253_);
v___x_4258_ = v_reuseFailAlloc_4259_;
goto v_reusejp_4257_;
}
v_reusejp_4257_:
{
return v___x_4258_;
}
}
}
}
}
v___jp_4261_:
{
if (lean_obj_tag(v___y_4262_) == 0)
{
lean_object* v_a_4263_; 
v_a_4263_ = lean_ctor_get(v___y_4262_, 0);
lean_inc(v_a_4263_);
lean_dec_ref_known(v___y_4262_, 1);
v_a_4240_ = v_a_4263_;
goto v___jp_4239_;
}
else
{
lean_object* v_a_4264_; lean_object* v___x_4266_; uint8_t v_isShared_4267_; uint8_t v_isSharedCheck_4271_; 
lean_dec_ref(v_reflectionResult_3016_);
lean_dec(v_goal_3015_);
lean_dec_ref(v_ctx_3014_);
v_a_4264_ = lean_ctor_get(v___y_4262_, 0);
v_isSharedCheck_4271_ = !lean_is_exclusive(v___y_4262_);
if (v_isSharedCheck_4271_ == 0)
{
v___x_4266_ = v___y_4262_;
v_isShared_4267_ = v_isSharedCheck_4271_;
goto v_resetjp_4265_;
}
else
{
lean_inc(v_a_4264_);
lean_dec(v___y_4262_);
v___x_4266_ = lean_box(0);
v_isShared_4267_ = v_isSharedCheck_4271_;
goto v_resetjp_4265_;
}
v_resetjp_4265_:
{
lean_object* v___x_4269_; 
if (v_isShared_4267_ == 0)
{
v___x_4269_ = v___x_4266_;
goto v_reusejp_4268_;
}
else
{
lean_object* v_reuseFailAlloc_4270_; 
v_reuseFailAlloc_4270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4270_, 0, v_a_4264_);
v___x_4269_ = v_reuseFailAlloc_4270_;
goto v_reusejp_4268_;
}
v_reusejp_4268_:
{
return v___x_4269_;
}
}
}
}
v___jp_4272_:
{
lean_object* v___x_4276_; double v___x_4277_; double v___x_4278_; double v___x_4279_; double v___x_4280_; double v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; 
v___x_4276_ = lean_io_mono_nanos_now();
v___x_4277_ = lean_float_of_nat(v___y_4273_);
v___x_4278_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4279_ = lean_float_div(v___x_4277_, v___x_4278_);
v___x_4280_ = lean_float_of_nat(v___x_4276_);
v___x_4281_ = lean_float_div(v___x_4280_, v___x_4278_);
v___x_4282_ = lean_box_float(v___x_4279_);
v___x_4283_ = lean_box_float(v___x_4281_);
v___x_4284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4284_, 0, v___x_4282_);
lean_ctor_set(v___x_4284_, 1, v___x_4283_);
v___x_4285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4285_, 0, v_a_4275_);
lean_ctor_set(v___x_4285_, 1, v___x_4284_);
v___x_4286_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v_cls_3541_, v___x_3146_, v___x_3147_, v_options_3138_, v___x_3548_, v___y_4274_, v___f_3545_, v___x_4285_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
v___y_4262_ = v___x_4286_;
goto v___jp_4261_;
}
v___jp_4287_:
{
lean_object* v___x_4291_; double v___x_4292_; double v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; 
v___x_4291_ = lean_io_get_num_heartbeats();
v___x_4292_ = lean_float_of_nat(v___y_4288_);
v___x_4293_ = lean_float_of_nat(v___x_4291_);
v___x_4294_ = lean_box_float(v___x_4292_);
v___x_4295_ = lean_box_float(v___x_4293_);
v___x_4296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4296_, 0, v___x_4294_);
lean_ctor_set(v___x_4296_, 1, v___x_4295_);
v___x_4297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4297_, 0, v_a_4290_);
lean_ctor_set(v___x_4297_, 1, v___x_4296_);
v___x_4298_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v_cls_3541_, v___x_3146_, v___x_3147_, v_options_3138_, v___x_3548_, v___y_4289_, v___f_3545_, v___x_4297_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
v___y_4262_ = v___x_4298_;
goto v___jp_4261_;
}
v___jp_4299_:
{
lean_object* v___x_4300_; lean_object* v_a_4301_; lean_object* v___x_4303_; uint8_t v_isShared_4304_; uint8_t v_isSharedCheck_4355_; 
v___x_4300_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_3021_);
v_a_4301_ = lean_ctor_get(v___x_4300_, 0);
v_isSharedCheck_4355_ = !lean_is_exclusive(v___x_4300_);
if (v_isSharedCheck_4355_ == 0)
{
v___x_4303_ = v___x_4300_;
v_isShared_4304_ = v_isSharedCheck_4355_;
goto v_resetjp_4302_;
}
else
{
lean_inc(v_a_4301_);
lean_dec(v___x_4300_);
v___x_4303_ = lean_box(0);
v_isShared_4304_ = v_isSharedCheck_4355_;
goto v_resetjp_4302_;
}
v_resetjp_4302_:
{
lean_object* v___x_4305_; uint8_t v___x_4306_; 
v___x_4305_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4306_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_3138_, v___x_4305_);
if (v___x_4306_ == 0)
{
lean_object* v___x_4307_; lean_object* v___x_4308_; 
v___x_4307_ = lean_io_mono_nanos_now();
v___x_4308_ = l_IO_lazyPure___redArg(v___f_3145_);
if (lean_obj_tag(v___x_4308_) == 0)
{
lean_object* v_a_4309_; lean_object* v___x_4311_; uint8_t v_isShared_4312_; uint8_t v_isSharedCheck_4316_; 
lean_del_object(v___x_4303_);
v_a_4309_ = lean_ctor_get(v___x_4308_, 0);
v_isSharedCheck_4316_ = !lean_is_exclusive(v___x_4308_);
if (v_isSharedCheck_4316_ == 0)
{
v___x_4311_ = v___x_4308_;
v_isShared_4312_ = v_isSharedCheck_4316_;
goto v_resetjp_4310_;
}
else
{
lean_inc(v_a_4309_);
lean_dec(v___x_4308_);
v___x_4311_ = lean_box(0);
v_isShared_4312_ = v_isSharedCheck_4316_;
goto v_resetjp_4310_;
}
v_resetjp_4310_:
{
lean_object* v___x_4314_; 
if (v_isShared_4312_ == 0)
{
lean_ctor_set_tag(v___x_4311_, 1);
v___x_4314_ = v___x_4311_;
goto v_reusejp_4313_;
}
else
{
lean_object* v_reuseFailAlloc_4315_; 
v_reuseFailAlloc_4315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4315_, 0, v_a_4309_);
v___x_4314_ = v_reuseFailAlloc_4315_;
goto v_reusejp_4313_;
}
v_reusejp_4313_:
{
v___y_4273_ = v___x_4307_;
v___y_4274_ = v_a_4301_;
v_a_4275_ = v___x_4314_;
goto v___jp_4272_;
}
}
}
else
{
lean_object* v_a_4317_; lean_object* v___x_4319_; uint8_t v_isShared_4320_; uint8_t v_isSharedCheck_4330_; 
v_a_4317_ = lean_ctor_get(v___x_4308_, 0);
v_isSharedCheck_4330_ = !lean_is_exclusive(v___x_4308_);
if (v_isSharedCheck_4330_ == 0)
{
v___x_4319_ = v___x_4308_;
v_isShared_4320_ = v_isSharedCheck_4330_;
goto v_resetjp_4318_;
}
else
{
lean_inc(v_a_4317_);
lean_dec(v___x_4308_);
v___x_4319_ = lean_box(0);
v_isShared_4320_ = v_isSharedCheck_4330_;
goto v_resetjp_4318_;
}
v_resetjp_4318_:
{
lean_object* v___x_4321_; lean_object* v___x_4323_; 
v___x_4321_ = lean_io_error_to_string(v_a_4317_);
if (v_isShared_4320_ == 0)
{
lean_ctor_set_tag(v___x_4319_, 3);
lean_ctor_set(v___x_4319_, 0, v___x_4321_);
v___x_4323_ = v___x_4319_;
goto v_reusejp_4322_;
}
else
{
lean_object* v_reuseFailAlloc_4329_; 
v_reuseFailAlloc_4329_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4329_, 0, v___x_4321_);
v___x_4323_ = v_reuseFailAlloc_4329_;
goto v_reusejp_4322_;
}
v_reusejp_4322_:
{
lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4327_; 
v___x_4324_ = l_Lean_MessageData_ofFormat(v___x_4323_);
lean_inc(v_ref_3139_);
v___x_4325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4325_, 0, v_ref_3139_);
lean_ctor_set(v___x_4325_, 1, v___x_4324_);
if (v_isShared_4304_ == 0)
{
lean_ctor_set(v___x_4303_, 0, v___x_4325_);
v___x_4327_ = v___x_4303_;
goto v_reusejp_4326_;
}
else
{
lean_object* v_reuseFailAlloc_4328_; 
v_reuseFailAlloc_4328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4328_, 0, v___x_4325_);
v___x_4327_ = v_reuseFailAlloc_4328_;
goto v_reusejp_4326_;
}
v_reusejp_4326_:
{
v___y_4273_ = v___x_4307_;
v___y_4274_ = v_a_4301_;
v_a_4275_ = v___x_4327_;
goto v___jp_4272_;
}
}
}
}
}
else
{
lean_object* v___x_4331_; lean_object* v___x_4332_; 
v___x_4331_ = lean_io_get_num_heartbeats();
v___x_4332_ = l_IO_lazyPure___redArg(v___f_3145_);
if (lean_obj_tag(v___x_4332_) == 0)
{
lean_object* v_a_4333_; lean_object* v___x_4335_; uint8_t v_isShared_4336_; uint8_t v_isSharedCheck_4340_; 
lean_del_object(v___x_4303_);
v_a_4333_ = lean_ctor_get(v___x_4332_, 0);
v_isSharedCheck_4340_ = !lean_is_exclusive(v___x_4332_);
if (v_isSharedCheck_4340_ == 0)
{
v___x_4335_ = v___x_4332_;
v_isShared_4336_ = v_isSharedCheck_4340_;
goto v_resetjp_4334_;
}
else
{
lean_inc(v_a_4333_);
lean_dec(v___x_4332_);
v___x_4335_ = lean_box(0);
v_isShared_4336_ = v_isSharedCheck_4340_;
goto v_resetjp_4334_;
}
v_resetjp_4334_:
{
lean_object* v___x_4338_; 
if (v_isShared_4336_ == 0)
{
lean_ctor_set_tag(v___x_4335_, 1);
v___x_4338_ = v___x_4335_;
goto v_reusejp_4337_;
}
else
{
lean_object* v_reuseFailAlloc_4339_; 
v_reuseFailAlloc_4339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4339_, 0, v_a_4333_);
v___x_4338_ = v_reuseFailAlloc_4339_;
goto v_reusejp_4337_;
}
v_reusejp_4337_:
{
v___y_4288_ = v___x_4331_;
v___y_4289_ = v_a_4301_;
v_a_4290_ = v___x_4338_;
goto v___jp_4287_;
}
}
}
else
{
lean_object* v_a_4341_; lean_object* v___x_4343_; uint8_t v_isShared_4344_; uint8_t v_isSharedCheck_4354_; 
v_a_4341_ = lean_ctor_get(v___x_4332_, 0);
v_isSharedCheck_4354_ = !lean_is_exclusive(v___x_4332_);
if (v_isSharedCheck_4354_ == 0)
{
v___x_4343_ = v___x_4332_;
v_isShared_4344_ = v_isSharedCheck_4354_;
goto v_resetjp_4342_;
}
else
{
lean_inc(v_a_4341_);
lean_dec(v___x_4332_);
v___x_4343_ = lean_box(0);
v_isShared_4344_ = v_isSharedCheck_4354_;
goto v_resetjp_4342_;
}
v_resetjp_4342_:
{
lean_object* v___x_4345_; lean_object* v___x_4347_; 
v___x_4345_ = lean_io_error_to_string(v_a_4341_);
if (v_isShared_4344_ == 0)
{
lean_ctor_set_tag(v___x_4343_, 3);
lean_ctor_set(v___x_4343_, 0, v___x_4345_);
v___x_4347_ = v___x_4343_;
goto v_reusejp_4346_;
}
else
{
lean_object* v_reuseFailAlloc_4353_; 
v_reuseFailAlloc_4353_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4353_, 0, v___x_4345_);
v___x_4347_ = v_reuseFailAlloc_4353_;
goto v_reusejp_4346_;
}
v_reusejp_4346_:
{
lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4351_; 
v___x_4348_ = l_Lean_MessageData_ofFormat(v___x_4347_);
lean_inc(v_ref_3139_);
v___x_4349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4349_, 0, v_ref_3139_);
lean_ctor_set(v___x_4349_, 1, v___x_4348_);
if (v_isShared_4304_ == 0)
{
lean_ctor_set(v___x_4303_, 0, v___x_4349_);
v___x_4351_ = v___x_4303_;
goto v_reusejp_4350_;
}
else
{
lean_object* v_reuseFailAlloc_4352_; 
v_reuseFailAlloc_4352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4352_, 0, v___x_4349_);
v___x_4351_ = v_reuseFailAlloc_4352_;
goto v_reusejp_4350_;
}
v_reusejp_4350_:
{
v___y_4288_ = v___x_4331_;
v___y_4289_ = v_a_4301_;
v_a_4290_ = v___x_4351_;
goto v___jp_4287_;
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
lean_inc_ref(v_unusedHypotheses_3074_);
goto v___jp_3870_;
}
}
else
{
lean_inc_ref(v_unusedHypotheses_3074_);
goto v___jp_3870_;
}
v___jp_3549_:
{
lean_object* v___x_3553_; double v___x_3554_; double v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; 
v___x_3553_ = lean_io_get_num_heartbeats();
v___x_3554_ = lean_float_of_nat(v___y_3550_);
v___x_3555_ = lean_float_of_nat(v___x_3553_);
v___x_3556_ = lean_box_float(v___x_3554_);
v___x_3557_ = lean_box_float(v___x_3555_);
v___x_3558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3558_, 0, v___x_3556_);
lean_ctor_set(v___x_3558_, 1, v___x_3557_);
v___x_3559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3559_, 0, v_a_3552_);
lean_ctor_set(v___x_3559_, 1, v___x_3558_);
v___x_3560_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(v_cls_3541_, v___x_3146_, v___x_3147_, v_options_3138_, v___x_3548_, v___y_3551_, v___f_3544_, v___x_3559_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
return v___x_3560_;
}
v___jp_3561_:
{
lean_object* v___x_3565_; 
v___x_3565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3565_, 0, v_a_3564_);
v___y_3550_ = v___y_3562_;
v___y_3551_ = v___y_3563_;
v_a_3552_ = v___x_3565_;
goto v___jp_3549_;
}
v___jp_3566_:
{
if (lean_obj_tag(v___y_3569_) == 0)
{
lean_object* v_a_3570_; lean_object* v___x_3572_; uint8_t v_isShared_3573_; uint8_t v_isSharedCheck_3577_; 
v_a_3570_ = lean_ctor_get(v___y_3569_, 0);
v_isSharedCheck_3577_ = !lean_is_exclusive(v___y_3569_);
if (v_isSharedCheck_3577_ == 0)
{
v___x_3572_ = v___y_3569_;
v_isShared_3573_ = v_isSharedCheck_3577_;
goto v_resetjp_3571_;
}
else
{
lean_inc(v_a_3570_);
lean_dec(v___y_3569_);
v___x_3572_ = lean_box(0);
v_isShared_3573_ = v_isSharedCheck_3577_;
goto v_resetjp_3571_;
}
v_resetjp_3571_:
{
lean_object* v___x_3575_; 
if (v_isShared_3573_ == 0)
{
lean_ctor_set_tag(v___x_3572_, 1);
v___x_3575_ = v___x_3572_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v_a_3570_);
v___x_3575_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
v___y_3550_ = v___y_3567_;
v___y_3551_ = v___y_3568_;
v_a_3552_ = v___x_3575_;
goto v___jp_3549_;
}
}
}
else
{
lean_object* v_a_3578_; 
v_a_3578_ = lean_ctor_get(v___y_3569_, 0);
lean_inc(v_a_3578_);
lean_dec_ref_known(v___y_3569_, 1);
v___y_3562_ = v___y_3567_;
v___y_3563_ = v___y_3568_;
v_a_3564_ = v_a_3578_;
goto v___jp_3561_;
}
}
v___jp_3579_:
{
lean_object* v_aig_3584_; lean_object* v_decls_3585_; lean_object* v___f_3586_; 
v_aig_3584_ = lean_ctor_get(v_a_3583_, 0);
lean_inc_ref(v_aig_3584_);
v_decls_3585_ = lean_ctor_get(v_aig_3584_, 0);
lean_inc_ref(v_a_3583_);
v___f_3586_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3___boxed), 3, 2);
lean_closure_set(v___f_3586_, 0, v___x_3142_);
lean_closure_set(v___f_3586_, 1, v_a_3583_);
if (v___x_3548_ == 0)
{
lean_object* v___x_3587_; lean_object* v___x_3588_; 
v___x_3587_ = lean_box(0);
v___x_3588_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(v_ctx_3014_, v_aig_3584_, v_atomsAssignment_3017_, v_goal_3015_, v_unusedHypotheses_3074_, v_reflectionResult_3016_, v___x_3146_, v___x_3147_, v___f_3543_, v___y_3580_, v___f_3542_, v___f_3586_, v___x_3143_, v___x_3144_, v_a_3583_, v___x_3587_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
v___y_3567_ = v___y_3581_;
v___y_3568_ = v___y_3582_;
v___y_3569_ = v___x_3588_;
goto v___jp_3566_;
}
else
{
lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; 
v___x_3589_ = lean_array_get_size(v_decls_3585_);
v___x_3590_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8));
v___x_3591_ = l_Nat_reprFast(v___x_3589_);
v___x_3592_ = lean_string_append(v___x_3590_, v___x_3591_);
lean_dec_ref(v___x_3591_);
v___x_3593_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__9));
v___x_3594_ = lean_string_append(v___x_3592_, v___x_3593_);
v___x_3595_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3595_, 0, v___x_3594_);
v___x_3596_ = l_Lean_MessageData_ofFormat(v___x_3595_);
v___x_3597_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v_cls_3541_, v___x_3596_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
if (lean_obj_tag(v___x_3597_) == 0)
{
lean_object* v_a_3598_; lean_object* v___x_3599_; 
v_a_3598_ = lean_ctor_get(v___x_3597_, 0);
lean_inc(v_a_3598_);
lean_dec_ref_known(v___x_3597_, 1);
v___x_3599_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(v_ctx_3014_, v_aig_3584_, v_atomsAssignment_3017_, v_goal_3015_, v_unusedHypotheses_3074_, v_reflectionResult_3016_, v___x_3146_, v___x_3147_, v___f_3543_, v___y_3580_, v___f_3542_, v___f_3586_, v___x_3143_, v___x_3144_, v_a_3583_, v_a_3598_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
v___y_3567_ = v___y_3581_;
v___y_3568_ = v___y_3582_;
v___y_3569_ = v___x_3599_;
goto v___jp_3566_;
}
else
{
lean_object* v_a_3600_; 
lean_dec_ref(v___f_3586_);
lean_dec_ref(v_aig_3584_);
lean_dec_ref(v_a_3583_);
lean_dec_ref(v_unusedHypotheses_3074_);
lean_dec_ref(v_reflectionResult_3016_);
lean_dec(v_goal_3015_);
lean_dec_ref(v_ctx_3014_);
v_a_3600_ = lean_ctor_get(v___x_3597_, 0);
lean_inc(v_a_3600_);
lean_dec_ref_known(v___x_3597_, 1);
v___y_3562_ = v___y_3581_;
v___y_3563_ = v___y_3582_;
v_a_3564_ = v_a_3600_;
goto v___jp_3561_;
}
}
}
v___jp_3601_:
{
if (lean_obj_tag(v___y_3605_) == 0)
{
lean_object* v_a_3606_; 
v_a_3606_ = lean_ctor_get(v___y_3605_, 0);
lean_inc(v_a_3606_);
lean_dec_ref_known(v___y_3605_, 1);
v___y_3580_ = v___y_3602_;
v___y_3581_ = v___y_3603_;
v___y_3582_ = v___y_3604_;
v_a_3583_ = v_a_3606_;
goto v___jp_3579_;
}
else
{
lean_object* v_a_3607_; 
lean_dec_ref(v_unusedHypotheses_3074_);
lean_dec_ref(v_reflectionResult_3016_);
lean_dec(v_goal_3015_);
lean_dec_ref(v_ctx_3014_);
v_a_3607_ = lean_ctor_get(v___y_3605_, 0);
lean_inc(v_a_3607_);
lean_dec_ref_known(v___y_3605_, 1);
v___y_3562_ = v___y_3603_;
v___y_3563_ = v___y_3604_;
v_a_3564_ = v_a_3607_;
goto v___jp_3561_;
}
}
v___jp_3608_:
{
lean_object* v___x_3616_; double v___x_3617_; double v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; 
v___x_3616_ = lean_io_get_num_heartbeats();
v___x_3617_ = lean_float_of_nat(v___y_3612_);
v___x_3618_ = lean_float_of_nat(v___x_3616_);
v___x_3619_ = lean_box_float(v___x_3617_);
v___x_3620_ = lean_box_float(v___x_3618_);
v___x_3621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3621_, 0, v___x_3619_);
lean_ctor_set(v___x_3621_, 1, v___x_3620_);
v___x_3622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3622_, 0, v_a_3615_);
lean_ctor_set(v___x_3622_, 1, v___x_3621_);
v___x_3623_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v_cls_3541_, v___x_3146_, v___x_3147_, v_options_3138_, v___y_3614_, v___y_3611_, v___f_3545_, v___x_3622_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
v___y_3602_ = v___y_3609_;
v___y_3603_ = v___y_3610_;
v___y_3604_ = v___y_3613_;
v___y_3605_ = v___x_3623_;
goto v___jp_3601_;
}
v___jp_3624_:
{
lean_object* v___x_3632_; double v___x_3633_; double v___x_3634_; double v___x_3635_; double v___x_3636_; double v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; 
v___x_3632_ = lean_io_mono_nanos_now();
v___x_3633_ = lean_float_of_nat(v___y_3628_);
v___x_3634_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3635_ = lean_float_div(v___x_3633_, v___x_3634_);
v___x_3636_ = lean_float_of_nat(v___x_3632_);
v___x_3637_ = lean_float_div(v___x_3636_, v___x_3634_);
v___x_3638_ = lean_box_float(v___x_3635_);
v___x_3639_ = lean_box_float(v___x_3637_);
v___x_3640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3640_, 0, v___x_3638_);
lean_ctor_set(v___x_3640_, 1, v___x_3639_);
v___x_3641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3641_, 0, v_a_3631_);
lean_ctor_set(v___x_3641_, 1, v___x_3640_);
v___x_3642_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v_cls_3541_, v___x_3146_, v___x_3147_, v_options_3138_, v___y_3630_, v___y_3627_, v___f_3545_, v___x_3641_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
v___y_3602_ = v___y_3625_;
v___y_3603_ = v___y_3626_;
v___y_3604_ = v___y_3629_;
v___y_3605_ = v___x_3642_;
goto v___jp_3601_;
}
v___jp_3643_:
{
lean_object* v___x_3649_; 
v___x_3649_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_3021_);
if (v___y_3647_ == 0)
{
lean_object* v_a_3650_; lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3678_; 
v_a_3650_ = lean_ctor_get(v___x_3649_, 0);
v_isSharedCheck_3678_ = !lean_is_exclusive(v___x_3649_);
if (v_isSharedCheck_3678_ == 0)
{
v___x_3652_ = v___x_3649_;
v_isShared_3653_ = v_isSharedCheck_3678_;
goto v_resetjp_3651_;
}
else
{
lean_inc(v_a_3650_);
lean_dec(v___x_3649_);
v___x_3652_ = lean_box(0);
v_isShared_3653_ = v_isSharedCheck_3678_;
goto v_resetjp_3651_;
}
v_resetjp_3651_:
{
lean_object* v___x_3654_; lean_object* v___x_3655_; 
v___x_3654_ = lean_io_mono_nanos_now();
v___x_3655_ = l_IO_lazyPure___redArg(v___f_3145_);
if (lean_obj_tag(v___x_3655_) == 0)
{
lean_object* v_a_3656_; lean_object* v___x_3658_; uint8_t v_isShared_3659_; uint8_t v_isSharedCheck_3663_; 
lean_del_object(v___x_3652_);
v_a_3656_ = lean_ctor_get(v___x_3655_, 0);
v_isSharedCheck_3663_ = !lean_is_exclusive(v___x_3655_);
if (v_isSharedCheck_3663_ == 0)
{
v___x_3658_ = v___x_3655_;
v_isShared_3659_ = v_isSharedCheck_3663_;
goto v_resetjp_3657_;
}
else
{
lean_inc(v_a_3656_);
lean_dec(v___x_3655_);
v___x_3658_ = lean_box(0);
v_isShared_3659_ = v_isSharedCheck_3663_;
goto v_resetjp_3657_;
}
v_resetjp_3657_:
{
lean_object* v___x_3661_; 
if (v_isShared_3659_ == 0)
{
lean_ctor_set_tag(v___x_3658_, 1);
v___x_3661_ = v___x_3658_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v_a_3656_);
v___x_3661_ = v_reuseFailAlloc_3662_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
v___y_3625_ = v___y_3644_;
v___y_3626_ = v___y_3645_;
v___y_3627_ = v_a_3650_;
v___y_3628_ = v___x_3654_;
v___y_3629_ = v___y_3646_;
v___y_3630_ = v___y_3648_;
v_a_3631_ = v___x_3661_;
goto v___jp_3624_;
}
}
}
else
{
lean_object* v_a_3664_; lean_object* v___x_3666_; uint8_t v_isShared_3667_; uint8_t v_isSharedCheck_3677_; 
v_a_3664_ = lean_ctor_get(v___x_3655_, 0);
v_isSharedCheck_3677_ = !lean_is_exclusive(v___x_3655_);
if (v_isSharedCheck_3677_ == 0)
{
v___x_3666_ = v___x_3655_;
v_isShared_3667_ = v_isSharedCheck_3677_;
goto v_resetjp_3665_;
}
else
{
lean_inc(v_a_3664_);
lean_dec(v___x_3655_);
v___x_3666_ = lean_box(0);
v_isShared_3667_ = v_isSharedCheck_3677_;
goto v_resetjp_3665_;
}
v_resetjp_3665_:
{
lean_object* v___x_3668_; lean_object* v___x_3670_; 
v___x_3668_ = lean_io_error_to_string(v_a_3664_);
if (v_isShared_3667_ == 0)
{
lean_ctor_set_tag(v___x_3666_, 3);
lean_ctor_set(v___x_3666_, 0, v___x_3668_);
v___x_3670_ = v___x_3666_;
goto v_reusejp_3669_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v___x_3668_);
v___x_3670_ = v_reuseFailAlloc_3676_;
goto v_reusejp_3669_;
}
v_reusejp_3669_:
{
lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3674_; 
v___x_3671_ = l_Lean_MessageData_ofFormat(v___x_3670_);
lean_inc(v_ref_3139_);
v___x_3672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3672_, 0, v_ref_3139_);
lean_ctor_set(v___x_3672_, 1, v___x_3671_);
if (v_isShared_3653_ == 0)
{
lean_ctor_set(v___x_3652_, 0, v___x_3672_);
v___x_3674_ = v___x_3652_;
goto v_reusejp_3673_;
}
else
{
lean_object* v_reuseFailAlloc_3675_; 
v_reuseFailAlloc_3675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3675_, 0, v___x_3672_);
v___x_3674_ = v_reuseFailAlloc_3675_;
goto v_reusejp_3673_;
}
v_reusejp_3673_:
{
v___y_3625_ = v___y_3644_;
v___y_3626_ = v___y_3645_;
v___y_3627_ = v_a_3650_;
v___y_3628_ = v___x_3654_;
v___y_3629_ = v___y_3646_;
v___y_3630_ = v___y_3648_;
v_a_3631_ = v___x_3674_;
goto v___jp_3624_;
}
}
}
}
}
}
else
{
lean_object* v_a_3679_; lean_object* v___x_3681_; uint8_t v_isShared_3682_; uint8_t v_isSharedCheck_3707_; 
v_a_3679_ = lean_ctor_get(v___x_3649_, 0);
v_isSharedCheck_3707_ = !lean_is_exclusive(v___x_3649_);
if (v_isSharedCheck_3707_ == 0)
{
v___x_3681_ = v___x_3649_;
v_isShared_3682_ = v_isSharedCheck_3707_;
goto v_resetjp_3680_;
}
else
{
lean_inc(v_a_3679_);
lean_dec(v___x_3649_);
v___x_3681_ = lean_box(0);
v_isShared_3682_ = v_isSharedCheck_3707_;
goto v_resetjp_3680_;
}
v_resetjp_3680_:
{
lean_object* v___x_3683_; lean_object* v___x_3684_; 
v___x_3683_ = lean_io_get_num_heartbeats();
v___x_3684_ = l_IO_lazyPure___redArg(v___f_3145_);
if (lean_obj_tag(v___x_3684_) == 0)
{
lean_object* v_a_3685_; lean_object* v___x_3687_; uint8_t v_isShared_3688_; uint8_t v_isSharedCheck_3692_; 
lean_del_object(v___x_3681_);
v_a_3685_ = lean_ctor_get(v___x_3684_, 0);
v_isSharedCheck_3692_ = !lean_is_exclusive(v___x_3684_);
if (v_isSharedCheck_3692_ == 0)
{
v___x_3687_ = v___x_3684_;
v_isShared_3688_ = v_isSharedCheck_3692_;
goto v_resetjp_3686_;
}
else
{
lean_inc(v_a_3685_);
lean_dec(v___x_3684_);
v___x_3687_ = lean_box(0);
v_isShared_3688_ = v_isSharedCheck_3692_;
goto v_resetjp_3686_;
}
v_resetjp_3686_:
{
lean_object* v___x_3690_; 
if (v_isShared_3688_ == 0)
{
lean_ctor_set_tag(v___x_3687_, 1);
v___x_3690_ = v___x_3687_;
goto v_reusejp_3689_;
}
else
{
lean_object* v_reuseFailAlloc_3691_; 
v_reuseFailAlloc_3691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3691_, 0, v_a_3685_);
v___x_3690_ = v_reuseFailAlloc_3691_;
goto v_reusejp_3689_;
}
v_reusejp_3689_:
{
v___y_3609_ = v___y_3644_;
v___y_3610_ = v___y_3645_;
v___y_3611_ = v_a_3679_;
v___y_3612_ = v___x_3683_;
v___y_3613_ = v___y_3646_;
v___y_3614_ = v___y_3648_;
v_a_3615_ = v___x_3690_;
goto v___jp_3608_;
}
}
}
else
{
lean_object* v_a_3693_; lean_object* v___x_3695_; uint8_t v_isShared_3696_; uint8_t v_isSharedCheck_3706_; 
v_a_3693_ = lean_ctor_get(v___x_3684_, 0);
v_isSharedCheck_3706_ = !lean_is_exclusive(v___x_3684_);
if (v_isSharedCheck_3706_ == 0)
{
v___x_3695_ = v___x_3684_;
v_isShared_3696_ = v_isSharedCheck_3706_;
goto v_resetjp_3694_;
}
else
{
lean_inc(v_a_3693_);
lean_dec(v___x_3684_);
v___x_3695_ = lean_box(0);
v_isShared_3696_ = v_isSharedCheck_3706_;
goto v_resetjp_3694_;
}
v_resetjp_3694_:
{
lean_object* v___x_3697_; lean_object* v___x_3699_; 
v___x_3697_ = lean_io_error_to_string(v_a_3693_);
if (v_isShared_3696_ == 0)
{
lean_ctor_set_tag(v___x_3695_, 3);
lean_ctor_set(v___x_3695_, 0, v___x_3697_);
v___x_3699_ = v___x_3695_;
goto v_reusejp_3698_;
}
else
{
lean_object* v_reuseFailAlloc_3705_; 
v_reuseFailAlloc_3705_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3705_, 0, v___x_3697_);
v___x_3699_ = v_reuseFailAlloc_3705_;
goto v_reusejp_3698_;
}
v_reusejp_3698_:
{
lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3703_; 
v___x_3700_ = l_Lean_MessageData_ofFormat(v___x_3699_);
lean_inc(v_ref_3139_);
v___x_3701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3701_, 0, v_ref_3139_);
lean_ctor_set(v___x_3701_, 1, v___x_3700_);
if (v_isShared_3682_ == 0)
{
lean_ctor_set(v___x_3681_, 0, v___x_3701_);
v___x_3703_ = v___x_3681_;
goto v_reusejp_3702_;
}
else
{
lean_object* v_reuseFailAlloc_3704_; 
v_reuseFailAlloc_3704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3704_, 0, v___x_3701_);
v___x_3703_ = v_reuseFailAlloc_3704_;
goto v_reusejp_3702_;
}
v_reusejp_3702_:
{
v___y_3609_ = v___y_3644_;
v___y_3610_ = v___y_3645_;
v___y_3611_ = v_a_3679_;
v___y_3612_ = v___x_3683_;
v___y_3613_ = v___y_3646_;
v___y_3614_ = v___y_3648_;
v_a_3615_ = v___x_3703_;
goto v___jp_3608_;
}
}
}
}
}
}
}
v___jp_3708_:
{
lean_object* v___x_3712_; double v___x_3713_; double v___x_3714_; double v___x_3715_; double v___x_3716_; double v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; 
v___x_3712_ = lean_io_mono_nanos_now();
v___x_3713_ = lean_float_of_nat(v___y_3709_);
v___x_3714_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3715_ = lean_float_div(v___x_3713_, v___x_3714_);
v___x_3716_ = lean_float_of_nat(v___x_3712_);
v___x_3717_ = lean_float_div(v___x_3716_, v___x_3714_);
v___x_3718_ = lean_box_float(v___x_3715_);
v___x_3719_ = lean_box_float(v___x_3717_);
v___x_3720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3720_, 0, v___x_3718_);
lean_ctor_set(v___x_3720_, 1, v___x_3719_);
v___x_3721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3721_, 0, v_a_3711_);
lean_ctor_set(v___x_3721_, 1, v___x_3720_);
v___x_3722_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(v_cls_3541_, v___x_3146_, v___x_3147_, v_options_3138_, v___x_3548_, v___y_3710_, v___f_3544_, v___x_3721_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
return v___x_3722_;
}
v___jp_3723_:
{
lean_object* v___x_3727_; 
v___x_3727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3727_, 0, v_a_3726_);
v___y_3709_ = v___y_3724_;
v___y_3710_ = v___y_3725_;
v_a_3711_ = v___x_3727_;
goto v___jp_3708_;
}
v___jp_3728_:
{
if (lean_obj_tag(v___y_3731_) == 0)
{
lean_object* v_a_3732_; lean_object* v___x_3734_; uint8_t v_isShared_3735_; uint8_t v_isSharedCheck_3739_; 
v_a_3732_ = lean_ctor_get(v___y_3731_, 0);
v_isSharedCheck_3739_ = !lean_is_exclusive(v___y_3731_);
if (v_isSharedCheck_3739_ == 0)
{
v___x_3734_ = v___y_3731_;
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
else
{
lean_inc(v_a_3732_);
lean_dec(v___y_3731_);
v___x_3734_ = lean_box(0);
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
v_resetjp_3733_:
{
lean_object* v___x_3737_; 
if (v_isShared_3735_ == 0)
{
lean_ctor_set_tag(v___x_3734_, 1);
v___x_3737_ = v___x_3734_;
goto v_reusejp_3736_;
}
else
{
lean_object* v_reuseFailAlloc_3738_; 
v_reuseFailAlloc_3738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3738_, 0, v_a_3732_);
v___x_3737_ = v_reuseFailAlloc_3738_;
goto v_reusejp_3736_;
}
v_reusejp_3736_:
{
v___y_3709_ = v___y_3729_;
v___y_3710_ = v___y_3730_;
v_a_3711_ = v___x_3737_;
goto v___jp_3708_;
}
}
}
else
{
lean_object* v_a_3740_; 
v_a_3740_ = lean_ctor_get(v___y_3731_, 0);
lean_inc(v_a_3740_);
lean_dec_ref_known(v___y_3731_, 1);
v___y_3724_ = v___y_3729_;
v___y_3725_ = v___y_3730_;
v_a_3726_ = v_a_3740_;
goto v___jp_3723_;
}
}
v___jp_3741_:
{
lean_object* v_aig_3746_; lean_object* v_decls_3747_; lean_object* v___f_3748_; 
v_aig_3746_ = lean_ctor_get(v_a_3745_, 0);
lean_inc_ref(v_aig_3746_);
v_decls_3747_ = lean_ctor_get(v_aig_3746_, 0);
lean_inc_ref(v_a_3745_);
v___f_3748_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3___boxed), 3, 2);
lean_closure_set(v___f_3748_, 0, v___x_3142_);
lean_closure_set(v___f_3748_, 1, v_a_3745_);
if (v___x_3548_ == 0)
{
lean_object* v___x_3749_; lean_object* v___x_3750_; 
v___x_3749_ = lean_box(0);
v___x_3750_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6(v_ctx_3014_, v_aig_3746_, v_atomsAssignment_3017_, v_goal_3015_, v_unusedHypotheses_3074_, v_reflectionResult_3016_, v___x_3146_, v___x_3147_, v___f_3543_, v___y_3742_, v___f_3542_, v___f_3748_, v___x_3143_, v___x_3144_, v_a_3745_, v___x_3749_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
v___y_3729_ = v___y_3743_;
v___y_3730_ = v___y_3744_;
v___y_3731_ = v___x_3750_;
goto v___jp_3728_;
}
else
{
lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; 
v___x_3751_ = lean_array_get_size(v_decls_3747_);
v___x_3752_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8));
v___x_3753_ = l_Nat_reprFast(v___x_3751_);
v___x_3754_ = lean_string_append(v___x_3752_, v___x_3753_);
lean_dec_ref(v___x_3753_);
v___x_3755_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__9));
v___x_3756_ = lean_string_append(v___x_3754_, v___x_3755_);
v___x_3757_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3757_, 0, v___x_3756_);
v___x_3758_ = l_Lean_MessageData_ofFormat(v___x_3757_);
v___x_3759_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v_cls_3541_, v___x_3758_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
if (lean_obj_tag(v___x_3759_) == 0)
{
lean_object* v_a_3760_; lean_object* v___x_3761_; 
v_a_3760_ = lean_ctor_get(v___x_3759_, 0);
lean_inc(v_a_3760_);
lean_dec_ref_known(v___x_3759_, 1);
v___x_3761_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6(v_ctx_3014_, v_aig_3746_, v_atomsAssignment_3017_, v_goal_3015_, v_unusedHypotheses_3074_, v_reflectionResult_3016_, v___x_3146_, v___x_3147_, v___f_3543_, v___y_3742_, v___f_3542_, v___f_3748_, v___x_3143_, v___x_3144_, v_a_3745_, v_a_3760_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
v___y_3729_ = v___y_3743_;
v___y_3730_ = v___y_3744_;
v___y_3731_ = v___x_3761_;
goto v___jp_3728_;
}
else
{
lean_object* v_a_3762_; 
lean_dec_ref(v___f_3748_);
lean_dec_ref(v_aig_3746_);
lean_dec_ref(v_a_3745_);
lean_dec_ref(v_unusedHypotheses_3074_);
lean_dec_ref(v_reflectionResult_3016_);
lean_dec(v_goal_3015_);
lean_dec_ref(v_ctx_3014_);
v_a_3762_ = lean_ctor_get(v___x_3759_, 0);
lean_inc(v_a_3762_);
lean_dec_ref_known(v___x_3759_, 1);
v___y_3724_ = v___y_3743_;
v___y_3725_ = v___y_3744_;
v_a_3726_ = v_a_3762_;
goto v___jp_3723_;
}
}
}
v___jp_3763_:
{
if (lean_obj_tag(v___y_3767_) == 0)
{
lean_object* v_a_3768_; 
v_a_3768_ = lean_ctor_get(v___y_3767_, 0);
lean_inc(v_a_3768_);
lean_dec_ref_known(v___y_3767_, 1);
v___y_3742_ = v___y_3764_;
v___y_3743_ = v___y_3765_;
v___y_3744_ = v___y_3766_;
v_a_3745_ = v_a_3768_;
goto v___jp_3741_;
}
else
{
lean_object* v_a_3769_; 
lean_dec_ref(v_unusedHypotheses_3074_);
lean_dec_ref(v_reflectionResult_3016_);
lean_dec(v_goal_3015_);
lean_dec_ref(v_ctx_3014_);
v_a_3769_ = lean_ctor_get(v___y_3767_, 0);
lean_inc(v_a_3769_);
lean_dec_ref_known(v___y_3767_, 1);
v___y_3724_ = v___y_3765_;
v___y_3725_ = v___y_3766_;
v_a_3726_ = v_a_3769_;
goto v___jp_3723_;
}
}
v___jp_3770_:
{
lean_object* v___x_3778_; double v___x_3779_; double v___x_3780_; double v___x_3781_; double v___x_3782_; double v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; 
v___x_3778_ = lean_io_mono_nanos_now();
v___x_3779_ = lean_float_of_nat(v___y_3775_);
v___x_3780_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3781_ = lean_float_div(v___x_3779_, v___x_3780_);
v___x_3782_ = lean_float_of_nat(v___x_3778_);
v___x_3783_ = lean_float_div(v___x_3782_, v___x_3780_);
v___x_3784_ = lean_box_float(v___x_3781_);
v___x_3785_ = lean_box_float(v___x_3783_);
v___x_3786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3786_, 0, v___x_3784_);
lean_ctor_set(v___x_3786_, 1, v___x_3785_);
v___x_3787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3787_, 0, v_a_3777_);
lean_ctor_set(v___x_3787_, 1, v___x_3786_);
v___x_3788_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v_cls_3541_, v___x_3146_, v___x_3147_, v_options_3138_, v___y_3774_, v___y_3773_, v___f_3545_, v___x_3787_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
v___y_3764_ = v___y_3771_;
v___y_3765_ = v___y_3772_;
v___y_3766_ = v___y_3776_;
v___y_3767_ = v___x_3788_;
goto v___jp_3763_;
}
v___jp_3789_:
{
lean_object* v___x_3797_; double v___x_3798_; double v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; 
v___x_3797_ = lean_io_get_num_heartbeats();
v___x_3798_ = lean_float_of_nat(v___y_3791_);
v___x_3799_ = lean_float_of_nat(v___x_3797_);
v___x_3800_ = lean_box_float(v___x_3798_);
v___x_3801_ = lean_box_float(v___x_3799_);
v___x_3802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3802_, 0, v___x_3800_);
lean_ctor_set(v___x_3802_, 1, v___x_3801_);
v___x_3803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3803_, 0, v_a_3796_);
lean_ctor_set(v___x_3803_, 1, v___x_3802_);
v___x_3804_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v_cls_3541_, v___x_3146_, v___x_3147_, v_options_3138_, v___y_3794_, v___y_3793_, v___f_3545_, v___x_3803_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
v___y_3764_ = v___y_3790_;
v___y_3765_ = v___y_3792_;
v___y_3766_ = v___y_3795_;
v___y_3767_ = v___x_3804_;
goto v___jp_3763_;
}
v___jp_3805_:
{
lean_object* v___x_3811_; 
v___x_3811_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_3021_);
if (v___y_3810_ == 0)
{
lean_object* v_a_3812_; lean_object* v___x_3814_; uint8_t v_isShared_3815_; uint8_t v_isSharedCheck_3840_; 
v_a_3812_ = lean_ctor_get(v___x_3811_, 0);
v_isSharedCheck_3840_ = !lean_is_exclusive(v___x_3811_);
if (v_isSharedCheck_3840_ == 0)
{
v___x_3814_ = v___x_3811_;
v_isShared_3815_ = v_isSharedCheck_3840_;
goto v_resetjp_3813_;
}
else
{
lean_inc(v_a_3812_);
lean_dec(v___x_3811_);
v___x_3814_ = lean_box(0);
v_isShared_3815_ = v_isSharedCheck_3840_;
goto v_resetjp_3813_;
}
v_resetjp_3813_:
{
lean_object* v___x_3816_; lean_object* v___x_3817_; 
v___x_3816_ = lean_io_mono_nanos_now();
v___x_3817_ = l_IO_lazyPure___redArg(v___f_3145_);
if (lean_obj_tag(v___x_3817_) == 0)
{
lean_object* v_a_3818_; lean_object* v___x_3820_; uint8_t v_isShared_3821_; uint8_t v_isSharedCheck_3825_; 
lean_del_object(v___x_3814_);
v_a_3818_ = lean_ctor_get(v___x_3817_, 0);
v_isSharedCheck_3825_ = !lean_is_exclusive(v___x_3817_);
if (v_isSharedCheck_3825_ == 0)
{
v___x_3820_ = v___x_3817_;
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
else
{
lean_inc(v_a_3818_);
lean_dec(v___x_3817_);
v___x_3820_ = lean_box(0);
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
v_resetjp_3819_:
{
lean_object* v___x_3823_; 
if (v_isShared_3821_ == 0)
{
lean_ctor_set_tag(v___x_3820_, 1);
v___x_3823_ = v___x_3820_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3824_; 
v_reuseFailAlloc_3824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3824_, 0, v_a_3818_);
v___x_3823_ = v_reuseFailAlloc_3824_;
goto v_reusejp_3822_;
}
v_reusejp_3822_:
{
v___y_3771_ = v___y_3806_;
v___y_3772_ = v___y_3807_;
v___y_3773_ = v_a_3812_;
v___y_3774_ = v___y_3808_;
v___y_3775_ = v___x_3816_;
v___y_3776_ = v___y_3809_;
v_a_3777_ = v___x_3823_;
goto v___jp_3770_;
}
}
}
else
{
lean_object* v_a_3826_; lean_object* v___x_3828_; uint8_t v_isShared_3829_; uint8_t v_isSharedCheck_3839_; 
v_a_3826_ = lean_ctor_get(v___x_3817_, 0);
v_isSharedCheck_3839_ = !lean_is_exclusive(v___x_3817_);
if (v_isSharedCheck_3839_ == 0)
{
v___x_3828_ = v___x_3817_;
v_isShared_3829_ = v_isSharedCheck_3839_;
goto v_resetjp_3827_;
}
else
{
lean_inc(v_a_3826_);
lean_dec(v___x_3817_);
v___x_3828_ = lean_box(0);
v_isShared_3829_ = v_isSharedCheck_3839_;
goto v_resetjp_3827_;
}
v_resetjp_3827_:
{
lean_object* v___x_3830_; lean_object* v___x_3832_; 
v___x_3830_ = lean_io_error_to_string(v_a_3826_);
if (v_isShared_3829_ == 0)
{
lean_ctor_set_tag(v___x_3828_, 3);
lean_ctor_set(v___x_3828_, 0, v___x_3830_);
v___x_3832_ = v___x_3828_;
goto v_reusejp_3831_;
}
else
{
lean_object* v_reuseFailAlloc_3838_; 
v_reuseFailAlloc_3838_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3838_, 0, v___x_3830_);
v___x_3832_ = v_reuseFailAlloc_3838_;
goto v_reusejp_3831_;
}
v_reusejp_3831_:
{
lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3836_; 
v___x_3833_ = l_Lean_MessageData_ofFormat(v___x_3832_);
lean_inc(v_ref_3139_);
v___x_3834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3834_, 0, v_ref_3139_);
lean_ctor_set(v___x_3834_, 1, v___x_3833_);
if (v_isShared_3815_ == 0)
{
lean_ctor_set(v___x_3814_, 0, v___x_3834_);
v___x_3836_ = v___x_3814_;
goto v_reusejp_3835_;
}
else
{
lean_object* v_reuseFailAlloc_3837_; 
v_reuseFailAlloc_3837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3837_, 0, v___x_3834_);
v___x_3836_ = v_reuseFailAlloc_3837_;
goto v_reusejp_3835_;
}
v_reusejp_3835_:
{
v___y_3771_ = v___y_3806_;
v___y_3772_ = v___y_3807_;
v___y_3773_ = v_a_3812_;
v___y_3774_ = v___y_3808_;
v___y_3775_ = v___x_3816_;
v___y_3776_ = v___y_3809_;
v_a_3777_ = v___x_3836_;
goto v___jp_3770_;
}
}
}
}
}
}
else
{
lean_object* v_a_3841_; lean_object* v___x_3843_; uint8_t v_isShared_3844_; uint8_t v_isSharedCheck_3869_; 
v_a_3841_ = lean_ctor_get(v___x_3811_, 0);
v_isSharedCheck_3869_ = !lean_is_exclusive(v___x_3811_);
if (v_isSharedCheck_3869_ == 0)
{
v___x_3843_ = v___x_3811_;
v_isShared_3844_ = v_isSharedCheck_3869_;
goto v_resetjp_3842_;
}
else
{
lean_inc(v_a_3841_);
lean_dec(v___x_3811_);
v___x_3843_ = lean_box(0);
v_isShared_3844_ = v_isSharedCheck_3869_;
goto v_resetjp_3842_;
}
v_resetjp_3842_:
{
lean_object* v___x_3845_; lean_object* v___x_3846_; 
v___x_3845_ = lean_io_get_num_heartbeats();
v___x_3846_ = l_IO_lazyPure___redArg(v___f_3145_);
if (lean_obj_tag(v___x_3846_) == 0)
{
lean_object* v_a_3847_; lean_object* v___x_3849_; uint8_t v_isShared_3850_; uint8_t v_isSharedCheck_3854_; 
lean_del_object(v___x_3843_);
v_a_3847_ = lean_ctor_get(v___x_3846_, 0);
v_isSharedCheck_3854_ = !lean_is_exclusive(v___x_3846_);
if (v_isSharedCheck_3854_ == 0)
{
v___x_3849_ = v___x_3846_;
v_isShared_3850_ = v_isSharedCheck_3854_;
goto v_resetjp_3848_;
}
else
{
lean_inc(v_a_3847_);
lean_dec(v___x_3846_);
v___x_3849_ = lean_box(0);
v_isShared_3850_ = v_isSharedCheck_3854_;
goto v_resetjp_3848_;
}
v_resetjp_3848_:
{
lean_object* v___x_3852_; 
if (v_isShared_3850_ == 0)
{
lean_ctor_set_tag(v___x_3849_, 1);
v___x_3852_ = v___x_3849_;
goto v_reusejp_3851_;
}
else
{
lean_object* v_reuseFailAlloc_3853_; 
v_reuseFailAlloc_3853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3853_, 0, v_a_3847_);
v___x_3852_ = v_reuseFailAlloc_3853_;
goto v_reusejp_3851_;
}
v_reusejp_3851_:
{
v___y_3790_ = v___y_3806_;
v___y_3791_ = v___x_3845_;
v___y_3792_ = v___y_3807_;
v___y_3793_ = v_a_3841_;
v___y_3794_ = v___y_3808_;
v___y_3795_ = v___y_3809_;
v_a_3796_ = v___x_3852_;
goto v___jp_3789_;
}
}
}
else
{
lean_object* v_a_3855_; lean_object* v___x_3857_; uint8_t v_isShared_3858_; uint8_t v_isSharedCheck_3868_; 
v_a_3855_ = lean_ctor_get(v___x_3846_, 0);
v_isSharedCheck_3868_ = !lean_is_exclusive(v___x_3846_);
if (v_isSharedCheck_3868_ == 0)
{
v___x_3857_ = v___x_3846_;
v_isShared_3858_ = v_isSharedCheck_3868_;
goto v_resetjp_3856_;
}
else
{
lean_inc(v_a_3855_);
lean_dec(v___x_3846_);
v___x_3857_ = lean_box(0);
v_isShared_3858_ = v_isSharedCheck_3868_;
goto v_resetjp_3856_;
}
v_resetjp_3856_:
{
lean_object* v___x_3859_; lean_object* v___x_3861_; 
v___x_3859_ = lean_io_error_to_string(v_a_3855_);
if (v_isShared_3858_ == 0)
{
lean_ctor_set_tag(v___x_3857_, 3);
lean_ctor_set(v___x_3857_, 0, v___x_3859_);
v___x_3861_ = v___x_3857_;
goto v_reusejp_3860_;
}
else
{
lean_object* v_reuseFailAlloc_3867_; 
v_reuseFailAlloc_3867_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3867_, 0, v___x_3859_);
v___x_3861_ = v_reuseFailAlloc_3867_;
goto v_reusejp_3860_;
}
v_reusejp_3860_:
{
lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3865_; 
v___x_3862_ = l_Lean_MessageData_ofFormat(v___x_3861_);
lean_inc(v_ref_3139_);
v___x_3863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3863_, 0, v_ref_3139_);
lean_ctor_set(v___x_3863_, 1, v___x_3862_);
if (v_isShared_3844_ == 0)
{
lean_ctor_set(v___x_3843_, 0, v___x_3863_);
v___x_3865_ = v___x_3843_;
goto v_reusejp_3864_;
}
else
{
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v___x_3863_);
v___x_3865_ = v_reuseFailAlloc_3866_;
goto v_reusejp_3864_;
}
v_reusejp_3864_:
{
v___y_3790_ = v___y_3806_;
v___y_3791_ = v___x_3845_;
v___y_3792_ = v___y_3807_;
v___y_3793_ = v_a_3841_;
v___y_3794_ = v___y_3808_;
v___y_3795_ = v___y_3809_;
v_a_3796_ = v___x_3865_;
goto v___jp_3789_;
}
}
}
}
}
}
}
v___jp_3870_:
{
lean_object* v___x_3871_; lean_object* v_a_3872_; lean_object* v___x_3873_; uint8_t v___x_3874_; 
v___x_3871_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_3021_);
v_a_3872_ = lean_ctor_get(v___x_3871_, 0);
lean_inc(v_a_3872_);
lean_dec_ref(v___x_3871_);
v___x_3873_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3874_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_3138_, v___x_3873_);
if (v___x_3874_ == 0)
{
lean_object* v___x_3875_; 
v___x_3875_ = lean_io_mono_nanos_now();
if (v___x_3548_ == 0)
{
lean_object* v___x_3876_; uint8_t v___x_3877_; 
v___x_3876_ = l_Lean_trace_profiler;
v___x_3877_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_3138_, v___x_3876_);
if (v___x_3877_ == 0)
{
lean_object* v___x_3878_; 
v___x_3878_ = l_IO_lazyPure___redArg(v___f_3145_);
if (lean_obj_tag(v___x_3878_) == 0)
{
lean_object* v_a_3879_; 
v_a_3879_ = lean_ctor_get(v___x_3878_, 0);
lean_inc(v_a_3879_);
lean_dec_ref_known(v___x_3878_, 1);
v___y_3742_ = v___x_3873_;
v___y_3743_ = v___x_3875_;
v___y_3744_ = v_a_3872_;
v_a_3745_ = v_a_3879_;
goto v___jp_3741_;
}
else
{
lean_object* v_a_3880_; lean_object* v___x_3882_; uint8_t v_isShared_3883_; uint8_t v_isSharedCheck_3890_; 
lean_dec_ref(v_unusedHypotheses_3074_);
lean_dec_ref(v_reflectionResult_3016_);
lean_dec(v_goal_3015_);
lean_dec_ref(v_ctx_3014_);
v_a_3880_ = lean_ctor_get(v___x_3878_, 0);
v_isSharedCheck_3890_ = !lean_is_exclusive(v___x_3878_);
if (v_isSharedCheck_3890_ == 0)
{
v___x_3882_ = v___x_3878_;
v_isShared_3883_ = v_isSharedCheck_3890_;
goto v_resetjp_3881_;
}
else
{
lean_inc(v_a_3880_);
lean_dec(v___x_3878_);
v___x_3882_ = lean_box(0);
v_isShared_3883_ = v_isSharedCheck_3890_;
goto v_resetjp_3881_;
}
v_resetjp_3881_:
{
lean_object* v___x_3884_; lean_object* v___x_3886_; 
v___x_3884_ = lean_io_error_to_string(v_a_3880_);
if (v_isShared_3883_ == 0)
{
lean_ctor_set_tag(v___x_3882_, 3);
lean_ctor_set(v___x_3882_, 0, v___x_3884_);
v___x_3886_ = v___x_3882_;
goto v_reusejp_3885_;
}
else
{
lean_object* v_reuseFailAlloc_3889_; 
v_reuseFailAlloc_3889_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3889_, 0, v___x_3884_);
v___x_3886_ = v_reuseFailAlloc_3889_;
goto v_reusejp_3885_;
}
v_reusejp_3885_:
{
lean_object* v___x_3887_; lean_object* v___x_3888_; 
v___x_3887_ = l_Lean_MessageData_ofFormat(v___x_3886_);
lean_inc(v_ref_3139_);
v___x_3888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3888_, 0, v_ref_3139_);
lean_ctor_set(v___x_3888_, 1, v___x_3887_);
v___y_3724_ = v___x_3875_;
v___y_3725_ = v_a_3872_;
v_a_3726_ = v___x_3888_;
goto v___jp_3723_;
}
}
}
}
else
{
v___y_3806_ = v___x_3873_;
v___y_3807_ = v___x_3875_;
v___y_3808_ = v___x_3548_;
v___y_3809_ = v_a_3872_;
v___y_3810_ = v___x_3874_;
goto v___jp_3805_;
}
}
else
{
v___y_3806_ = v___x_3873_;
v___y_3807_ = v___x_3875_;
v___y_3808_ = v___x_3548_;
v___y_3809_ = v_a_3872_;
v___y_3810_ = v___x_3874_;
goto v___jp_3805_;
}
}
else
{
lean_object* v___x_3891_; 
v___x_3891_ = lean_io_get_num_heartbeats();
if (v___x_3548_ == 0)
{
lean_object* v___x_3892_; uint8_t v___x_3893_; 
v___x_3892_ = l_Lean_trace_profiler;
v___x_3893_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_3138_, v___x_3892_);
if (v___x_3893_ == 0)
{
lean_object* v___x_3894_; 
v___x_3894_ = l_IO_lazyPure___redArg(v___f_3145_);
if (lean_obj_tag(v___x_3894_) == 0)
{
lean_object* v_a_3895_; 
v_a_3895_ = lean_ctor_get(v___x_3894_, 0);
lean_inc(v_a_3895_);
lean_dec_ref_known(v___x_3894_, 1);
v___y_3580_ = v___x_3873_;
v___y_3581_ = v___x_3891_;
v___y_3582_ = v_a_3872_;
v_a_3583_ = v_a_3895_;
goto v___jp_3579_;
}
else
{
lean_object* v_a_3896_; lean_object* v___x_3898_; uint8_t v_isShared_3899_; uint8_t v_isSharedCheck_3906_; 
lean_dec_ref(v_unusedHypotheses_3074_);
lean_dec_ref(v_reflectionResult_3016_);
lean_dec(v_goal_3015_);
lean_dec_ref(v_ctx_3014_);
v_a_3896_ = lean_ctor_get(v___x_3894_, 0);
v_isSharedCheck_3906_ = !lean_is_exclusive(v___x_3894_);
if (v_isSharedCheck_3906_ == 0)
{
v___x_3898_ = v___x_3894_;
v_isShared_3899_ = v_isSharedCheck_3906_;
goto v_resetjp_3897_;
}
else
{
lean_inc(v_a_3896_);
lean_dec(v___x_3894_);
v___x_3898_ = lean_box(0);
v_isShared_3899_ = v_isSharedCheck_3906_;
goto v_resetjp_3897_;
}
v_resetjp_3897_:
{
lean_object* v___x_3900_; lean_object* v___x_3902_; 
v___x_3900_ = lean_io_error_to_string(v_a_3896_);
if (v_isShared_3899_ == 0)
{
lean_ctor_set_tag(v___x_3898_, 3);
lean_ctor_set(v___x_3898_, 0, v___x_3900_);
v___x_3902_ = v___x_3898_;
goto v_reusejp_3901_;
}
else
{
lean_object* v_reuseFailAlloc_3905_; 
v_reuseFailAlloc_3905_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3905_, 0, v___x_3900_);
v___x_3902_ = v_reuseFailAlloc_3905_;
goto v_reusejp_3901_;
}
v_reusejp_3901_:
{
lean_object* v___x_3903_; lean_object* v___x_3904_; 
v___x_3903_ = l_Lean_MessageData_ofFormat(v___x_3902_);
lean_inc(v_ref_3139_);
v___x_3904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3904_, 0, v_ref_3139_);
lean_ctor_set(v___x_3904_, 1, v___x_3903_);
v___y_3562_ = v___x_3891_;
v___y_3563_ = v_a_3872_;
v_a_3564_ = v___x_3904_;
goto v___jp_3561_;
}
}
}
}
else
{
v___y_3644_ = v___x_3873_;
v___y_3645_ = v___x_3891_;
v___y_3646_ = v_a_3872_;
v___y_3647_ = v___x_3874_;
v___y_3648_ = v___x_3548_;
goto v___jp_3643_;
}
}
else
{
v___y_3644_ = v___x_3873_;
v___y_3645_ = v___x_3891_;
v___y_3646_ = v_a_3872_;
v___y_3647_ = v___x_3874_;
v___y_3648_ = v___x_3548_;
goto v___jp_3643_;
}
}
}
}
v___jp_3023_:
{
lean_object* v___x_3029_; 
lean_inc_ref(v___y_3024_);
v___x_3029_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_3024_, v_ctx_3014_, v_reflectionResult_3016_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_);
if (lean_obj_tag(v___x_3029_) == 0)
{
lean_object* v_a_3030_; lean_object* v___x_3032_; uint8_t v_isShared_3033_; uint8_t v_isSharedCheck_3039_; 
v_a_3030_ = lean_ctor_get(v___x_3029_, 0);
v_isSharedCheck_3039_ = !lean_is_exclusive(v___x_3029_);
if (v_isSharedCheck_3039_ == 0)
{
v___x_3032_ = v___x_3029_;
v_isShared_3033_ = v_isSharedCheck_3039_;
goto v_resetjp_3031_;
}
else
{
lean_inc(v_a_3030_);
lean_dec(v___x_3029_);
v___x_3032_ = lean_box(0);
v_isShared_3033_ = v_isSharedCheck_3039_;
goto v_resetjp_3031_;
}
v_resetjp_3031_:
{
lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3037_; 
v___x_3034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3034_, 0, v_a_3030_);
lean_ctor_set(v___x_3034_, 1, v___y_3024_);
v___x_3035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3035_, 0, v___x_3034_);
if (v_isShared_3033_ == 0)
{
lean_ctor_set(v___x_3032_, 0, v___x_3035_);
v___x_3037_ = v___x_3032_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v___x_3035_);
v___x_3037_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
return v___x_3037_;
}
}
}
else
{
lean_object* v_a_3040_; lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3047_; 
lean_dec_ref(v___y_3024_);
v_a_3040_ = lean_ctor_get(v___x_3029_, 0);
v_isSharedCheck_3047_ = !lean_is_exclusive(v___x_3029_);
if (v_isSharedCheck_3047_ == 0)
{
v___x_3042_ = v___x_3029_;
v_isShared_3043_ = v_isSharedCheck_3047_;
goto v_resetjp_3041_;
}
else
{
lean_inc(v_a_3040_);
lean_dec(v___x_3029_);
v___x_3042_ = lean_box(0);
v_isShared_3043_ = v_isSharedCheck_3047_;
goto v_resetjp_3041_;
}
v_resetjp_3041_:
{
lean_object* v___x_3045_; 
if (v_isShared_3043_ == 0)
{
v___x_3045_ = v___x_3042_;
goto v_reusejp_3044_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v_a_3040_);
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
v___jp_3048_:
{
lean_object* v___x_3054_; 
lean_inc_ref(v___y_3049_);
v___x_3054_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_3049_, v_ctx_3014_, v_reflectionResult_3016_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_);
if (lean_obj_tag(v___x_3054_) == 0)
{
lean_object* v_a_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3064_; 
v_a_3055_ = lean_ctor_get(v___x_3054_, 0);
v_isSharedCheck_3064_ = !lean_is_exclusive(v___x_3054_);
if (v_isSharedCheck_3064_ == 0)
{
v___x_3057_ = v___x_3054_;
v_isShared_3058_ = v_isSharedCheck_3064_;
goto v_resetjp_3056_;
}
else
{
lean_inc(v_a_3055_);
lean_dec(v___x_3054_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3064_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3062_; 
v___x_3059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3059_, 0, v_a_3055_);
lean_ctor_set(v___x_3059_, 1, v___y_3049_);
v___x_3060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3060_, 0, v___x_3059_);
if (v_isShared_3058_ == 0)
{
lean_ctor_set(v___x_3057_, 0, v___x_3060_);
v___x_3062_ = v___x_3057_;
goto v_reusejp_3061_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v___x_3060_);
v___x_3062_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3061_;
}
v_reusejp_3061_:
{
return v___x_3062_;
}
}
}
else
{
lean_object* v_a_3065_; lean_object* v___x_3067_; uint8_t v_isShared_3068_; uint8_t v_isSharedCheck_3072_; 
lean_dec_ref(v___y_3049_);
v_a_3065_ = lean_ctor_get(v___x_3054_, 0);
v_isSharedCheck_3072_ = !lean_is_exclusive(v___x_3054_);
if (v_isSharedCheck_3072_ == 0)
{
v___x_3067_ = v___x_3054_;
v_isShared_3068_ = v_isSharedCheck_3072_;
goto v_resetjp_3066_;
}
else
{
lean_inc(v_a_3065_);
lean_dec(v___x_3054_);
v___x_3067_ = lean_box(0);
v_isShared_3068_ = v_isSharedCheck_3072_;
goto v_resetjp_3066_;
}
v_resetjp_3066_:
{
lean_object* v___x_3070_; 
if (v_isShared_3068_ == 0)
{
v___x_3070_ = v___x_3067_;
goto v_reusejp_3069_;
}
else
{
lean_object* v_reuseFailAlloc_3071_; 
v_reuseFailAlloc_3071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3071_, 0, v_a_3065_);
v___x_3070_ = v_reuseFailAlloc_3071_;
goto v_reusejp_3069_;
}
v_reusejp_3069_:
{
return v___x_3070_;
}
}
}
}
v___jp_3075_:
{
lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; 
v___x_3078_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v___y_3076_, v___y_3077_, v_atomsAssignment_3017_);
lean_dec_ref(v___y_3077_);
v___x_3079_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3079_, 0, v_goal_3015_);
lean_ctor_set(v___x_3079_, 1, v_unusedHypotheses_3074_);
lean_ctor_set(v___x_3079_, 2, v___x_3078_);
v___x_3080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3080_, 0, v___x_3079_);
v___x_3081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3081_, 0, v___x_3080_);
return v___x_3081_;
}
v___jp_3082_:
{
if (lean_obj_tag(v___y_3089_) == 0)
{
lean_object* v_a_3090_; 
v_a_3090_ = lean_ctor_get(v___y_3089_, 0);
lean_inc(v_a_3090_);
lean_dec_ref_known(v___y_3089_, 1);
if (lean_obj_tag(v_a_3090_) == 0)
{
lean_object* v_toCold_3091_; lean_object* v_options_3092_; uint8_t v_hasTrace_3093_; 
lean_inc_ref(v_unusedHypotheses_3074_);
lean_dec_ref(v_reflectionResult_3016_);
lean_dec_ref(v_ctx_3014_);
v_toCold_3091_ = lean_ctor_get(v___y_3086_, 0);
v_options_3092_ = lean_ctor_get(v_toCold_3091_, 2);
v_hasTrace_3093_ = lean_ctor_get_uint8(v_options_3092_, sizeof(void*)*1);
if (v_hasTrace_3093_ == 0)
{
lean_object* v_a_3094_; 
v_a_3094_ = lean_ctor_get(v_a_3090_, 0);
lean_inc(v_a_3094_);
lean_dec_ref_known(v_a_3090_, 1);
v___y_3076_ = v___y_3083_;
v___y_3077_ = v_a_3094_;
goto v___jp_3075_;
}
else
{
lean_object* v_a_3095_; lean_object* v_inheritedTraceOptions_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; uint8_t v___x_3099_; 
v_a_3095_ = lean_ctor_get(v_a_3090_, 0);
lean_inc(v_a_3095_);
lean_dec_ref_known(v_a_3090_, 1);
v_inheritedTraceOptions_3096_ = lean_ctor_get(v_toCold_3091_, 11);
v___x_3097_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___y_3085_);
v___x_3098_ = l_Lean_Name_append(v___x_3097_, v___y_3085_);
v___x_3099_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3096_, v_options_3092_, v___x_3098_);
lean_dec(v___x_3098_);
if (v___x_3099_ == 0)
{
v___y_3076_ = v___y_3083_;
v___y_3077_ = v_a_3095_;
goto v___jp_3075_;
}
else
{
lean_object* v___x_3100_; lean_object* v___x_3101_; 
v___x_3100_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1);
lean_inc(v___y_3085_);
v___x_3101_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v___y_3085_, v___x_3100_, v___y_3088_, v___y_3087_, v___y_3086_, v___y_3084_);
if (lean_obj_tag(v___x_3101_) == 0)
{
lean_dec_ref_known(v___x_3101_, 1);
v___y_3076_ = v___y_3083_;
v___y_3077_ = v_a_3095_;
goto v___jp_3075_;
}
else
{
lean_object* v_a_3102_; lean_object* v___x_3104_; uint8_t v_isShared_3105_; uint8_t v_isSharedCheck_3109_; 
lean_dec(v_a_3095_);
lean_dec_ref(v___y_3083_);
lean_dec_ref(v_unusedHypotheses_3074_);
lean_dec(v_goal_3015_);
v_a_3102_ = lean_ctor_get(v___x_3101_, 0);
v_isSharedCheck_3109_ = !lean_is_exclusive(v___x_3101_);
if (v_isSharedCheck_3109_ == 0)
{
v___x_3104_ = v___x_3101_;
v_isShared_3105_ = v_isSharedCheck_3109_;
goto v_resetjp_3103_;
}
else
{
lean_inc(v_a_3102_);
lean_dec(v___x_3101_);
v___x_3104_ = lean_box(0);
v_isShared_3105_ = v_isSharedCheck_3109_;
goto v_resetjp_3103_;
}
v_resetjp_3103_:
{
lean_object* v___x_3107_; 
if (v_isShared_3105_ == 0)
{
v___x_3107_ = v___x_3104_;
goto v_reusejp_3106_;
}
else
{
lean_object* v_reuseFailAlloc_3108_; 
v_reuseFailAlloc_3108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3108_, 0, v_a_3102_);
v___x_3107_ = v_reuseFailAlloc_3108_;
goto v_reusejp_3106_;
}
v_reusejp_3106_:
{
return v___x_3107_;
}
}
}
}
}
}
else
{
lean_object* v_toCold_3110_; lean_object* v_options_3111_; uint8_t v_hasTrace_3112_; 
lean_dec_ref(v___y_3083_);
lean_dec(v_goal_3015_);
v_toCold_3110_ = lean_ctor_get(v___y_3086_, 0);
v_options_3111_ = lean_ctor_get(v_toCold_3110_, 2);
v_hasTrace_3112_ = lean_ctor_get_uint8(v_options_3111_, sizeof(void*)*1);
if (v_hasTrace_3112_ == 0)
{
lean_object* v_a_3113_; 
v_a_3113_ = lean_ctor_get(v_a_3090_, 0);
lean_inc(v_a_3113_);
lean_dec_ref_known(v_a_3090_, 1);
v___y_3024_ = v_a_3113_;
v___y_3025_ = v___y_3088_;
v___y_3026_ = v___y_3087_;
v___y_3027_ = v___y_3086_;
v___y_3028_ = v___y_3084_;
goto v___jp_3023_;
}
else
{
lean_object* v_a_3114_; lean_object* v_inheritedTraceOptions_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; uint8_t v___x_3118_; 
v_a_3114_ = lean_ctor_get(v_a_3090_, 0);
lean_inc(v_a_3114_);
lean_dec_ref_known(v_a_3090_, 1);
v_inheritedTraceOptions_3115_ = lean_ctor_get(v_toCold_3110_, 11);
v___x_3116_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___y_3085_);
v___x_3117_ = l_Lean_Name_append(v___x_3116_, v___y_3085_);
v___x_3118_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3115_, v_options_3111_, v___x_3117_);
lean_dec(v___x_3117_);
if (v___x_3118_ == 0)
{
v___y_3024_ = v_a_3114_;
v___y_3025_ = v___y_3088_;
v___y_3026_ = v___y_3087_;
v___y_3027_ = v___y_3086_;
v___y_3028_ = v___y_3084_;
goto v___jp_3023_;
}
else
{
lean_object* v___x_3119_; lean_object* v___x_3120_; 
v___x_3119_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3);
lean_inc(v___y_3085_);
v___x_3120_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v___y_3085_, v___x_3119_, v___y_3088_, v___y_3087_, v___y_3086_, v___y_3084_);
if (lean_obj_tag(v___x_3120_) == 0)
{
lean_dec_ref_known(v___x_3120_, 1);
v___y_3024_ = v_a_3114_;
v___y_3025_ = v___y_3088_;
v___y_3026_ = v___y_3087_;
v___y_3027_ = v___y_3086_;
v___y_3028_ = v___y_3084_;
goto v___jp_3023_;
}
else
{
lean_object* v_a_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3128_; 
lean_dec(v_a_3114_);
lean_dec_ref(v_reflectionResult_3016_);
lean_dec_ref(v_ctx_3014_);
v_a_3121_ = lean_ctor_get(v___x_3120_, 0);
v_isSharedCheck_3128_ = !lean_is_exclusive(v___x_3120_);
if (v_isSharedCheck_3128_ == 0)
{
v___x_3123_ = v___x_3120_;
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_a_3121_);
lean_dec(v___x_3120_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
lean_object* v___x_3126_; 
if (v_isShared_3124_ == 0)
{
v___x_3126_ = v___x_3123_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v_a_3121_);
v___x_3126_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
return v___x_3126_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3129_; lean_object* v___x_3131_; uint8_t v_isShared_3132_; uint8_t v_isSharedCheck_3136_; 
lean_dec_ref(v___y_3083_);
lean_dec_ref(v_reflectionResult_3016_);
lean_dec(v_goal_3015_);
lean_dec_ref(v_ctx_3014_);
v_a_3129_ = lean_ctor_get(v___y_3089_, 0);
v_isSharedCheck_3136_ = !lean_is_exclusive(v___y_3089_);
if (v_isSharedCheck_3136_ == 0)
{
v___x_3131_ = v___y_3089_;
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
else
{
lean_inc(v_a_3129_);
lean_dec(v___y_3089_);
v___x_3131_ = lean_box(0);
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
v_resetjp_3130_:
{
lean_object* v___x_3134_; 
if (v_isShared_3132_ == 0)
{
v___x_3134_ = v___x_3131_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v_a_3129_);
v___x_3134_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
return v___x_3134_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___boxed(lean_object* v_ctx_4370_, lean_object* v_goal_4371_, lean_object* v_reflectionResult_4372_, lean_object* v_atomsAssignment_4373_, lean_object* v_a_4374_, lean_object* v_a_4375_, lean_object* v_a_4376_, lean_object* v_a_4377_, lean_object* v_a_4378_){
_start:
{
lean_object* v_res_4379_; 
v_res_4379_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster(v_ctx_4370_, v_goal_4371_, v_reflectionResult_4372_, v_atomsAssignment_4373_, v_a_4374_, v_a_4375_, v_a_4376_, v_a_4377_);
lean_dec(v_a_4377_);
lean_dec_ref(v_a_4376_);
lean_dec(v_a_4375_);
lean_dec_ref(v_a_4374_);
lean_dec_ref(v_atomsAssignment_4373_);
return v_res_4379_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6(lean_object* v_acc_4380_, lean_object* v_decls_4381_, lean_object* v_hinv_4382_, lean_object* v_idx_4383_, lean_object* v_hidx_4384_, lean_object* v_a_4385_){
_start:
{
lean_object* v___x_4386_; 
v___x_4386_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6___redArg(v_acc_4380_, v_decls_4381_, v_idx_4383_, v_a_4385_);
return v___x_4386_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6___boxed(lean_object* v_acc_4387_, lean_object* v_decls_4388_, lean_object* v_hinv_4389_, lean_object* v_idx_4390_, lean_object* v_hidx_4391_, lean_object* v_a_4392_){
_start:
{
lean_object* v_res_4393_; 
v_res_4393_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6(v_acc_4387_, v_decls_4388_, v_hinv_4389_, v_idx_4390_, v_hidx_4391_, v_a_4392_);
lean_dec_ref(v_decls_4388_);
return v_res_4393_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7(lean_object* v___x_4394_, lean_object* v_00_u03b2_4395_, lean_object* v_m_4396_, lean_object* v_a_4397_){
_start:
{
uint8_t v___x_4398_; 
v___x_4398_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7___redArg(v___x_4394_, v_m_4396_, v_a_4397_);
return v___x_4398_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7___boxed(lean_object* v___x_4399_, lean_object* v_00_u03b2_4400_, lean_object* v_m_4401_, lean_object* v_a_4402_){
_start:
{
uint8_t v_res_4403_; lean_object* v_r_4404_; 
v_res_4403_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7(v___x_4399_, v_00_u03b2_4400_, v_m_4401_, v_a_4402_);
lean_dec(v_a_4402_);
lean_dec_ref(v_m_4401_);
lean_dec(v___x_4399_);
v_r_4404_ = lean_box(v_res_4403_);
return v_r_4404_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8(lean_object* v___x_4405_, lean_object* v_00_u03b2_4406_, lean_object* v_m_4407_, lean_object* v_a_4408_, lean_object* v_b_4409_){
_start:
{
lean_object* v___x_4410_; 
v___x_4410_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8___redArg(v___x_4405_, v_m_4407_, v_a_4408_, v_b_4409_);
return v___x_4410_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8___boxed(lean_object* v___x_4411_, lean_object* v_00_u03b2_4412_, lean_object* v_m_4413_, lean_object* v_a_4414_, lean_object* v_b_4415_){
_start:
{
lean_object* v_res_4416_; 
v_res_4416_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8(v___x_4411_, v_00_u03b2_4412_, v_m_4413_, v_a_4414_, v_b_4415_);
lean_dec(v___x_4411_);
return v_res_4416_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7_spec__12(lean_object* v___x_4417_, lean_object* v_00_u03b2_4418_, lean_object* v_a_4419_, lean_object* v_x_4420_){
_start:
{
uint8_t v___x_4421_; 
v___x_4421_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7_spec__12___redArg(v_a_4419_, v_x_4420_);
return v___x_4421_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7_spec__12___boxed(lean_object* v___x_4422_, lean_object* v_00_u03b2_4423_, lean_object* v_a_4424_, lean_object* v_x_4425_){
_start:
{
uint8_t v_res_4426_; lean_object* v_r_4427_; 
v_res_4426_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7_spec__12(v___x_4422_, v_00_u03b2_4423_, v_a_4424_, v_x_4425_);
lean_dec(v_x_4425_);
lean_dec(v_a_4424_);
lean_dec(v___x_4422_);
v_r_4427_ = lean_box(v_res_4426_);
return v_r_4427_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14(lean_object* v___x_4428_, lean_object* v_00_u03b2_4429_, lean_object* v_data_4430_){
_start:
{
lean_object* v___x_4431_; 
v___x_4431_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14___redArg(v___x_4428_, v_data_4430_);
return v___x_4431_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14___boxed(lean_object* v___x_4432_, lean_object* v_00_u03b2_4433_, lean_object* v_data_4434_){
_start:
{
lean_object* v_res_4435_; 
v_res_4435_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14(v___x_4432_, v_00_u03b2_4433_, v_data_4434_);
lean_dec(v___x_4432_);
return v_res_4435_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14_spec__17(lean_object* v___x_4436_, lean_object* v_00_u03b2_4437_, lean_object* v_i_4438_, lean_object* v_source_4439_, lean_object* v_target_4440_){
_start:
{
lean_object* v___x_4441_; 
v___x_4441_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14_spec__17___redArg(v_i_4438_, v_source_4439_, v_target_4440_);
return v___x_4441_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14_spec__17___boxed(lean_object* v___x_4442_, lean_object* v_00_u03b2_4443_, lean_object* v_i_4444_, lean_object* v_source_4445_, lean_object* v_target_4446_){
_start:
{
lean_object* v_res_4447_; 
v_res_4447_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14_spec__17(v___x_4442_, v_00_u03b2_4443_, v_i_4444_, v_source_4445_, v_target_4446_);
lean_dec(v___x_4442_);
return v_res_4447_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14_spec__17_spec__18(lean_object* v_00_u03b2_4448_, lean_object* v_x_4449_, lean_object* v_x_4450_){
_start:
{
lean_object* v___x_4451_; 
v___x_4451_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14_spec__17_spec__18___redArg(v_x_4449_, v_x_4450_);
return v___x_4451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0(lean_object* v_x_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_){
_start:
{
lean_object* v___x_4458_; lean_object* v___x_4459_; 
v___x_4458_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2);
v___x_4459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4459_, 0, v___x_4458_);
return v___x_4459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0___boxed(lean_object* v_x_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_){
_start:
{
lean_object* v_res_4466_; 
v_res_4466_ = l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0(v_x_4460_, v___y_4461_, v___y_4462_, v___y_4463_, v___y_4464_);
lean_dec(v___y_4464_);
lean_dec_ref(v___y_4463_);
lean_dec(v___y_4462_);
lean_dec_ref(v___y_4461_);
lean_dec_ref(v_x_4460_);
return v_res_4466_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0_spec__0(lean_object* v_e_4467_){
_start:
{
if (lean_obj_tag(v_e_4467_) == 0)
{
uint8_t v___x_4468_; 
v___x_4468_ = 2;
return v___x_4468_;
}
else
{
uint8_t v___x_4469_; 
v___x_4469_ = 0;
return v___x_4469_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0_spec__0___boxed(lean_object* v_e_4470_){
_start:
{
uint8_t v_res_4471_; lean_object* v_r_4472_; 
v_res_4471_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0_spec__0(v_e_4470_);
lean_dec_ref(v_e_4470_);
v_r_4472_ = lean_box(v_res_4471_);
return v_r_4472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(lean_object* v_cls_4473_, uint8_t v_collapsed_4474_, lean_object* v_tag_4475_, lean_object* v_opts_4476_, uint8_t v_clsEnabled_4477_, lean_object* v_oldTraces_4478_, lean_object* v_msg_4479_, lean_object* v_resStartStop_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_){
_start:
{
lean_object* v_fst_4486_; lean_object* v_snd_4487_; lean_object* v___y_4489_; lean_object* v___y_4490_; lean_object* v_data_4491_; lean_object* v_fst_4502_; lean_object* v_snd_4503_; lean_object* v___x_4504_; uint8_t v___x_4505_; lean_object* v___y_4507_; lean_object* v_a_4508_; uint8_t v___y_4523_; double v___y_4555_; 
v_fst_4486_ = lean_ctor_get(v_resStartStop_4480_, 0);
lean_inc(v_fst_4486_);
v_snd_4487_ = lean_ctor_get(v_resStartStop_4480_, 1);
lean_inc(v_snd_4487_);
lean_dec_ref(v_resStartStop_4480_);
v_fst_4502_ = lean_ctor_get(v_snd_4487_, 0);
lean_inc(v_fst_4502_);
v_snd_4503_ = lean_ctor_get(v_snd_4487_, 1);
lean_inc(v_snd_4503_);
lean_dec(v_snd_4487_);
v___x_4504_ = l_Lean_trace_profiler;
v___x_4505_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_4476_, v___x_4504_);
if (v___x_4505_ == 0)
{
v___y_4523_ = v___x_4505_;
goto v___jp_4522_;
}
else
{
lean_object* v___x_4560_; uint8_t v___x_4561_; 
v___x_4560_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4561_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_4476_, v___x_4560_);
if (v___x_4561_ == 0)
{
lean_object* v___x_4562_; lean_object* v___x_4563_; double v___x_4564_; double v___x_4565_; double v___x_4566_; 
v___x_4562_ = l_Lean_trace_profiler_threshold;
v___x_4563_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_4476_, v___x_4562_);
v___x_4564_ = lean_float_of_nat(v___x_4563_);
v___x_4565_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3);
v___x_4566_ = lean_float_div(v___x_4564_, v___x_4565_);
v___y_4555_ = v___x_4566_;
goto v___jp_4554_;
}
else
{
lean_object* v___x_4567_; lean_object* v___x_4568_; double v___x_4569_; 
v___x_4567_ = l_Lean_trace_profiler_threshold;
v___x_4568_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_4476_, v___x_4567_);
v___x_4569_ = lean_float_of_nat(v___x_4568_);
v___y_4555_ = v___x_4569_;
goto v___jp_4554_;
}
}
v___jp_4488_:
{
lean_object* v___x_4492_; 
lean_inc(v___y_4490_);
v___x_4492_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2(v_oldTraces_4478_, v_data_4491_, v___y_4490_, v___y_4489_, v___y_4481_, v___y_4482_, v___y_4483_, v___y_4484_);
if (lean_obj_tag(v___x_4492_) == 0)
{
lean_object* v___x_4493_; 
lean_dec_ref_known(v___x_4492_, 1);
v___x_4493_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(v_fst_4486_);
return v___x_4493_;
}
else
{
lean_object* v_a_4494_; lean_object* v___x_4496_; uint8_t v_isShared_4497_; uint8_t v_isSharedCheck_4501_; 
lean_dec(v_fst_4486_);
v_a_4494_ = lean_ctor_get(v___x_4492_, 0);
v_isSharedCheck_4501_ = !lean_is_exclusive(v___x_4492_);
if (v_isSharedCheck_4501_ == 0)
{
v___x_4496_ = v___x_4492_;
v_isShared_4497_ = v_isSharedCheck_4501_;
goto v_resetjp_4495_;
}
else
{
lean_inc(v_a_4494_);
lean_dec(v___x_4492_);
v___x_4496_ = lean_box(0);
v_isShared_4497_ = v_isSharedCheck_4501_;
goto v_resetjp_4495_;
}
v_resetjp_4495_:
{
lean_object* v___x_4499_; 
if (v_isShared_4497_ == 0)
{
v___x_4499_ = v___x_4496_;
goto v_reusejp_4498_;
}
else
{
lean_object* v_reuseFailAlloc_4500_; 
v_reuseFailAlloc_4500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4500_, 0, v_a_4494_);
v___x_4499_ = v_reuseFailAlloc_4500_;
goto v_reusejp_4498_;
}
v_reusejp_4498_:
{
return v___x_4499_;
}
}
}
}
v___jp_4506_:
{
uint8_t v_result_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; double v___x_4512_; lean_object* v_data_4513_; 
v_result_4509_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0_spec__0(v_fst_4486_);
v___x_4510_ = lean_box(v_result_4509_);
v___x_4511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4511_, 0, v___x_4510_);
v___x_4512_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0);
lean_inc_ref(v_tag_4475_);
lean_inc_ref(v___x_4511_);
lean_inc(v_cls_4473_);
v_data_4513_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4513_, 0, v_cls_4473_);
lean_ctor_set(v_data_4513_, 1, v___x_4511_);
lean_ctor_set(v_data_4513_, 2, v_tag_4475_);
lean_ctor_set_float(v_data_4513_, sizeof(void*)*3, v___x_4512_);
lean_ctor_set_float(v_data_4513_, sizeof(void*)*3 + 8, v___x_4512_);
lean_ctor_set_uint8(v_data_4513_, sizeof(void*)*3 + 16, v_collapsed_4474_);
if (v___x_4505_ == 0)
{
lean_dec_ref_known(v___x_4511_, 1);
lean_dec(v_snd_4503_);
lean_dec(v_fst_4502_);
lean_dec_ref(v_tag_4475_);
lean_dec(v_cls_4473_);
v___y_4489_ = v_a_4508_;
v___y_4490_ = v___y_4507_;
v_data_4491_ = v_data_4513_;
goto v___jp_4488_;
}
else
{
lean_object* v_data_4514_; double v___x_4515_; double v___x_4516_; 
lean_dec_ref_known(v_data_4513_, 3);
v_data_4514_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4514_, 0, v_cls_4473_);
lean_ctor_set(v_data_4514_, 1, v___x_4511_);
lean_ctor_set(v_data_4514_, 2, v_tag_4475_);
v___x_4515_ = lean_unbox_float(v_fst_4502_);
lean_dec(v_fst_4502_);
lean_ctor_set_float(v_data_4514_, sizeof(void*)*3, v___x_4515_);
v___x_4516_ = lean_unbox_float(v_snd_4503_);
lean_dec(v_snd_4503_);
lean_ctor_set_float(v_data_4514_, sizeof(void*)*3 + 8, v___x_4516_);
lean_ctor_set_uint8(v_data_4514_, sizeof(void*)*3 + 16, v_collapsed_4474_);
v___y_4489_ = v_a_4508_;
v___y_4490_ = v___y_4507_;
v_data_4491_ = v_data_4514_;
goto v___jp_4488_;
}
}
v___jp_4517_:
{
lean_object* v_ref_4518_; lean_object* v___x_4519_; 
v_ref_4518_ = lean_ctor_get(v___y_4483_, 2);
lean_inc(v___y_4484_);
lean_inc_ref(v___y_4483_);
lean_inc(v___y_4482_);
lean_inc_ref(v___y_4481_);
lean_inc(v_fst_4486_);
v___x_4519_ = lean_apply_6(v_msg_4479_, v_fst_4486_, v___y_4481_, v___y_4482_, v___y_4483_, v___y_4484_, lean_box(0));
if (lean_obj_tag(v___x_4519_) == 0)
{
lean_object* v_a_4520_; 
v_a_4520_ = lean_ctor_get(v___x_4519_, 0);
lean_inc(v_a_4520_);
lean_dec_ref_known(v___x_4519_, 1);
v___y_4507_ = v_ref_4518_;
v_a_4508_ = v_a_4520_;
goto v___jp_4506_;
}
else
{
lean_object* v___x_4521_; 
lean_dec_ref_known(v___x_4519_, 1);
v___x_4521_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2);
v___y_4507_ = v_ref_4518_;
v_a_4508_ = v___x_4521_;
goto v___jp_4506_;
}
}
v___jp_4522_:
{
if (v_clsEnabled_4477_ == 0)
{
if (v___y_4523_ == 0)
{
lean_object* v___x_4524_; lean_object* v_traceState_4525_; lean_object* v_env_4526_; lean_object* v_nextMacroScope_4527_; lean_object* v_ngen_4528_; lean_object* v_auxDeclNGen_4529_; lean_object* v_cache_4530_; lean_object* v_recordedDeps_4531_; lean_object* v_messages_4532_; lean_object* v_infoState_4533_; lean_object* v_snapshotTasks_4534_; lean_object* v___x_4536_; uint8_t v_isShared_4537_; uint8_t v_isSharedCheck_4553_; 
lean_dec(v_snd_4503_);
lean_dec(v_fst_4502_);
lean_dec_ref(v_msg_4479_);
lean_dec_ref(v_tag_4475_);
lean_dec(v_cls_4473_);
v___x_4524_ = lean_st_ref_take(v___y_4484_);
v_traceState_4525_ = lean_ctor_get(v___x_4524_, 4);
v_env_4526_ = lean_ctor_get(v___x_4524_, 0);
v_nextMacroScope_4527_ = lean_ctor_get(v___x_4524_, 1);
v_ngen_4528_ = lean_ctor_get(v___x_4524_, 2);
v_auxDeclNGen_4529_ = lean_ctor_get(v___x_4524_, 3);
v_cache_4530_ = lean_ctor_get(v___x_4524_, 5);
v_recordedDeps_4531_ = lean_ctor_get(v___x_4524_, 6);
v_messages_4532_ = lean_ctor_get(v___x_4524_, 7);
v_infoState_4533_ = lean_ctor_get(v___x_4524_, 8);
v_snapshotTasks_4534_ = lean_ctor_get(v___x_4524_, 9);
v_isSharedCheck_4553_ = !lean_is_exclusive(v___x_4524_);
if (v_isSharedCheck_4553_ == 0)
{
v___x_4536_ = v___x_4524_;
v_isShared_4537_ = v_isSharedCheck_4553_;
goto v_resetjp_4535_;
}
else
{
lean_inc(v_snapshotTasks_4534_);
lean_inc(v_infoState_4533_);
lean_inc(v_messages_4532_);
lean_inc(v_recordedDeps_4531_);
lean_inc(v_cache_4530_);
lean_inc(v_traceState_4525_);
lean_inc(v_auxDeclNGen_4529_);
lean_inc(v_ngen_4528_);
lean_inc(v_nextMacroScope_4527_);
lean_inc(v_env_4526_);
lean_dec(v___x_4524_);
v___x_4536_ = lean_box(0);
v_isShared_4537_ = v_isSharedCheck_4553_;
goto v_resetjp_4535_;
}
v_resetjp_4535_:
{
uint64_t v_tid_4538_; lean_object* v_traces_4539_; lean_object* v___x_4541_; uint8_t v_isShared_4542_; uint8_t v_isSharedCheck_4552_; 
v_tid_4538_ = lean_ctor_get_uint64(v_traceState_4525_, sizeof(void*)*1);
v_traces_4539_ = lean_ctor_get(v_traceState_4525_, 0);
v_isSharedCheck_4552_ = !lean_is_exclusive(v_traceState_4525_);
if (v_isSharedCheck_4552_ == 0)
{
v___x_4541_ = v_traceState_4525_;
v_isShared_4542_ = v_isSharedCheck_4552_;
goto v_resetjp_4540_;
}
else
{
lean_inc(v_traces_4539_);
lean_dec(v_traceState_4525_);
v___x_4541_ = lean_box(0);
v_isShared_4542_ = v_isSharedCheck_4552_;
goto v_resetjp_4540_;
}
v_resetjp_4540_:
{
lean_object* v___x_4543_; lean_object* v___x_4545_; 
v___x_4543_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_4478_, v_traces_4539_);
lean_dec_ref(v_traces_4539_);
if (v_isShared_4542_ == 0)
{
lean_ctor_set(v___x_4541_, 0, v___x_4543_);
v___x_4545_ = v___x_4541_;
goto v_reusejp_4544_;
}
else
{
lean_object* v_reuseFailAlloc_4551_; 
v_reuseFailAlloc_4551_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4551_, 0, v___x_4543_);
lean_ctor_set_uint64(v_reuseFailAlloc_4551_, sizeof(void*)*1, v_tid_4538_);
v___x_4545_ = v_reuseFailAlloc_4551_;
goto v_reusejp_4544_;
}
v_reusejp_4544_:
{
lean_object* v___x_4547_; 
if (v_isShared_4537_ == 0)
{
lean_ctor_set(v___x_4536_, 4, v___x_4545_);
v___x_4547_ = v___x_4536_;
goto v_reusejp_4546_;
}
else
{
lean_object* v_reuseFailAlloc_4550_; 
v_reuseFailAlloc_4550_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4550_, 0, v_env_4526_);
lean_ctor_set(v_reuseFailAlloc_4550_, 1, v_nextMacroScope_4527_);
lean_ctor_set(v_reuseFailAlloc_4550_, 2, v_ngen_4528_);
lean_ctor_set(v_reuseFailAlloc_4550_, 3, v_auxDeclNGen_4529_);
lean_ctor_set(v_reuseFailAlloc_4550_, 4, v___x_4545_);
lean_ctor_set(v_reuseFailAlloc_4550_, 5, v_cache_4530_);
lean_ctor_set(v_reuseFailAlloc_4550_, 6, v_recordedDeps_4531_);
lean_ctor_set(v_reuseFailAlloc_4550_, 7, v_messages_4532_);
lean_ctor_set(v_reuseFailAlloc_4550_, 8, v_infoState_4533_);
lean_ctor_set(v_reuseFailAlloc_4550_, 9, v_snapshotTasks_4534_);
v___x_4547_ = v_reuseFailAlloc_4550_;
goto v_reusejp_4546_;
}
v_reusejp_4546_:
{
lean_object* v___x_4548_; lean_object* v___x_4549_; 
v___x_4548_ = lean_st_ref_put(v___y_4484_, v___x_4547_);
v___x_4549_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(v_fst_4486_);
return v___x_4549_;
}
}
}
}
}
else
{
goto v___jp_4517_;
}
}
else
{
goto v___jp_4517_;
}
}
v___jp_4554_:
{
double v___x_4556_; double v___x_4557_; double v___x_4558_; uint8_t v___x_4559_; 
v___x_4556_ = lean_unbox_float(v_snd_4503_);
v___x_4557_ = lean_unbox_float(v_fst_4502_);
v___x_4558_ = lean_float_sub(v___x_4556_, v___x_4557_);
v___x_4559_ = lean_float_decLt(v___y_4555_, v___x_4558_);
v___y_4523_ = v___x_4559_;
goto v___jp_4522_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___boxed(lean_object* v_cls_4570_, lean_object* v_collapsed_4571_, lean_object* v_tag_4572_, lean_object* v_opts_4573_, lean_object* v_clsEnabled_4574_, lean_object* v_oldTraces_4575_, lean_object* v_msg_4576_, lean_object* v_resStartStop_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_){
_start:
{
uint8_t v_collapsed_boxed_4583_; uint8_t v_clsEnabled_boxed_4584_; lean_object* v_res_4585_; 
v_collapsed_boxed_4583_ = lean_unbox(v_collapsed_4571_);
v_clsEnabled_boxed_4584_ = lean_unbox(v_clsEnabled_4574_);
v_res_4585_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(v_cls_4570_, v_collapsed_boxed_4583_, v_tag_4572_, v_opts_4573_, v_clsEnabled_boxed_4584_, v_oldTraces_4575_, v_msg_4576_, v_resStartStop_4577_, v___y_4578_, v___y_4579_, v___y_4580_, v___y_4581_);
lean_dec(v___y_4581_);
lean_dec_ref(v___y_4580_);
lean_dec(v___y_4579_);
lean_dec_ref(v___y_4578_);
lean_dec_ref(v_opts_4573_);
return v_res_4585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg(lean_object* v_ctx_4587_, lean_object* v_reflectionResult_4588_, lean_object* v_a_4589_, lean_object* v_a_4590_, lean_object* v_a_4591_, lean_object* v_a_4592_){
_start:
{
lean_object* v_toCold_4594_; lean_object* v_options_4595_; uint8_t v_hasTrace_4596_; 
v_toCold_4594_ = lean_ctor_get(v_a_4591_, 0);
v_options_4595_ = lean_ctor_get(v_toCold_4594_, 2);
v_hasTrace_4596_ = lean_ctor_get_uint8(v_options_4595_, sizeof(void*)*1);
if (v_hasTrace_4596_ == 0)
{
lean_object* v_config_4597_; lean_object* v_lratPath_4598_; uint8_t v_trimProofs_4599_; lean_object* v___x_4600_; 
v_config_4597_ = lean_ctor_get(v_ctx_4587_, 5);
v_lratPath_4598_ = lean_ctor_get(v_ctx_4587_, 4);
v_trimProofs_4599_ = lean_ctor_get_uint8(v_config_4597_, sizeof(void*)*2);
v___x_4600_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_4598_, v_trimProofs_4599_, v_a_4591_, v_a_4592_);
if (lean_obj_tag(v___x_4600_) == 0)
{
lean_object* v_a_4601_; lean_object* v___x_4602_; 
v_a_4601_ = lean_ctor_get(v___x_4600_, 0);
lean_inc(v_a_4601_);
lean_dec_ref_known(v___x_4600_, 1);
v___x_4602_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_4601_, v_ctx_4587_, v_reflectionResult_4588_, v_a_4589_, v_a_4590_, v_a_4591_, v_a_4592_);
if (lean_obj_tag(v___x_4602_) == 0)
{
lean_object* v_a_4603_; lean_object* v___x_4605_; uint8_t v_isShared_4606_; uint8_t v_isSharedCheck_4613_; 
v_a_4603_ = lean_ctor_get(v___x_4602_, 0);
v_isSharedCheck_4613_ = !lean_is_exclusive(v___x_4602_);
if (v_isSharedCheck_4613_ == 0)
{
v___x_4605_ = v___x_4602_;
v_isShared_4606_ = v_isSharedCheck_4613_;
goto v_resetjp_4604_;
}
else
{
lean_inc(v_a_4603_);
lean_dec(v___x_4602_);
v___x_4605_ = lean_box(0);
v_isShared_4606_ = v_isSharedCheck_4613_;
goto v_resetjp_4604_;
}
v_resetjp_4604_:
{
lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4611_; 
v___x_4607_ = lean_box(0);
v___x_4608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4608_, 0, v_a_4603_);
lean_ctor_set(v___x_4608_, 1, v___x_4607_);
v___x_4609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4609_, 0, v___x_4608_);
if (v_isShared_4606_ == 0)
{
lean_ctor_set(v___x_4605_, 0, v___x_4609_);
v___x_4611_ = v___x_4605_;
goto v_reusejp_4610_;
}
else
{
lean_object* v_reuseFailAlloc_4612_; 
v_reuseFailAlloc_4612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4612_, 0, v___x_4609_);
v___x_4611_ = v_reuseFailAlloc_4612_;
goto v_reusejp_4610_;
}
v_reusejp_4610_:
{
return v___x_4611_;
}
}
}
else
{
lean_object* v_a_4614_; lean_object* v___x_4616_; uint8_t v_isShared_4617_; uint8_t v_isSharedCheck_4621_; 
v_a_4614_ = lean_ctor_get(v___x_4602_, 0);
v_isSharedCheck_4621_ = !lean_is_exclusive(v___x_4602_);
if (v_isSharedCheck_4621_ == 0)
{
v___x_4616_ = v___x_4602_;
v_isShared_4617_ = v_isSharedCheck_4621_;
goto v_resetjp_4615_;
}
else
{
lean_inc(v_a_4614_);
lean_dec(v___x_4602_);
v___x_4616_ = lean_box(0);
v_isShared_4617_ = v_isSharedCheck_4621_;
goto v_resetjp_4615_;
}
v_resetjp_4615_:
{
lean_object* v___x_4619_; 
if (v_isShared_4617_ == 0)
{
v___x_4619_ = v___x_4616_;
goto v_reusejp_4618_;
}
else
{
lean_object* v_reuseFailAlloc_4620_; 
v_reuseFailAlloc_4620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4620_, 0, v_a_4614_);
v___x_4619_ = v_reuseFailAlloc_4620_;
goto v_reusejp_4618_;
}
v_reusejp_4618_:
{
return v___x_4619_;
}
}
}
}
else
{
lean_object* v_a_4622_; lean_object* v___x_4624_; uint8_t v_isShared_4625_; uint8_t v_isSharedCheck_4629_; 
lean_dec_ref(v_reflectionResult_4588_);
lean_dec_ref(v_ctx_4587_);
v_a_4622_ = lean_ctor_get(v___x_4600_, 0);
v_isSharedCheck_4629_ = !lean_is_exclusive(v___x_4600_);
if (v_isSharedCheck_4629_ == 0)
{
v___x_4624_ = v___x_4600_;
v_isShared_4625_ = v_isSharedCheck_4629_;
goto v_resetjp_4623_;
}
else
{
lean_inc(v_a_4622_);
lean_dec(v___x_4600_);
v___x_4624_ = lean_box(0);
v_isShared_4625_ = v_isSharedCheck_4629_;
goto v_resetjp_4623_;
}
v_resetjp_4623_:
{
lean_object* v___x_4627_; 
if (v_isShared_4625_ == 0)
{
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
return v___x_4627_;
}
}
}
}
else
{
lean_object* v_config_4630_; lean_object* v_lratPath_4631_; uint8_t v_trimProofs_4632_; lean_object* v_inheritedTraceOptions_4633_; lean_object* v___f_4634_; lean_object* v___x_4635_; lean_object* v___x_4636_; lean_object* v___x_4637_; uint8_t v___x_4638_; lean_object* v___y_4640_; lean_object* v___y_4641_; lean_object* v_a_4642_; lean_object* v___y_4655_; lean_object* v___y_4656_; lean_object* v_a_4657_; lean_object* v___y_4660_; lean_object* v___y_4661_; lean_object* v_a_4662_; lean_object* v___y_4672_; lean_object* v___y_4673_; lean_object* v_a_4674_; 
v_config_4630_ = lean_ctor_get(v_ctx_4587_, 5);
v_lratPath_4631_ = lean_ctor_get(v_ctx_4587_, 4);
v_trimProofs_4632_ = lean_ctor_get_uint8(v_config_4630_, sizeof(void*)*2);
v_inheritedTraceOptions_4633_ = lean_ctor_get(v_toCold_4594_, 11);
v___f_4634_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___closed__0));
v___x_4635_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
v___x_4636_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
v___x_4637_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_4638_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4633_, v_options_4595_, v___x_4637_);
if (v___x_4638_ == 0)
{
lean_object* v___x_4727_; uint8_t v___x_4728_; 
v___x_4727_ = l_Lean_trace_profiler;
v___x_4728_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_4595_, v___x_4727_);
if (v___x_4728_ == 0)
{
lean_object* v___x_4729_; 
v___x_4729_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_4631_, v_trimProofs_4632_, v_a_4591_, v_a_4592_);
if (lean_obj_tag(v___x_4729_) == 0)
{
lean_object* v_a_4730_; lean_object* v___x_4731_; 
v_a_4730_ = lean_ctor_get(v___x_4729_, 0);
lean_inc(v_a_4730_);
lean_dec_ref_known(v___x_4729_, 1);
v___x_4731_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_4730_, v_ctx_4587_, v_reflectionResult_4588_, v_a_4589_, v_a_4590_, v_a_4591_, v_a_4592_);
if (lean_obj_tag(v___x_4731_) == 0)
{
lean_object* v_a_4732_; lean_object* v___x_4734_; uint8_t v_isShared_4735_; uint8_t v_isSharedCheck_4742_; 
v_a_4732_ = lean_ctor_get(v___x_4731_, 0);
v_isSharedCheck_4742_ = !lean_is_exclusive(v___x_4731_);
if (v_isSharedCheck_4742_ == 0)
{
v___x_4734_ = v___x_4731_;
v_isShared_4735_ = v_isSharedCheck_4742_;
goto v_resetjp_4733_;
}
else
{
lean_inc(v_a_4732_);
lean_dec(v___x_4731_);
v___x_4734_ = lean_box(0);
v_isShared_4735_ = v_isSharedCheck_4742_;
goto v_resetjp_4733_;
}
v_resetjp_4733_:
{
lean_object* v___x_4736_; lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4740_; 
v___x_4736_ = lean_box(0);
v___x_4737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4737_, 0, v_a_4732_);
lean_ctor_set(v___x_4737_, 1, v___x_4736_);
v___x_4738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4738_, 0, v___x_4737_);
if (v_isShared_4735_ == 0)
{
lean_ctor_set(v___x_4734_, 0, v___x_4738_);
v___x_4740_ = v___x_4734_;
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
return v___x_4740_;
}
}
}
else
{
lean_object* v_a_4743_; lean_object* v___x_4745_; uint8_t v_isShared_4746_; uint8_t v_isSharedCheck_4750_; 
v_a_4743_ = lean_ctor_get(v___x_4731_, 0);
v_isSharedCheck_4750_ = !lean_is_exclusive(v___x_4731_);
if (v_isSharedCheck_4750_ == 0)
{
v___x_4745_ = v___x_4731_;
v_isShared_4746_ = v_isSharedCheck_4750_;
goto v_resetjp_4744_;
}
else
{
lean_inc(v_a_4743_);
lean_dec(v___x_4731_);
v___x_4745_ = lean_box(0);
v_isShared_4746_ = v_isSharedCheck_4750_;
goto v_resetjp_4744_;
}
v_resetjp_4744_:
{
lean_object* v___x_4748_; 
if (v_isShared_4746_ == 0)
{
v___x_4748_ = v___x_4745_;
goto v_reusejp_4747_;
}
else
{
lean_object* v_reuseFailAlloc_4749_; 
v_reuseFailAlloc_4749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4749_, 0, v_a_4743_);
v___x_4748_ = v_reuseFailAlloc_4749_;
goto v_reusejp_4747_;
}
v_reusejp_4747_:
{
return v___x_4748_;
}
}
}
}
else
{
lean_object* v_a_4751_; lean_object* v___x_4753_; uint8_t v_isShared_4754_; uint8_t v_isSharedCheck_4758_; 
lean_dec_ref(v_reflectionResult_4588_);
lean_dec_ref(v_ctx_4587_);
v_a_4751_ = lean_ctor_get(v___x_4729_, 0);
v_isSharedCheck_4758_ = !lean_is_exclusive(v___x_4729_);
if (v_isSharedCheck_4758_ == 0)
{
v___x_4753_ = v___x_4729_;
v_isShared_4754_ = v_isSharedCheck_4758_;
goto v_resetjp_4752_;
}
else
{
lean_inc(v_a_4751_);
lean_dec(v___x_4729_);
v___x_4753_ = lean_box(0);
v_isShared_4754_ = v_isSharedCheck_4758_;
goto v_resetjp_4752_;
}
v_resetjp_4752_:
{
lean_object* v___x_4756_; 
if (v_isShared_4754_ == 0)
{
v___x_4756_ = v___x_4753_;
goto v_reusejp_4755_;
}
else
{
lean_object* v_reuseFailAlloc_4757_; 
v_reuseFailAlloc_4757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4757_, 0, v_a_4751_);
v___x_4756_ = v_reuseFailAlloc_4757_;
goto v_reusejp_4755_;
}
v_reusejp_4755_:
{
return v___x_4756_;
}
}
}
}
else
{
goto v___jp_4676_;
}
}
else
{
goto v___jp_4676_;
}
v___jp_4639_:
{
lean_object* v___x_4643_; double v___x_4644_; double v___x_4645_; double v___x_4646_; double v___x_4647_; double v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; 
v___x_4643_ = lean_io_mono_nanos_now();
v___x_4644_ = lean_float_of_nat(v___y_4641_);
v___x_4645_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4646_ = lean_float_div(v___x_4644_, v___x_4645_);
v___x_4647_ = lean_float_of_nat(v___x_4643_);
v___x_4648_ = lean_float_div(v___x_4647_, v___x_4645_);
v___x_4649_ = lean_box_float(v___x_4646_);
v___x_4650_ = lean_box_float(v___x_4648_);
v___x_4651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4651_, 0, v___x_4649_);
lean_ctor_set(v___x_4651_, 1, v___x_4650_);
v___x_4652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4652_, 0, v_a_4642_);
lean_ctor_set(v___x_4652_, 1, v___x_4651_);
v___x_4653_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(v___x_4635_, v_hasTrace_4596_, v___x_4636_, v_options_4595_, v___x_4638_, v___y_4640_, v___f_4634_, v___x_4652_, v_a_4589_, v_a_4590_, v_a_4591_, v_a_4592_);
return v___x_4653_;
}
v___jp_4654_:
{
lean_object* v___x_4658_; 
v___x_4658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4658_, 0, v_a_4657_);
v___y_4640_ = v___y_4655_;
v___y_4641_ = v___y_4656_;
v_a_4642_ = v___x_4658_;
goto v___jp_4639_;
}
v___jp_4659_:
{
lean_object* v___x_4663_; double v___x_4664_; double v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; 
v___x_4663_ = lean_io_get_num_heartbeats();
v___x_4664_ = lean_float_of_nat(v___y_4661_);
v___x_4665_ = lean_float_of_nat(v___x_4663_);
v___x_4666_ = lean_box_float(v___x_4664_);
v___x_4667_ = lean_box_float(v___x_4665_);
v___x_4668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4668_, 0, v___x_4666_);
lean_ctor_set(v___x_4668_, 1, v___x_4667_);
v___x_4669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4669_, 0, v_a_4662_);
lean_ctor_set(v___x_4669_, 1, v___x_4668_);
v___x_4670_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(v___x_4635_, v_hasTrace_4596_, v___x_4636_, v_options_4595_, v___x_4638_, v___y_4660_, v___f_4634_, v___x_4669_, v_a_4589_, v_a_4590_, v_a_4591_, v_a_4592_);
return v___x_4670_;
}
v___jp_4671_:
{
lean_object* v___x_4675_; 
v___x_4675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4675_, 0, v_a_4674_);
v___y_4660_ = v___y_4672_;
v___y_4661_ = v___y_4673_;
v_a_4662_ = v___x_4675_;
goto v___jp_4659_;
}
v___jp_4676_:
{
lean_object* v___x_4677_; lean_object* v_a_4678_; lean_object* v___x_4679_; uint8_t v___x_4680_; 
v___x_4677_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_4592_);
v_a_4678_ = lean_ctor_get(v___x_4677_, 0);
lean_inc(v_a_4678_);
lean_dec_ref(v___x_4677_);
v___x_4679_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4680_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_4595_, v___x_4679_);
if (v___x_4680_ == 0)
{
lean_object* v___x_4681_; lean_object* v___x_4682_; 
v___x_4681_ = lean_io_mono_nanos_now();
v___x_4682_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_4631_, v_trimProofs_4632_, v_a_4591_, v_a_4592_);
if (lean_obj_tag(v___x_4682_) == 0)
{
lean_object* v_a_4683_; lean_object* v___x_4685_; uint8_t v_isShared_4686_; uint8_t v_isSharedCheck_4702_; 
v_a_4683_ = lean_ctor_get(v___x_4682_, 0);
v_isSharedCheck_4702_ = !lean_is_exclusive(v___x_4682_);
if (v_isSharedCheck_4702_ == 0)
{
v___x_4685_ = v___x_4682_;
v_isShared_4686_ = v_isSharedCheck_4702_;
goto v_resetjp_4684_;
}
else
{
lean_inc(v_a_4683_);
lean_dec(v___x_4682_);
v___x_4685_ = lean_box(0);
v_isShared_4686_ = v_isSharedCheck_4702_;
goto v_resetjp_4684_;
}
v_resetjp_4684_:
{
lean_object* v___x_4687_; 
v___x_4687_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_4683_, v_ctx_4587_, v_reflectionResult_4588_, v_a_4589_, v_a_4590_, v_a_4591_, v_a_4592_);
if (lean_obj_tag(v___x_4687_) == 0)
{
lean_object* v_a_4688_; lean_object* v___x_4690_; uint8_t v_isShared_4691_; uint8_t v_isSharedCheck_4700_; 
v_a_4688_ = lean_ctor_get(v___x_4687_, 0);
v_isSharedCheck_4700_ = !lean_is_exclusive(v___x_4687_);
if (v_isSharedCheck_4700_ == 0)
{
v___x_4690_ = v___x_4687_;
v_isShared_4691_ = v_isSharedCheck_4700_;
goto v_resetjp_4689_;
}
else
{
lean_inc(v_a_4688_);
lean_dec(v___x_4687_);
v___x_4690_ = lean_box(0);
v_isShared_4691_ = v_isSharedCheck_4700_;
goto v_resetjp_4689_;
}
v_resetjp_4689_:
{
lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4695_; 
v___x_4692_ = lean_box(0);
v___x_4693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4693_, 0, v_a_4688_);
lean_ctor_set(v___x_4693_, 1, v___x_4692_);
if (v_isShared_4691_ == 0)
{
lean_ctor_set_tag(v___x_4690_, 1);
lean_ctor_set(v___x_4690_, 0, v___x_4693_);
v___x_4695_ = v___x_4690_;
goto v_reusejp_4694_;
}
else
{
lean_object* v_reuseFailAlloc_4699_; 
v_reuseFailAlloc_4699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4699_, 0, v___x_4693_);
v___x_4695_ = v_reuseFailAlloc_4699_;
goto v_reusejp_4694_;
}
v_reusejp_4694_:
{
lean_object* v___x_4697_; 
if (v_isShared_4686_ == 0)
{
lean_ctor_set_tag(v___x_4685_, 1);
lean_ctor_set(v___x_4685_, 0, v___x_4695_);
v___x_4697_ = v___x_4685_;
goto v_reusejp_4696_;
}
else
{
lean_object* v_reuseFailAlloc_4698_; 
v_reuseFailAlloc_4698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4698_, 0, v___x_4695_);
v___x_4697_ = v_reuseFailAlloc_4698_;
goto v_reusejp_4696_;
}
v_reusejp_4696_:
{
v___y_4640_ = v_a_4678_;
v___y_4641_ = v___x_4681_;
v_a_4642_ = v___x_4697_;
goto v___jp_4639_;
}
}
}
}
else
{
lean_object* v_a_4701_; 
lean_del_object(v___x_4685_);
v_a_4701_ = lean_ctor_get(v___x_4687_, 0);
lean_inc(v_a_4701_);
lean_dec_ref_known(v___x_4687_, 1);
v___y_4655_ = v_a_4678_;
v___y_4656_ = v___x_4681_;
v_a_4657_ = v_a_4701_;
goto v___jp_4654_;
}
}
}
else
{
lean_object* v_a_4703_; 
lean_dec_ref(v_reflectionResult_4588_);
lean_dec_ref(v_ctx_4587_);
v_a_4703_ = lean_ctor_get(v___x_4682_, 0);
lean_inc(v_a_4703_);
lean_dec_ref_known(v___x_4682_, 1);
v___y_4655_ = v_a_4678_;
v___y_4656_ = v___x_4681_;
v_a_4657_ = v_a_4703_;
goto v___jp_4654_;
}
}
else
{
lean_object* v___x_4704_; lean_object* v___x_4705_; 
v___x_4704_ = lean_io_get_num_heartbeats();
v___x_4705_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_4631_, v_trimProofs_4632_, v_a_4591_, v_a_4592_);
if (lean_obj_tag(v___x_4705_) == 0)
{
lean_object* v_a_4706_; lean_object* v___x_4708_; uint8_t v_isShared_4709_; uint8_t v_isSharedCheck_4725_; 
v_a_4706_ = lean_ctor_get(v___x_4705_, 0);
v_isSharedCheck_4725_ = !lean_is_exclusive(v___x_4705_);
if (v_isSharedCheck_4725_ == 0)
{
v___x_4708_ = v___x_4705_;
v_isShared_4709_ = v_isSharedCheck_4725_;
goto v_resetjp_4707_;
}
else
{
lean_inc(v_a_4706_);
lean_dec(v___x_4705_);
v___x_4708_ = lean_box(0);
v_isShared_4709_ = v_isSharedCheck_4725_;
goto v_resetjp_4707_;
}
v_resetjp_4707_:
{
lean_object* v___x_4710_; 
v___x_4710_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_4706_, v_ctx_4587_, v_reflectionResult_4588_, v_a_4589_, v_a_4590_, v_a_4591_, v_a_4592_);
if (lean_obj_tag(v___x_4710_) == 0)
{
lean_object* v_a_4711_; lean_object* v___x_4713_; uint8_t v_isShared_4714_; uint8_t v_isSharedCheck_4723_; 
v_a_4711_ = lean_ctor_get(v___x_4710_, 0);
v_isSharedCheck_4723_ = !lean_is_exclusive(v___x_4710_);
if (v_isSharedCheck_4723_ == 0)
{
v___x_4713_ = v___x_4710_;
v_isShared_4714_ = v_isSharedCheck_4723_;
goto v_resetjp_4712_;
}
else
{
lean_inc(v_a_4711_);
lean_dec(v___x_4710_);
v___x_4713_ = lean_box(0);
v_isShared_4714_ = v_isSharedCheck_4723_;
goto v_resetjp_4712_;
}
v_resetjp_4712_:
{
lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4718_; 
v___x_4715_ = lean_box(0);
v___x_4716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4716_, 0, v_a_4711_);
lean_ctor_set(v___x_4716_, 1, v___x_4715_);
if (v_isShared_4714_ == 0)
{
lean_ctor_set_tag(v___x_4713_, 1);
lean_ctor_set(v___x_4713_, 0, v___x_4716_);
v___x_4718_ = v___x_4713_;
goto v_reusejp_4717_;
}
else
{
lean_object* v_reuseFailAlloc_4722_; 
v_reuseFailAlloc_4722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4722_, 0, v___x_4716_);
v___x_4718_ = v_reuseFailAlloc_4722_;
goto v_reusejp_4717_;
}
v_reusejp_4717_:
{
lean_object* v___x_4720_; 
if (v_isShared_4709_ == 0)
{
lean_ctor_set_tag(v___x_4708_, 1);
lean_ctor_set(v___x_4708_, 0, v___x_4718_);
v___x_4720_ = v___x_4708_;
goto v_reusejp_4719_;
}
else
{
lean_object* v_reuseFailAlloc_4721_; 
v_reuseFailAlloc_4721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4721_, 0, v___x_4718_);
v___x_4720_ = v_reuseFailAlloc_4721_;
goto v_reusejp_4719_;
}
v_reusejp_4719_:
{
v___y_4660_ = v_a_4678_;
v___y_4661_ = v___x_4704_;
v_a_4662_ = v___x_4720_;
goto v___jp_4659_;
}
}
}
}
else
{
lean_object* v_a_4724_; 
lean_del_object(v___x_4708_);
v_a_4724_ = lean_ctor_get(v___x_4710_, 0);
lean_inc(v_a_4724_);
lean_dec_ref_known(v___x_4710_, 1);
v___y_4672_ = v_a_4678_;
v___y_4673_ = v___x_4704_;
v_a_4674_ = v_a_4724_;
goto v___jp_4671_;
}
}
}
else
{
lean_object* v_a_4726_; 
lean_dec_ref(v_reflectionResult_4588_);
lean_dec_ref(v_ctx_4587_);
v_a_4726_ = lean_ctor_get(v___x_4705_, 0);
lean_inc(v_a_4726_);
lean_dec_ref_known(v___x_4705_, 1);
v___y_4672_ = v_a_4678_;
v___y_4673_ = v___x_4704_;
v_a_4674_ = v_a_4726_;
goto v___jp_4671_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___boxed(lean_object* v_ctx_4759_, lean_object* v_reflectionResult_4760_, lean_object* v_a_4761_, lean_object* v_a_4762_, lean_object* v_a_4763_, lean_object* v_a_4764_, lean_object* v_a_4765_){
_start:
{
lean_object* v_res_4766_; 
v_res_4766_ = l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg(v_ctx_4759_, v_reflectionResult_4760_, v_a_4761_, v_a_4762_, v_a_4763_, v_a_4764_);
lean_dec(v_a_4764_);
lean_dec_ref(v_a_4763_);
lean_dec(v_a_4762_);
lean_dec_ref(v_a_4761_);
return v_res_4766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker(lean_object* v_ctx_4767_, lean_object* v_x_4768_, lean_object* v_reflectionResult_4769_, lean_object* v_x_4770_, lean_object* v_a_4771_, lean_object* v_a_4772_, lean_object* v_a_4773_, lean_object* v_a_4774_){
_start:
{
lean_object* v___x_4776_; 
v___x_4776_ = l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg(v_ctx_4767_, v_reflectionResult_4769_, v_a_4771_, v_a_4772_, v_a_4773_, v_a_4774_);
return v___x_4776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___boxed(lean_object* v_ctx_4777_, lean_object* v_x_4778_, lean_object* v_reflectionResult_4779_, lean_object* v_x_4780_, lean_object* v_a_4781_, lean_object* v_a_4782_, lean_object* v_a_4783_, lean_object* v_a_4784_, lean_object* v_a_4785_){
_start:
{
lean_object* v_res_4786_; 
v_res_4786_ = l_Lean_Meta_Tactic_BVDecide_lratChecker(v_ctx_4777_, v_x_4778_, v_reflectionResult_4779_, v_x_4780_, v_a_4781_, v_a_4782_, v_a_4783_, v_a_4784_);
lean_dec(v_a_4784_);
lean_dec_ref(v_a_4783_);
lean_dec(v_a_4782_);
lean_dec_ref(v_a_4781_);
lean_dec_ref(v_x_4780_);
lean_dec(v_x_4778_);
return v_res_4786_;
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
