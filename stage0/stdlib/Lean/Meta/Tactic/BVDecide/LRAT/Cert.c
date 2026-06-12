// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.LRAT.Cert
// Imports: public import Std.Tactic.BVDecide.LRAT.Checker public import Lean.CoreM public import Std.Tactic.BVDecide.Syntax import Lean.Meta.Tactic.BVDecide.LRAT.Trim import Std.Tactic.BVDecide.LRAT.Parser import Lean.Meta.Tactic.BVDecide.External
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_parseLRATProof(lean_object*);
extern lean_object* l_Lean_instToExprNat;
lean_object* l_Lean_instToExprArrayOfToLevel___redArg(lean_object*, lean_object*);
lean_object* l_Lean_instToExprProdOfToLevel___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instToExprInt;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_TraceResult_toEmoji(uint8_t);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
lean_object* l_IO_FS_readBinFile(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_io_get_num_heartbeats();
lean_object* lean_io_mono_nanos_now();
lean_object* l_IO_lazyPure___redArg(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_LRAT_trim(lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_CNF_dimacs(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_External_satQuery(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_put_str(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_flush(lean_object*);
lean_object* lean_io_create_tempfile();
lean_object* lean_io_remove_file(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Array"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__6;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__7;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__8_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__9_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__10;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "BVDecide"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LRAT"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Action"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__15_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "addEmpty"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__16_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__11_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__17_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__12_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__17_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__17_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__17_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__14_value),LEAN_SCALAR_PTR_LITERAL(93, 190, 57, 97, 43, 82, 204, 195)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__17_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__17_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__15_value),LEAN_SCALAR_PTR_LITERAL(252, 170, 87, 126, 210, 40, 34, 60)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__17_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__16_value),LEAN_SCALAR_PTR_LITERAL(104, 109, 74, 91, 62, 109, 218, 23)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__17_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__2_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__18_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__19;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "List"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__20_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "toArray"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__21_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__20_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__22_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__21_value),LEAN_SCALAR_PTR_LITERAL(225, 54, 189, 64, 249, 49, 198, 116)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__22 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__22_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__23;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "nil"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__24 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__24_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__20_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__25_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__24_value),LEAN_SCALAR_PTR_LITERAL(90, 150, 134, 113, 145, 38, 173, 251)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__25 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__25_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__26;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__27;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cons"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__28 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__28_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__20_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__29_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__28_value),LEAN_SCALAR_PTR_LITERAL(98, 170, 59, 223, 79, 132, 139, 119)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__29 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__29_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__30;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__31;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "addRup"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__32 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__32_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__11_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__33_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__33_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__12_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__33_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__33_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__33_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__33_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__14_value),LEAN_SCALAR_PTR_LITERAL(93, 190, 57, 97, 43, 82, 204, 195)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__33_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__33_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__15_value),LEAN_SCALAR_PTR_LITERAL(252, 170, 87, 126, 210, 40, 34, 60)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__33_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__32_value),LEAN_SCALAR_PTR_LITERAL(165, 250, 224, 102, 206, 35, 100, 254)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__33 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__33_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__34;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__35;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__36;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__37;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "addRat"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__38 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__38_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__11_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__39_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__39_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__12_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__39_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__39_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__39_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__39_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__14_value),LEAN_SCALAR_PTR_LITERAL(93, 190, 57, 97, 43, 82, 204, 195)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__39_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__39_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__15_value),LEAN_SCALAR_PTR_LITERAL(252, 170, 87, 126, 210, 40, 34, 60)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__39_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__38_value),LEAN_SCALAR_PTR_LITERAL(126, 188, 16, 206, 14, 241, 53, 87)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__39 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__39_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__40;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__41 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__41_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__41_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__42 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__42_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__43;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Prod"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__44 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__44_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__45 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__45_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__46_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__44_value),LEAN_SCALAR_PTR_LITERAL(121, 119, 164, 206, 221, 118, 48, 212)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__46_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__45_value),LEAN_SCALAR_PTR_LITERAL(117, 121, 37, 123, 104, 28, 189, 89)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__46 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__46_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__47;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__48;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__44_value),LEAN_SCALAR_PTR_LITERAL(121, 119, 164, 206, 221, 118, 48, 212)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__49 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__49_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__50_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__50;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__51;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__52_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__52;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__53_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__53;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__54 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__54_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__55_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__41_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__55_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__54_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__55 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__55_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__56_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__56;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__57 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__57_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__58_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__41_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__58_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__57_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__58 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__58_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__59_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__59;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "del"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__60 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__60_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__61_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__11_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__61_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__61_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__12_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__61_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__61_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__61_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__61_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__14_value),LEAN_SCALAR_PTR_LITERAL(93, 190, 57, 97, 43, 82, 204, 195)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__61_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__61_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__15_value),LEAN_SCALAR_PTR_LITERAL(252, 170, 87, 126, 210, 40, 34, 60)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__61_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__60_value),LEAN_SCALAR_PTR_LITERAL(104, 230, 17, 1, 168, 25, 208, 83)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__61 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__61_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__62_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__62;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__2;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "IntAction"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__11_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__12_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__14_value),LEAN_SCALAR_PTR_LITERAL(93, 190, 57, 97, 43, 82, 204, 195)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__4_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__3_value),LEAN_SCALAR_PTR_LITERAL(90, 57, 146, 191, 99, 77, 0, 56)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__5;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__4___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Trimming LRAT proof"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__2___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Parsing LRAT file"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__3___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__3___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__3___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__3___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__3___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5_spec__7(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__6___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__4___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__4;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0___closed__0 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0___closed__0_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__1_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "sat"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__1_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__12_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__2_value),LEAN_SCALAR_PTR_LITERAL(174, 199, 37, 233, 64, 174, 173, 134)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__3_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__4_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "LRAT proof has "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__7 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__7_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = " steps after trimming"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__8 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = " steps before trimming"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__10 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__10_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "SAT solver produced invalid LRAT: "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__11 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__11_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__3___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__13 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__13_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Running SAT solver"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Obtaining LRAT certificate"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Serializing SAT problem to DIMACS file"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2_spec__4___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1_spec__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_runExternal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_runExternal___closed__0_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_runExternal___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_runExternal___closed__1_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_runExternal___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_runExternal___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__3(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_7_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__2));
v___x_8_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__1));
v___x_9_ = l_Lean_mkConst(v___x_8_, v___x_7_);
return v___x_9_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__6(void){
_start:
{
lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_13_ = lean_box(0);
v___x_14_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__5));
v___x_15_ = l_Lean_mkConst(v___x_14_, v___x_13_);
return v___x_15_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__7(void){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v_beta_18_; 
v___x_16_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__6);
v___x_17_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__3);
v_beta_18_ = l_Lean_Expr_app___override(v___x_17_, v___x_16_);
return v_beta_18_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__10(void){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v_alpha_24_; 
v___x_22_ = lean_box(0);
v___x_23_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__9));
v_alpha_24_ = l_Lean_mkConst(v___x_23_, v___x_22_);
return v_alpha_24_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__19(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_41_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__18));
v___x_42_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__17));
v___x_43_ = l_Lean_mkConst(v___x_42_, v___x_41_);
return v___x_43_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__23(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_49_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__2));
v___x_50_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__22));
v___x_51_ = l_Lean_mkConst(v___x_50_, v___x_49_);
return v___x_51_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__26(void){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_56_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__2));
v___x_57_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__25));
v___x_58_ = l_Lean_mkConst(v___x_57_, v___x_56_);
return v___x_58_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__27(void){
_start:
{
lean_object* v_alpha_59_; lean_object* v___x_60_; lean_object* v_nil_61_; 
v_alpha_59_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__10, &l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__10_once, _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__10);
v___x_60_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__26, &l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__26_once, _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__26);
v_nil_61_ = l_Lean_Expr_app___override(v___x_60_, v_alpha_59_);
return v_nil_61_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__30(void){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_66_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__2));
v___x_67_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__29));
v___x_68_ = l_Lean_mkConst(v___x_67_, v___x_66_);
return v___x_68_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__31(void){
_start:
{
lean_object* v_alpha_69_; lean_object* v___x_70_; lean_object* v_cons_71_; 
v_alpha_69_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__10, &l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__10_once, _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__10);
v___x_70_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__30, &l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__30_once, _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__30);
v_cons_71_ = l_Lean_Expr_app___override(v___x_70_, v_alpha_69_);
return v_cons_71_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__34(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_80_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__18));
v___x_81_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__33));
v___x_82_ = l_Lean_mkConst(v___x_81_, v___x_80_);
return v___x_82_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__35(void){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v_type_85_; 
v___x_83_ = lean_box(0);
v___x_84_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__5));
v_type_85_ = l_Lean_Expr_const___override(v___x_84_, v___x_83_);
return v_type_85_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__36(void){
_start:
{
lean_object* v_type_86_; lean_object* v___x_87_; lean_object* v_nil_88_; 
v_type_86_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__35, &l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__35_once, _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__35);
v___x_87_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__26, &l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__26_once, _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__26);
v_nil_88_ = l_Lean_Expr_app___override(v___x_87_, v_type_86_);
return v_nil_88_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__37(void){
_start:
{
lean_object* v_type_89_; lean_object* v___x_90_; lean_object* v_cons_91_; 
v_type_89_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__35, &l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__35_once, _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__35);
v___x_90_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__30, &l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__30_once, _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__30);
v_cons_91_ = l_Lean_Expr_app___override(v___x_90_, v_type_89_);
return v_cons_91_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__40(void){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_100_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__18));
v___x_101_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__39));
v___x_102_ = l_Lean_mkConst(v___x_101_, v___x_100_);
return v___x_102_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__43(void){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v_00_u03b2Type_108_; 
v___x_106_ = lean_box(0);
v___x_107_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__42));
v_00_u03b2Type_108_ = l_Lean_mkConst(v___x_107_, v___x_106_);
return v_00_u03b2Type_108_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__47(void){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_114_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__18));
v___x_115_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__46));
v___x_116_ = l_Lean_mkConst(v___x_115_, v___x_114_);
return v___x_116_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__48(void){
_start:
{
lean_object* v_alpha_117_; lean_object* v___x_118_; lean_object* v_00_u03b2Type_119_; 
v_alpha_117_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__10, &l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__10_once, _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__10);
v___x_118_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__3);
v_00_u03b2Type_119_ = l_Lean_Expr_app___override(v___x_118_, v_alpha_117_);
return v_00_u03b2Type_119_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__50(void){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_122_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__18));
v___x_123_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__49));
v___x_124_ = l_Lean_mkConst(v___x_123_, v___x_122_);
return v___x_124_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__51(void){
_start:
{
lean_object* v_00_u03b2Type_125_; lean_object* v_alpha_126_; lean_object* v___x_127_; lean_object* v_type_128_; 
v_00_u03b2Type_125_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__48, &l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__48_once, _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__48);
v_alpha_126_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__10, &l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__10_once, _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__10);
v___x_127_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__50, &l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__50_once, _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__50);
v_type_128_ = l_Lean_mkAppB(v___x_127_, v_alpha_126_, v_00_u03b2Type_125_);
return v_type_128_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__52(void){
_start:
{
lean_object* v_type_129_; lean_object* v___x_130_; lean_object* v_nil_131_; 
v_type_129_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__51, &l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__51_once, _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__51);
v___x_130_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__26, &l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__26_once, _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__26);
v_nil_131_ = l_Lean_Expr_app___override(v___x_130_, v_type_129_);
return v_nil_131_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__53(void){
_start:
{
lean_object* v_type_132_; lean_object* v___x_133_; lean_object* v_cons_134_; 
v_type_132_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__51, &l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__51_once, _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__51);
v___x_133_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__30, &l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__30_once, _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__30);
v_cons_134_ = l_Lean_Expr_app___override(v___x_133_, v_type_132_);
return v_cons_134_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__56(void){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_139_ = lean_box(0);
v___x_140_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__55));
v___x_141_ = l_Lean_mkConst(v___x_140_, v___x_139_);
return v___x_141_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__59(void){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_146_ = lean_box(0);
v___x_147_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__58));
v___x_148_ = l_Lean_mkConst(v___x_147_, v___x_146_);
return v___x_148_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__62(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_157_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__18));
v___x_158_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__61));
v___x_159_ = l_Lean_mkConst(v___x_158_, v___x_157_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0(lean_object* v___x_160_, lean_object* v___x_161_, lean_object* v___x_162_, lean_object* v_action_163_){
_start:
{
lean_object* v_beta_164_; lean_object* v_alpha_165_; 
v_beta_164_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__7, &l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__7_once, _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__7);
v_alpha_165_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__10, &l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__10_once, _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__10);
switch(lean_obj_tag(v_action_163_))
{
case 0:
{
lean_object* v_id_166_; lean_object* v_rupHints_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v_nil_171_; lean_object* v_cons_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
lean_dec_ref(v___x_162_);
lean_dec_ref(v___x_161_);
v_id_166_ = lean_ctor_get(v_action_163_, 0);
lean_inc(v_id_166_);
v_rupHints_167_ = lean_ctor_get(v_action_163_, 1);
lean_inc_ref(v_rupHints_167_);
lean_dec_ref_known(v_action_163_, 2);
v___x_168_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__19, &l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__19_once, _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__19);
v___x_169_ = l_Lean_mkNatLit(v_id_166_);
v___x_170_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__23, &l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__23_once, _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__23);
v_nil_171_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__27, &l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__27_once, _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__27);
v_cons_172_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__31, &l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__31_once, _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__31);
v___x_173_ = lean_array_to_list(v_rupHints_167_);
v___x_174_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux(lean_box(0), v___x_160_, v_nil_171_, v_cons_172_, v___x_173_);
v___x_175_ = l_Lean_mkAppB(v___x_170_, v_alpha_165_, v___x_174_);
v___x_176_ = l_Lean_mkApp4(v___x_168_, v_beta_164_, v_alpha_165_, v___x_169_, v___x_175_);
return v___x_176_;
}
case 1:
{
lean_object* v_id_177_; lean_object* v_c_178_; lean_object* v_rupHints_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v_type_182_; lean_object* v___x_183_; lean_object* v_nil_184_; lean_object* v_cons_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v_nil_189_; lean_object* v_cons_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
lean_dec_ref(v___x_162_);
v_id_177_ = lean_ctor_get(v_action_163_, 0);
lean_inc(v_id_177_);
v_c_178_ = lean_ctor_get(v_action_163_, 1);
lean_inc(v_c_178_);
v_rupHints_179_ = lean_ctor_get(v_action_163_, 2);
lean_inc_ref(v_rupHints_179_);
lean_dec_ref_known(v_action_163_, 3);
v___x_180_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__34, &l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__34_once, _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__34);
v___x_181_ = l_Lean_mkNatLit(v_id_177_);
v_type_182_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__35, &l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__35_once, _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__35);
v___x_183_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__23, &l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__23_once, _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__23);
v_nil_184_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__36, &l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__36_once, _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__36);
v_cons_185_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__37);
v___x_186_ = lean_array_to_list(v_c_178_);
v___x_187_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux(lean_box(0), v___x_161_, v_nil_184_, v_cons_185_, v___x_186_);
v___x_188_ = l_Lean_mkAppB(v___x_183_, v_type_182_, v___x_187_);
v_nil_189_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__27, &l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__27_once, _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__27);
v_cons_190_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__31, &l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__31_once, _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__31);
v___x_191_ = lean_array_to_list(v_rupHints_179_);
v___x_192_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux(lean_box(0), v___x_160_, v_nil_189_, v_cons_190_, v___x_191_);
v___x_193_ = l_Lean_mkAppB(v___x_183_, v_alpha_165_, v___x_192_);
v___x_194_ = l_Lean_mkApp5(v___x_180_, v_beta_164_, v_alpha_165_, v___x_181_, v___x_188_, v___x_193_);
return v___x_194_;
}
case 2:
{
lean_object* v_id_195_; lean_object* v_c_196_; lean_object* v_pivot_197_; lean_object* v_rupHints_198_; lean_object* v_ratHints_199_; lean_object* v___x_200_; lean_object* v_fst_201_; lean_object* v_snd_202_; lean_object* v_type_203_; lean_object* v_nil_204_; lean_object* v_cons_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v_00_u03b2Type_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___y_215_; uint8_t v___x_229_; 
v_id_195_ = lean_ctor_get(v_action_163_, 0);
lean_inc(v_id_195_);
v_c_196_ = lean_ctor_get(v_action_163_, 1);
lean_inc(v_c_196_);
v_pivot_197_ = lean_ctor_get(v_action_163_, 2);
lean_inc_ref(v_pivot_197_);
v_rupHints_198_ = lean_ctor_get(v_action_163_, 3);
lean_inc_ref(v_rupHints_198_);
v_ratHints_199_ = lean_ctor_get(v_action_163_, 4);
lean_inc_ref(v_ratHints_199_);
lean_dec_ref_known(v_action_163_, 5);
v___x_200_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__23, &l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__23_once, _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__23);
v_fst_201_ = lean_ctor_get(v_pivot_197_, 0);
lean_inc(v_fst_201_);
v_snd_202_ = lean_ctor_get(v_pivot_197_, 1);
lean_inc(v_snd_202_);
lean_dec_ref(v_pivot_197_);
v_type_203_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__35, &l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__35_once, _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__35);
v_nil_204_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__36, &l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__36_once, _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__36);
v_cons_205_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__37);
v___x_206_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__40, &l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__40_once, _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__40);
v___x_207_ = l_Lean_mkNatLit(v_id_195_);
v___x_208_ = lean_array_to_list(v_c_196_);
v___x_209_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux(lean_box(0), v___x_161_, v_nil_204_, v_cons_205_, v___x_208_);
v___x_210_ = l_Lean_mkAppB(v___x_200_, v_type_203_, v___x_209_);
v_00_u03b2Type_211_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__43, &l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__43_once, _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__43);
v___x_212_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__47, &l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__47_once, _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__47);
v___x_213_ = l_Lean_mkNatLit(v_fst_201_);
v___x_229_ = lean_unbox(v_snd_202_);
lean_dec(v_snd_202_);
if (v___x_229_ == 0)
{
lean_object* v___x_230_; 
v___x_230_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__56, &l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__56_once, _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__56);
v___y_215_ = v___x_230_;
goto v___jp_214_;
}
else
{
lean_object* v___x_231_; 
v___x_231_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__59, &l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__59_once, _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__59);
v___y_215_ = v___x_231_;
goto v___jp_214_;
}
v___jp_214_:
{
lean_object* v___x_216_; lean_object* v_nil_217_; lean_object* v_cons_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v_type_222_; lean_object* v_nil_223_; lean_object* v_cons_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
lean_inc_ref(v___y_215_);
v___x_216_ = l_Lean_mkApp4(v___x_212_, v_alpha_165_, v_00_u03b2Type_211_, v___x_213_, v___y_215_);
v_nil_217_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__27, &l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__27_once, _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__27);
v_cons_218_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__31, &l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__31_once, _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__31);
v___x_219_ = lean_array_to_list(v_rupHints_198_);
v___x_220_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux(lean_box(0), v___x_160_, v_nil_217_, v_cons_218_, v___x_219_);
v___x_221_ = l_Lean_mkAppB(v___x_200_, v_alpha_165_, v___x_220_);
v_type_222_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__51, &l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__51_once, _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__51);
v_nil_223_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__52, &l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__52_once, _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__52);
v_cons_224_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__53, &l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__53_once, _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__53);
v___x_225_ = lean_array_to_list(v_ratHints_199_);
v___x_226_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux(lean_box(0), v___x_162_, v_nil_223_, v_cons_224_, v___x_225_);
v___x_227_ = l_Lean_mkAppB(v___x_200_, v_type_222_, v___x_226_);
v___x_228_ = l_Lean_mkApp7(v___x_206_, v_beta_164_, v_alpha_165_, v___x_207_, v___x_210_, v___x_216_, v___x_221_, v___x_227_);
return v___x_228_;
}
}
default: 
{
lean_object* v_ids_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v_nil_235_; lean_object* v_cons_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
lean_dec_ref(v___x_162_);
lean_dec_ref(v___x_161_);
v_ids_232_ = lean_ctor_get(v_action_163_, 0);
lean_inc_ref(v_ids_232_);
lean_dec_ref_known(v_action_163_, 1);
v___x_233_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__62, &l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__62_once, _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__62);
v___x_234_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__23, &l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__23_once, _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__23);
v_nil_235_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__27, &l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__27_once, _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__27);
v_cons_236_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__31, &l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__31_once, _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__31);
v___x_237_ = lean_array_to_list(v_ids_232_);
v___x_238_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux(lean_box(0), v___x_160_, v_nil_235_, v_cons_236_, v___x_237_);
v___x_239_ = l_Lean_mkAppB(v___x_234_, v_alpha_165_, v___x_238_);
v___x_240_ = l_Lean_mkApp3(v___x_233_, v_beta_164_, v_alpha_165_, v___x_239_);
return v___x_240_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__0(void){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_241_ = l_Lean_instToExprNat;
v___x_242_ = lean_box(0);
v___x_243_ = l_Lean_instToExprArrayOfToLevel___redArg(v___x_242_, v___x_241_);
return v___x_243_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__1(void){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_244_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__0);
v___x_245_ = l_Lean_instToExprNat;
v___x_246_ = lean_box(0);
v___x_247_ = l_Lean_instToExprProdOfToLevel___redArg(v___x_246_, v___x_246_, v___x_245_, v___x_244_);
return v___x_247_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__2(void){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___f_251_; 
v___x_248_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__1);
v___x_249_ = l_Lean_instToExprInt;
v___x_250_ = l_Lean_instToExprNat;
v___f_251_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0), 4, 3);
lean_closure_set(v___f_251_, 0, v___x_250_);
lean_closure_set(v___f_251_, 1, v___x_249_);
lean_closure_set(v___f_251_, 2, v___x_248_);
return v___f_251_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__5(void){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_259_ = lean_box(0);
v___x_260_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__4));
v___x_261_ = l_Lean_mkConst(v___x_260_, v___x_259_);
return v___x_261_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__6(void){
_start:
{
lean_object* v___x_262_; lean_object* v___f_263_; lean_object* v___x_264_; 
v___x_262_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__5, &l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__5_once, _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__5);
v___f_263_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__2);
v___x_264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_264_, 0, v___f_263_);
lean_ctor_set(v___x_264_, 1, v___x_262_);
return v___x_264_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction(void){
_start:
{
lean_object* v___x_265_; 
v___x_265_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__6);
return v___x_265_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_266_ = lean_unsigned_to_nat(32u);
v___x_267_ = lean_mk_empty_array_with_capacity(v___x_266_);
v___x_268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
return v___x_268_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_269_ = ((size_t)5ULL);
v___x_270_ = lean_unsigned_to_nat(0u);
v___x_271_ = lean_unsigned_to_nat(32u);
v___x_272_ = lean_mk_empty_array_with_capacity(v___x_271_);
v___x_273_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg___closed__0);
v___x_274_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_274_, 0, v___x_273_);
lean_ctor_set(v___x_274_, 1, v___x_272_);
lean_ctor_set(v___x_274_, 2, v___x_270_);
lean_ctor_set(v___x_274_, 3, v___x_270_);
lean_ctor_set_usize(v___x_274_, 4, v___x_269_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg(lean_object* v___y_275_){
_start:
{
lean_object* v___x_277_; lean_object* v_traceState_278_; lean_object* v_traces_279_; lean_object* v___x_280_; lean_object* v_traceState_281_; lean_object* v_env_282_; lean_object* v_nextMacroScope_283_; lean_object* v_ngen_284_; lean_object* v_auxDeclNGen_285_; lean_object* v_cache_286_; lean_object* v_messages_287_; lean_object* v_infoState_288_; lean_object* v_snapshotTasks_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_308_; 
v___x_277_ = lean_st_ref_get(v___y_275_);
v_traceState_278_ = lean_ctor_get(v___x_277_, 4);
lean_inc_ref(v_traceState_278_);
lean_dec(v___x_277_);
v_traces_279_ = lean_ctor_get(v_traceState_278_, 0);
lean_inc_ref(v_traces_279_);
lean_dec_ref(v_traceState_278_);
v___x_280_ = lean_st_ref_take(v___y_275_);
v_traceState_281_ = lean_ctor_get(v___x_280_, 4);
v_env_282_ = lean_ctor_get(v___x_280_, 0);
v_nextMacroScope_283_ = lean_ctor_get(v___x_280_, 1);
v_ngen_284_ = lean_ctor_get(v___x_280_, 2);
v_auxDeclNGen_285_ = lean_ctor_get(v___x_280_, 3);
v_cache_286_ = lean_ctor_get(v___x_280_, 5);
v_messages_287_ = lean_ctor_get(v___x_280_, 6);
v_infoState_288_ = lean_ctor_get(v___x_280_, 7);
v_snapshotTasks_289_ = lean_ctor_get(v___x_280_, 8);
v_isSharedCheck_308_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_308_ == 0)
{
v___x_291_ = v___x_280_;
v_isShared_292_ = v_isSharedCheck_308_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_snapshotTasks_289_);
lean_inc(v_infoState_288_);
lean_inc(v_messages_287_);
lean_inc(v_cache_286_);
lean_inc(v_traceState_281_);
lean_inc(v_auxDeclNGen_285_);
lean_inc(v_ngen_284_);
lean_inc(v_nextMacroScope_283_);
lean_inc(v_env_282_);
lean_dec(v___x_280_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_308_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
uint64_t v_tid_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_306_; 
v_tid_293_ = lean_ctor_get_uint64(v_traceState_281_, sizeof(void*)*1);
v_isSharedCheck_306_ = !lean_is_exclusive(v_traceState_281_);
if (v_isSharedCheck_306_ == 0)
{
lean_object* v_unused_307_; 
v_unused_307_ = lean_ctor_get(v_traceState_281_, 0);
lean_dec(v_unused_307_);
v___x_295_ = v_traceState_281_;
v_isShared_296_ = v_isSharedCheck_306_;
goto v_resetjp_294_;
}
else
{
lean_dec(v_traceState_281_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_306_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_297_; lean_object* v___x_299_; 
v___x_297_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg___closed__1);
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 0, v___x_297_);
v___x_299_ = v___x_295_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v___x_297_);
lean_ctor_set_uint64(v_reuseFailAlloc_305_, sizeof(void*)*1, v_tid_293_);
v___x_299_ = v_reuseFailAlloc_305_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
lean_object* v___x_301_; 
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 4, v___x_299_);
v___x_301_ = v___x_291_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_env_282_);
lean_ctor_set(v_reuseFailAlloc_304_, 1, v_nextMacroScope_283_);
lean_ctor_set(v_reuseFailAlloc_304_, 2, v_ngen_284_);
lean_ctor_set(v_reuseFailAlloc_304_, 3, v_auxDeclNGen_285_);
lean_ctor_set(v_reuseFailAlloc_304_, 4, v___x_299_);
lean_ctor_set(v_reuseFailAlloc_304_, 5, v_cache_286_);
lean_ctor_set(v_reuseFailAlloc_304_, 6, v_messages_287_);
lean_ctor_set(v_reuseFailAlloc_304_, 7, v_infoState_288_);
lean_ctor_set(v_reuseFailAlloc_304_, 8, v_snapshotTasks_289_);
v___x_301_ = v_reuseFailAlloc_304_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = lean_st_ref_set(v___y_275_, v___x_301_);
v___x_303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_303_, 0, v_traces_279_);
return v___x_303_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg___boxed(lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg(v___y_309_);
lean_dec(v___y_309_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1(lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg(v___y_313_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___boxed(lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1(v___y_316_, v___y_317_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
return v_res_319_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(lean_object* v_opts_320_, lean_object* v_opt_321_){
_start:
{
lean_object* v_name_322_; lean_object* v_defValue_323_; lean_object* v_map_324_; lean_object* v___x_325_; 
v_name_322_ = lean_ctor_get(v_opt_321_, 0);
v_defValue_323_ = lean_ctor_get(v_opt_321_, 1);
v_map_324_ = lean_ctor_get(v_opts_320_, 0);
v___x_325_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_324_, v_name_322_);
if (lean_obj_tag(v___x_325_) == 0)
{
uint8_t v___x_326_; 
v___x_326_ = lean_unbox(v_defValue_323_);
return v___x_326_;
}
else
{
lean_object* v_val_327_; 
v_val_327_ = lean_ctor_get(v___x_325_, 0);
lean_inc(v_val_327_);
lean_dec_ref_known(v___x_325_, 1);
if (lean_obj_tag(v_val_327_) == 1)
{
uint8_t v_v_328_; 
v_v_328_ = lean_ctor_get_uint8(v_val_327_, 0);
lean_dec_ref_known(v_val_327_, 0);
return v_v_328_;
}
else
{
uint8_t v___x_329_; 
lean_dec(v_val_327_);
v___x_329_ = lean_unbox(v_defValue_323_);
return v___x_329_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2___boxed(lean_object* v_opts_330_, lean_object* v_opt_331_){
_start:
{
uint8_t v_res_332_; lean_object* v_r_333_; 
v_res_332_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_opts_330_, v_opt_331_);
lean_dec_ref(v_opt_331_);
lean_dec_ref(v_opts_330_);
v_r_333_ = lean_box(v_res_332_);
return v_r_333_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__4___redArg(lean_object* v_e_334_){
_start:
{
if (lean_obj_tag(v_e_334_) == 0)
{
lean_object* v_a_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_344_; 
v_a_336_ = lean_ctor_get(v_e_334_, 0);
v_isSharedCheck_344_ = !lean_is_exclusive(v_e_334_);
if (v_isSharedCheck_344_ == 0)
{
v___x_338_ = v_e_334_;
v_isShared_339_ = v_isSharedCheck_344_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_a_336_);
lean_dec(v_e_334_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_344_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_340_; lean_object* v___x_342_; 
v___x_340_ = lean_mk_io_user_error(v_a_336_);
if (v_isShared_339_ == 0)
{
lean_ctor_set_tag(v___x_338_, 1);
lean_ctor_set(v___x_338_, 0, v___x_340_);
v___x_342_ = v___x_338_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v___x_340_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
else
{
lean_object* v_a_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_352_; 
v_a_345_ = lean_ctor_get(v_e_334_, 0);
v_isSharedCheck_352_ = !lean_is_exclusive(v_e_334_);
if (v_isSharedCheck_352_ == 0)
{
v___x_347_ = v_e_334_;
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_a_345_);
lean_dec(v_e_334_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_350_; 
if (v_isShared_348_ == 0)
{
lean_ctor_set_tag(v___x_347_, 0);
v___x_350_ = v___x_347_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_a_345_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__4___redArg___boxed(lean_object* v_e_353_, lean_object* v_a_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__4___redArg(v_e_353_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__4(lean_object* v_00_u03b1_356_, lean_object* v_e_357_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__4___redArg(v_e_357_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__4___boxed(lean_object* v_00_u03b1_360_, lean_object* v_e_361_, lean_object* v_a_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__4(v_00_u03b1_360_, v_e_361_);
return v_res_363_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__0___closed__2(void){
_start:
{
lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_367_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__0___closed__1));
v___x_368_ = l_Lean_MessageData_ofFormat(v___x_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__0(lean_object* v_x_369_, lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__0___closed__2, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__0___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__0___closed__2);
v___x_374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_374_, 0, v___x_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__0___boxed(lean_object* v_x_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__0(v_x_375_, v___y_376_, v___y_377_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
lean_dec_ref(v_x_375_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__1(lean_object* v_a_380_, lean_object* v_x_381_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Std_Tactic_BVDecide_LRAT_parseLRATProof(v_a_380_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__2(lean_object* v_a_383_, lean_object* v_x_384_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l_Lean_Meta_Tactic_BVDecide_LRAT_trim(v_a_383_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__2___boxed(lean_object* v_a_386_, lean_object* v_x_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__2(v_a_386_, v_x_387_);
lean_dec_ref(v_a_386_);
return v_res_388_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__3___closed__2(void){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_392_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__3___closed__1));
v___x_393_ = l_Lean_MessageData_ofFormat(v___x_392_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__3(lean_object* v_x_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_398_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__3___closed__2, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__3___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__3___closed__2);
v___x_399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_399_, 0, v___x_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__3___boxed(lean_object* v_x_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__3(v_x_400_, v___y_401_, v___y_402_);
lean_dec(v___y_402_);
lean_dec_ref(v___y_401_);
lean_dec_ref(v_x_400_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5_spec__7(size_t v_sz_405_, size_t v_i_406_, lean_object* v_bs_407_){
_start:
{
uint8_t v___x_408_; 
v___x_408_ = lean_usize_dec_lt(v_i_406_, v_sz_405_);
if (v___x_408_ == 0)
{
return v_bs_407_;
}
else
{
lean_object* v_v_409_; lean_object* v_msg_410_; lean_object* v___x_411_; lean_object* v_bs_x27_412_; size_t v___x_413_; size_t v___x_414_; lean_object* v___x_415_; 
v_v_409_ = lean_array_uget_borrowed(v_bs_407_, v_i_406_);
v_msg_410_ = lean_ctor_get(v_v_409_, 1);
lean_inc_ref(v_msg_410_);
v___x_411_ = lean_unsigned_to_nat(0u);
v_bs_x27_412_ = lean_array_uset(v_bs_407_, v_i_406_, v___x_411_);
v___x_413_ = ((size_t)1ULL);
v___x_414_ = lean_usize_add(v_i_406_, v___x_413_);
v___x_415_ = lean_array_uset(v_bs_x27_412_, v_i_406_, v_msg_410_);
v_i_406_ = v___x_414_;
v_bs_407_ = v___x_415_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5_spec__7___boxed(lean_object* v_sz_417_, lean_object* v_i_418_, lean_object* v_bs_419_){
_start:
{
size_t v_sz_boxed_420_; size_t v_i_boxed_421_; lean_object* v_res_422_; 
v_sz_boxed_420_ = lean_unbox_usize(v_sz_417_);
lean_dec(v_sz_417_);
v_i_boxed_421_ = lean_unbox_usize(v_i_418_);
lean_dec(v_i_418_);
v_res_422_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5_spec__7(v_sz_boxed_420_, v_i_boxed_421_, v_bs_419_);
return v_res_422_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_423_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_424_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__0);
v___x_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_425_, 0, v___x_424_);
return v___x_425_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_426_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__1);
v___x_427_ = lean_unsigned_to_nat(0u);
v___x_428_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_428_, 0, v___x_427_);
lean_ctor_set(v___x_428_, 1, v___x_427_);
lean_ctor_set(v___x_428_, 2, v___x_427_);
lean_ctor_set(v___x_428_, 3, v___x_427_);
lean_ctor_set(v___x_428_, 4, v___x_426_);
lean_ctor_set(v___x_428_, 5, v___x_426_);
lean_ctor_set(v___x_428_, 6, v___x_426_);
lean_ctor_set(v___x_428_, 7, v___x_426_);
lean_ctor_set(v___x_428_, 8, v___x_426_);
lean_ctor_set(v___x_428_, 9, v___x_426_);
return v___x_428_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_429_ = lean_unsigned_to_nat(32u);
v___x_430_ = lean_mk_empty_array_with_capacity(v___x_429_);
v___x_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_431_, 0, v___x_430_);
return v___x_431_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_432_ = ((size_t)5ULL);
v___x_433_ = lean_unsigned_to_nat(0u);
v___x_434_ = lean_unsigned_to_nat(32u);
v___x_435_ = lean_mk_empty_array_with_capacity(v___x_434_);
v___x_436_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__3);
v___x_437_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_437_, 0, v___x_436_);
lean_ctor_set(v___x_437_, 1, v___x_435_);
lean_ctor_set(v___x_437_, 2, v___x_433_);
lean_ctor_set(v___x_437_, 3, v___x_433_);
lean_ctor_set_usize(v___x_437_, 4, v___x_432_);
return v___x_437_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_438_ = lean_box(1);
v___x_439_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__4);
v___x_440_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__1);
v___x_441_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_441_, 0, v___x_440_);
lean_ctor_set(v___x_441_, 1, v___x_439_);
lean_ctor_set(v___x_441_, 2, v___x_438_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0(lean_object* v_msgData_442_, lean_object* v___y_443_, lean_object* v___y_444_){
_start:
{
lean_object* v___x_446_; lean_object* v_env_447_; lean_object* v_options_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_446_ = lean_st_ref_get(v___y_444_);
v_env_447_ = lean_ctor_get(v___x_446_, 0);
lean_inc_ref(v_env_447_);
lean_dec(v___x_446_);
v_options_448_ = lean_ctor_get(v___y_443_, 2);
v___x_449_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__2);
v___x_450_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_448_);
v___x_451_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_451_, 0, v_env_447_);
lean_ctor_set(v___x_451_, 1, v___x_449_);
lean_ctor_set(v___x_451_, 2, v___x_450_);
lean_ctor_set(v___x_451_, 3, v_options_448_);
v___x_452_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_452_, 0, v___x_451_);
lean_ctor_set(v___x_452_, 1, v_msgData_442_);
v___x_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_453_, 0, v___x_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___boxed(lean_object* v_msgData_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0(v_msgData_454_, v___y_455_, v___y_456_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5(lean_object* v_oldTraces_459_, lean_object* v_data_460_, lean_object* v_ref_461_, lean_object* v_msg_462_, lean_object* v___y_463_, lean_object* v___y_464_){
_start:
{
lean_object* v_fileName_466_; lean_object* v_fileMap_467_; lean_object* v_options_468_; lean_object* v_currRecDepth_469_; lean_object* v_maxRecDepth_470_; lean_object* v_ref_471_; lean_object* v_currNamespace_472_; lean_object* v_openDecls_473_; lean_object* v_initHeartbeats_474_; lean_object* v_maxHeartbeats_475_; lean_object* v_quotContext_476_; lean_object* v_currMacroScope_477_; uint8_t v_diag_478_; lean_object* v_cancelTk_x3f_479_; uint8_t v_suppressElabErrors_480_; lean_object* v_inheritedTraceOptions_481_; lean_object* v___x_482_; lean_object* v_traceState_483_; lean_object* v_traces_484_; lean_object* v_ref_485_; lean_object* v___x_486_; lean_object* v___x_487_; size_t v_sz_488_; size_t v___x_489_; lean_object* v___x_490_; lean_object* v_msg_491_; lean_object* v___x_492_; lean_object* v_a_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_530_; 
v_fileName_466_ = lean_ctor_get(v___y_463_, 0);
v_fileMap_467_ = lean_ctor_get(v___y_463_, 1);
v_options_468_ = lean_ctor_get(v___y_463_, 2);
v_currRecDepth_469_ = lean_ctor_get(v___y_463_, 3);
v_maxRecDepth_470_ = lean_ctor_get(v___y_463_, 4);
v_ref_471_ = lean_ctor_get(v___y_463_, 5);
v_currNamespace_472_ = lean_ctor_get(v___y_463_, 6);
v_openDecls_473_ = lean_ctor_get(v___y_463_, 7);
v_initHeartbeats_474_ = lean_ctor_get(v___y_463_, 8);
v_maxHeartbeats_475_ = lean_ctor_get(v___y_463_, 9);
v_quotContext_476_ = lean_ctor_get(v___y_463_, 10);
v_currMacroScope_477_ = lean_ctor_get(v___y_463_, 11);
v_diag_478_ = lean_ctor_get_uint8(v___y_463_, sizeof(void*)*14);
v_cancelTk_x3f_479_ = lean_ctor_get(v___y_463_, 12);
v_suppressElabErrors_480_ = lean_ctor_get_uint8(v___y_463_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_481_ = lean_ctor_get(v___y_463_, 13);
v___x_482_ = lean_st_ref_get(v___y_464_);
v_traceState_483_ = lean_ctor_get(v___x_482_, 4);
lean_inc_ref(v_traceState_483_);
lean_dec(v___x_482_);
v_traces_484_ = lean_ctor_get(v_traceState_483_, 0);
lean_inc_ref(v_traces_484_);
lean_dec_ref(v_traceState_483_);
v_ref_485_ = l_Lean_replaceRef(v_ref_461_, v_ref_471_);
lean_inc_ref(v_inheritedTraceOptions_481_);
lean_inc(v_cancelTk_x3f_479_);
lean_inc(v_currMacroScope_477_);
lean_inc(v_quotContext_476_);
lean_inc(v_maxHeartbeats_475_);
lean_inc(v_initHeartbeats_474_);
lean_inc(v_openDecls_473_);
lean_inc(v_currNamespace_472_);
lean_inc(v_maxRecDepth_470_);
lean_inc(v_currRecDepth_469_);
lean_inc_ref(v_options_468_);
lean_inc_ref(v_fileMap_467_);
lean_inc_ref(v_fileName_466_);
v___x_486_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_486_, 0, v_fileName_466_);
lean_ctor_set(v___x_486_, 1, v_fileMap_467_);
lean_ctor_set(v___x_486_, 2, v_options_468_);
lean_ctor_set(v___x_486_, 3, v_currRecDepth_469_);
lean_ctor_set(v___x_486_, 4, v_maxRecDepth_470_);
lean_ctor_set(v___x_486_, 5, v_ref_485_);
lean_ctor_set(v___x_486_, 6, v_currNamespace_472_);
lean_ctor_set(v___x_486_, 7, v_openDecls_473_);
lean_ctor_set(v___x_486_, 8, v_initHeartbeats_474_);
lean_ctor_set(v___x_486_, 9, v_maxHeartbeats_475_);
lean_ctor_set(v___x_486_, 10, v_quotContext_476_);
lean_ctor_set(v___x_486_, 11, v_currMacroScope_477_);
lean_ctor_set(v___x_486_, 12, v_cancelTk_x3f_479_);
lean_ctor_set(v___x_486_, 13, v_inheritedTraceOptions_481_);
lean_ctor_set_uint8(v___x_486_, sizeof(void*)*14, v_diag_478_);
lean_ctor_set_uint8(v___x_486_, sizeof(void*)*14 + 1, v_suppressElabErrors_480_);
v___x_487_ = l_Lean_PersistentArray_toArray___redArg(v_traces_484_);
lean_dec_ref(v_traces_484_);
v_sz_488_ = lean_array_size(v___x_487_);
v___x_489_ = ((size_t)0ULL);
v___x_490_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5_spec__7(v_sz_488_, v___x_489_, v___x_487_);
v_msg_491_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_491_, 0, v_data_460_);
lean_ctor_set(v_msg_491_, 1, v_msg_462_);
lean_ctor_set(v_msg_491_, 2, v___x_490_);
v___x_492_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0(v_msg_491_, v___x_486_, v___y_464_);
lean_dec_ref_known(v___x_486_, 14);
v_a_493_ = lean_ctor_get(v___x_492_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_530_ == 0)
{
v___x_495_ = v___x_492_;
v_isShared_496_ = v_isSharedCheck_530_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_a_493_);
lean_dec(v___x_492_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_530_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_497_; lean_object* v_traceState_498_; lean_object* v_env_499_; lean_object* v_nextMacroScope_500_; lean_object* v_ngen_501_; lean_object* v_auxDeclNGen_502_; lean_object* v_cache_503_; lean_object* v_messages_504_; lean_object* v_infoState_505_; lean_object* v_snapshotTasks_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_529_; 
v___x_497_ = lean_st_ref_take(v___y_464_);
v_traceState_498_ = lean_ctor_get(v___x_497_, 4);
v_env_499_ = lean_ctor_get(v___x_497_, 0);
v_nextMacroScope_500_ = lean_ctor_get(v___x_497_, 1);
v_ngen_501_ = lean_ctor_get(v___x_497_, 2);
v_auxDeclNGen_502_ = lean_ctor_get(v___x_497_, 3);
v_cache_503_ = lean_ctor_get(v___x_497_, 5);
v_messages_504_ = lean_ctor_get(v___x_497_, 6);
v_infoState_505_ = lean_ctor_get(v___x_497_, 7);
v_snapshotTasks_506_ = lean_ctor_get(v___x_497_, 8);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_529_ == 0)
{
v___x_508_ = v___x_497_;
v_isShared_509_ = v_isSharedCheck_529_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_snapshotTasks_506_);
lean_inc(v_infoState_505_);
lean_inc(v_messages_504_);
lean_inc(v_cache_503_);
lean_inc(v_traceState_498_);
lean_inc(v_auxDeclNGen_502_);
lean_inc(v_ngen_501_);
lean_inc(v_nextMacroScope_500_);
lean_inc(v_env_499_);
lean_dec(v___x_497_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_529_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
uint64_t v_tid_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_527_; 
v_tid_510_ = lean_ctor_get_uint64(v_traceState_498_, sizeof(void*)*1);
v_isSharedCheck_527_ = !lean_is_exclusive(v_traceState_498_);
if (v_isSharedCheck_527_ == 0)
{
lean_object* v_unused_528_; 
v_unused_528_ = lean_ctor_get(v_traceState_498_, 0);
lean_dec(v_unused_528_);
v___x_512_ = v_traceState_498_;
v_isShared_513_ = v_isSharedCheck_527_;
goto v_resetjp_511_;
}
else
{
lean_dec(v_traceState_498_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_527_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_517_; 
v___x_514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_514_, 0, v_ref_461_);
lean_ctor_set(v___x_514_, 1, v_a_493_);
v___x_515_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_459_, v___x_514_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 0, v___x_515_);
v___x_517_ = v___x_512_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v___x_515_);
lean_ctor_set_uint64(v_reuseFailAlloc_526_, sizeof(void*)*1, v_tid_510_);
v___x_517_ = v_reuseFailAlloc_526_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
lean_object* v___x_519_; 
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 4, v___x_517_);
v___x_519_ = v___x_508_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_env_499_);
lean_ctor_set(v_reuseFailAlloc_525_, 1, v_nextMacroScope_500_);
lean_ctor_set(v_reuseFailAlloc_525_, 2, v_ngen_501_);
lean_ctor_set(v_reuseFailAlloc_525_, 3, v_auxDeclNGen_502_);
lean_ctor_set(v_reuseFailAlloc_525_, 4, v___x_517_);
lean_ctor_set(v_reuseFailAlloc_525_, 5, v_cache_503_);
lean_ctor_set(v_reuseFailAlloc_525_, 6, v_messages_504_);
lean_ctor_set(v_reuseFailAlloc_525_, 7, v_infoState_505_);
lean_ctor_set(v_reuseFailAlloc_525_, 8, v_snapshotTasks_506_);
v___x_519_ = v_reuseFailAlloc_525_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_523_; 
v___x_520_ = lean_st_ref_set(v___y_464_, v___x_519_);
v___x_521_ = lean_box(0);
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 0, v___x_521_);
v___x_523_ = v___x_495_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v___x_521_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5___boxed(lean_object* v_oldTraces_531_, lean_object* v_data_532_, lean_object* v_ref_533_, lean_object* v_msg_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5(v_oldTraces_531_, v_data_532_, v_ref_533_, v_msg_534_, v___y_535_, v___y_536_);
lean_dec(v___y_536_);
lean_dec_ref(v___y_535_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__6___redArg(lean_object* v_x_539_){
_start:
{
if (lean_obj_tag(v_x_539_) == 0)
{
lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_548_; 
v_a_541_ = lean_ctor_get(v_x_539_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v_x_539_);
if (v_isSharedCheck_548_ == 0)
{
v___x_543_ = v_x_539_;
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v_x_539_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_546_; 
if (v_isShared_544_ == 0)
{
lean_ctor_set_tag(v___x_543_, 1);
v___x_546_ = v___x_543_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_a_541_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
else
{
lean_object* v_a_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_556_; 
v_a_549_ = lean_ctor_get(v_x_539_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v_x_539_);
if (v_isSharedCheck_556_ == 0)
{
v___x_551_ = v_x_539_;
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_a_549_);
lean_dec(v_x_539_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_554_; 
if (v_isShared_552_ == 0)
{
lean_ctor_set_tag(v___x_551_, 0);
v___x_554_ = v___x_551_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_a_549_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__6___redArg___boxed(lean_object* v_x_557_, lean_object* v___y_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__6___redArg(v_x_557_);
return v_res_559_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__4(lean_object* v_e_560_){
_start:
{
if (lean_obj_tag(v_e_560_) == 0)
{
uint8_t v___x_561_; 
v___x_561_ = 2;
return v___x_561_;
}
else
{
uint8_t v___x_562_; 
v___x_562_ = 0;
return v___x_562_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__4___boxed(lean_object* v_e_563_){
_start:
{
uint8_t v_res_564_; lean_object* v_r_565_; 
v_res_564_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__4(v_e_563_);
lean_dec_ref(v_e_563_);
v_r_565_ = lean_box(v_res_564_);
return v_r_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(lean_object* v_opts_566_, lean_object* v_opt_567_){
_start:
{
lean_object* v_name_568_; lean_object* v_defValue_569_; lean_object* v_map_570_; lean_object* v___x_571_; 
v_name_568_ = lean_ctor_get(v_opt_567_, 0);
v_defValue_569_ = lean_ctor_get(v_opt_567_, 1);
v_map_570_ = lean_ctor_get(v_opts_566_, 0);
v___x_571_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_570_, v_name_568_);
if (lean_obj_tag(v___x_571_) == 0)
{
lean_inc(v_defValue_569_);
return v_defValue_569_;
}
else
{
lean_object* v_val_572_; 
v_val_572_ = lean_ctor_get(v___x_571_, 0);
lean_inc(v_val_572_);
lean_dec_ref_known(v___x_571_, 1);
if (lean_obj_tag(v_val_572_) == 3)
{
lean_object* v_v_573_; 
v_v_573_ = lean_ctor_get(v_val_572_, 0);
lean_inc(v_v_573_);
lean_dec_ref_known(v_val_572_, 1);
return v_v_573_;
}
else
{
lean_dec(v_val_572_);
lean_inc(v_defValue_569_);
return v_defValue_569_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7___boxed(lean_object* v_opts_574_, lean_object* v_opt_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(v_opts_574_, v_opt_575_);
lean_dec_ref(v_opt_575_);
lean_dec_ref(v_opts_574_);
return v_res_576_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__1(void){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_578_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0));
v___x_579_ = l_Lean_stringToMessageData(v___x_578_);
return v___x_579_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2(void){
_start:
{
lean_object* v___x_580_; double v___x_581_; 
v___x_580_ = lean_unsigned_to_nat(0u);
v___x_581_ = lean_float_of_nat(v___x_580_);
return v___x_581_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__4(void){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_583_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3));
v___x_584_ = l_Lean_stringToMessageData(v___x_583_);
return v___x_584_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__5(void){
_start:
{
lean_object* v___x_585_; double v___x_586_; 
v___x_585_ = lean_unsigned_to_nat(1000u);
v___x_586_ = lean_float_of_nat(v___x_585_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3(lean_object* v_cls_587_, uint8_t v_collapsed_588_, lean_object* v_tag_589_, lean_object* v_opts_590_, uint8_t v_clsEnabled_591_, lean_object* v_oldTraces_592_, lean_object* v_msg_593_, lean_object* v_resStartStop_594_, lean_object* v___y_595_, lean_object* v___y_596_){
_start:
{
lean_object* v_fst_598_; lean_object* v_snd_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_697_; 
v_fst_598_ = lean_ctor_get(v_resStartStop_594_, 0);
v_snd_599_ = lean_ctor_get(v_resStartStop_594_, 1);
v_isSharedCheck_697_ = !lean_is_exclusive(v_resStartStop_594_);
if (v_isSharedCheck_697_ == 0)
{
v___x_601_ = v_resStartStop_594_;
v_isShared_602_ = v_isSharedCheck_697_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_snd_599_);
lean_inc(v_fst_598_);
lean_dec(v_resStartStop_594_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_697_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___y_604_; lean_object* v___y_605_; lean_object* v_data_606_; lean_object* v_fst_617_; lean_object* v_snd_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_696_; 
v_fst_617_ = lean_ctor_get(v_snd_599_, 0);
v_snd_618_ = lean_ctor_get(v_snd_599_, 1);
v_isSharedCheck_696_ = !lean_is_exclusive(v_snd_599_);
if (v_isSharedCheck_696_ == 0)
{
v___x_620_ = v_snd_599_;
v_isShared_621_ = v_isSharedCheck_696_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_snd_618_);
lean_inc(v_fst_617_);
lean_dec(v_snd_599_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_696_;
goto v_resetjp_619_;
}
v___jp_603_:
{
lean_object* v___x_607_; 
lean_inc(v___y_604_);
v___x_607_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5(v_oldTraces_592_, v_data_606_, v___y_604_, v___y_605_, v___y_595_, v___y_596_);
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v___x_608_; 
lean_dec_ref_known(v___x_607_, 1);
v___x_608_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__6___redArg(v_fst_598_);
return v___x_608_;
}
else
{
lean_object* v_a_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_616_; 
lean_dec(v_fst_598_);
v_a_609_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_616_ == 0)
{
v___x_611_ = v___x_607_;
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_a_609_);
lean_dec(v___x_607_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_614_; 
if (v_isShared_612_ == 0)
{
v___x_614_ = v___x_611_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_a_609_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
}
v_resetjp_619_:
{
lean_object* v___x_622_; uint8_t v___x_623_; lean_object* v___y_625_; lean_object* v_a_626_; uint8_t v___y_650_; double v___y_681_; 
v___x_622_ = l_Lean_trace_profiler;
v___x_623_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_opts_590_, v___x_622_);
if (v___x_623_ == 0)
{
v___y_650_ = v___x_623_;
goto v___jp_649_;
}
else
{
lean_object* v___x_686_; uint8_t v___x_687_; 
v___x_686_ = l_Lean_trace_profiler_useHeartbeats;
v___x_687_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_opts_590_, v___x_686_);
if (v___x_687_ == 0)
{
lean_object* v___x_688_; lean_object* v___x_689_; double v___x_690_; double v___x_691_; double v___x_692_; 
v___x_688_ = l_Lean_trace_profiler_threshold;
v___x_689_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(v_opts_590_, v___x_688_);
v___x_690_ = lean_float_of_nat(v___x_689_);
v___x_691_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__5);
v___x_692_ = lean_float_div(v___x_690_, v___x_691_);
v___y_681_ = v___x_692_;
goto v___jp_680_;
}
else
{
lean_object* v___x_693_; lean_object* v___x_694_; double v___x_695_; 
v___x_693_ = l_Lean_trace_profiler_threshold;
v___x_694_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(v_opts_590_, v___x_693_);
v___x_695_ = lean_float_of_nat(v___x_694_);
v___y_681_ = v___x_695_;
goto v___jp_680_;
}
}
v___jp_624_:
{
uint8_t v_result_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_632_; 
v_result_627_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__4(v_fst_598_);
v___x_628_ = l_Lean_TraceResult_toEmoji(v_result_627_);
v___x_629_ = l_Lean_stringToMessageData(v___x_628_);
v___x_630_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__1);
if (v_isShared_621_ == 0)
{
lean_ctor_set_tag(v___x_620_, 7);
lean_ctor_set(v___x_620_, 1, v___x_630_);
lean_ctor_set(v___x_620_, 0, v___x_629_);
v___x_632_ = v___x_620_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v___x_629_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v___x_630_);
v___x_632_ = v_reuseFailAlloc_643_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
lean_object* v_m_634_; 
if (v_isShared_602_ == 0)
{
lean_ctor_set_tag(v___x_601_, 7);
lean_ctor_set(v___x_601_, 1, v_a_626_);
lean_ctor_set(v___x_601_, 0, v___x_632_);
v_m_634_ = v___x_601_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v___x_632_);
lean_ctor_set(v_reuseFailAlloc_642_, 1, v_a_626_);
v_m_634_ = v_reuseFailAlloc_642_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
lean_object* v___x_635_; lean_object* v___x_636_; double v___x_637_; lean_object* v_data_638_; 
v___x_635_ = lean_box(v_result_627_);
v___x_636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_636_, 0, v___x_635_);
v___x_637_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2);
lean_inc_ref(v_tag_589_);
lean_inc_ref(v___x_636_);
lean_inc(v_cls_587_);
v_data_638_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_638_, 0, v_cls_587_);
lean_ctor_set(v_data_638_, 1, v___x_636_);
lean_ctor_set(v_data_638_, 2, v_tag_589_);
lean_ctor_set_float(v_data_638_, sizeof(void*)*3, v___x_637_);
lean_ctor_set_float(v_data_638_, sizeof(void*)*3 + 8, v___x_637_);
lean_ctor_set_uint8(v_data_638_, sizeof(void*)*3 + 16, v_collapsed_588_);
if (v___x_623_ == 0)
{
lean_dec_ref_known(v___x_636_, 1);
lean_dec(v_snd_618_);
lean_dec(v_fst_617_);
lean_dec_ref(v_tag_589_);
lean_dec(v_cls_587_);
v___y_604_ = v___y_625_;
v___y_605_ = v_m_634_;
v_data_606_ = v_data_638_;
goto v___jp_603_;
}
else
{
lean_object* v_data_639_; double v___x_640_; double v___x_641_; 
lean_dec_ref_known(v_data_638_, 3);
v_data_639_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_639_, 0, v_cls_587_);
lean_ctor_set(v_data_639_, 1, v___x_636_);
lean_ctor_set(v_data_639_, 2, v_tag_589_);
v___x_640_ = lean_unbox_float(v_fst_617_);
lean_dec(v_fst_617_);
lean_ctor_set_float(v_data_639_, sizeof(void*)*3, v___x_640_);
v___x_641_ = lean_unbox_float(v_snd_618_);
lean_dec(v_snd_618_);
lean_ctor_set_float(v_data_639_, sizeof(void*)*3 + 8, v___x_641_);
lean_ctor_set_uint8(v_data_639_, sizeof(void*)*3 + 16, v_collapsed_588_);
v___y_604_ = v___y_625_;
v___y_605_ = v_m_634_;
v_data_606_ = v_data_639_;
goto v___jp_603_;
}
}
}
}
v___jp_644_:
{
lean_object* v_ref_645_; lean_object* v___x_646_; 
v_ref_645_ = lean_ctor_get(v___y_595_, 5);
lean_inc(v___y_596_);
lean_inc_ref(v___y_595_);
lean_inc(v_fst_598_);
v___x_646_ = lean_apply_4(v_msg_593_, v_fst_598_, v___y_595_, v___y_596_, lean_box(0));
if (lean_obj_tag(v___x_646_) == 0)
{
lean_object* v_a_647_; 
v_a_647_ = lean_ctor_get(v___x_646_, 0);
lean_inc(v_a_647_);
lean_dec_ref_known(v___x_646_, 1);
v___y_625_ = v_ref_645_;
v_a_626_ = v_a_647_;
goto v___jp_624_;
}
else
{
lean_object* v___x_648_; 
lean_dec_ref_known(v___x_646_, 1);
v___x_648_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__4);
v___y_625_ = v_ref_645_;
v_a_626_ = v___x_648_;
goto v___jp_624_;
}
}
v___jp_649_:
{
if (v_clsEnabled_591_ == 0)
{
if (v___y_650_ == 0)
{
lean_object* v___x_651_; lean_object* v_traceState_652_; lean_object* v_env_653_; lean_object* v_nextMacroScope_654_; lean_object* v_ngen_655_; lean_object* v_auxDeclNGen_656_; lean_object* v_cache_657_; lean_object* v_messages_658_; lean_object* v_infoState_659_; lean_object* v_snapshotTasks_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_679_; 
lean_del_object(v___x_620_);
lean_dec(v_snd_618_);
lean_dec(v_fst_617_);
lean_del_object(v___x_601_);
lean_dec_ref(v_msg_593_);
lean_dec_ref(v_tag_589_);
lean_dec(v_cls_587_);
v___x_651_ = lean_st_ref_take(v___y_596_);
v_traceState_652_ = lean_ctor_get(v___x_651_, 4);
v_env_653_ = lean_ctor_get(v___x_651_, 0);
v_nextMacroScope_654_ = lean_ctor_get(v___x_651_, 1);
v_ngen_655_ = lean_ctor_get(v___x_651_, 2);
v_auxDeclNGen_656_ = lean_ctor_get(v___x_651_, 3);
v_cache_657_ = lean_ctor_get(v___x_651_, 5);
v_messages_658_ = lean_ctor_get(v___x_651_, 6);
v_infoState_659_ = lean_ctor_get(v___x_651_, 7);
v_snapshotTasks_660_ = lean_ctor_get(v___x_651_, 8);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_679_ == 0)
{
v___x_662_ = v___x_651_;
v_isShared_663_ = v_isSharedCheck_679_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_snapshotTasks_660_);
lean_inc(v_infoState_659_);
lean_inc(v_messages_658_);
lean_inc(v_cache_657_);
lean_inc(v_traceState_652_);
lean_inc(v_auxDeclNGen_656_);
lean_inc(v_ngen_655_);
lean_inc(v_nextMacroScope_654_);
lean_inc(v_env_653_);
lean_dec(v___x_651_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_679_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
uint64_t v_tid_664_; lean_object* v_traces_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_678_; 
v_tid_664_ = lean_ctor_get_uint64(v_traceState_652_, sizeof(void*)*1);
v_traces_665_ = lean_ctor_get(v_traceState_652_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v_traceState_652_);
if (v_isSharedCheck_678_ == 0)
{
v___x_667_ = v_traceState_652_;
v_isShared_668_ = v_isSharedCheck_678_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_traces_665_);
lean_dec(v_traceState_652_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_678_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_669_; lean_object* v___x_671_; 
v___x_669_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_592_, v_traces_665_);
lean_dec_ref(v_traces_665_);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 0, v___x_669_);
v___x_671_ = v___x_667_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v___x_669_);
lean_ctor_set_uint64(v_reuseFailAlloc_677_, sizeof(void*)*1, v_tid_664_);
v___x_671_ = v_reuseFailAlloc_677_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
lean_object* v___x_673_; 
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 4, v___x_671_);
v___x_673_ = v___x_662_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_env_653_);
lean_ctor_set(v_reuseFailAlloc_676_, 1, v_nextMacroScope_654_);
lean_ctor_set(v_reuseFailAlloc_676_, 2, v_ngen_655_);
lean_ctor_set(v_reuseFailAlloc_676_, 3, v_auxDeclNGen_656_);
lean_ctor_set(v_reuseFailAlloc_676_, 4, v___x_671_);
lean_ctor_set(v_reuseFailAlloc_676_, 5, v_cache_657_);
lean_ctor_set(v_reuseFailAlloc_676_, 6, v_messages_658_);
lean_ctor_set(v_reuseFailAlloc_676_, 7, v_infoState_659_);
lean_ctor_set(v_reuseFailAlloc_676_, 8, v_snapshotTasks_660_);
v___x_673_ = v_reuseFailAlloc_676_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_674_ = lean_st_ref_set(v___y_596_, v___x_673_);
v___x_675_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__6___redArg(v_fst_598_);
return v___x_675_;
}
}
}
}
}
else
{
goto v___jp_644_;
}
}
else
{
goto v___jp_644_;
}
}
v___jp_680_:
{
double v___x_682_; double v___x_683_; double v___x_684_; uint8_t v___x_685_; 
v___x_682_ = lean_unbox_float(v_snd_618_);
v___x_683_ = lean_unbox_float(v_fst_617_);
v___x_684_ = lean_float_sub(v___x_682_, v___x_683_);
v___x_685_ = lean_float_decLt(v___y_681_, v___x_684_);
v___y_650_ = v___x_685_;
goto v___jp_649_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___boxed(lean_object* v_cls_698_, lean_object* v_collapsed_699_, lean_object* v_tag_700_, lean_object* v_opts_701_, lean_object* v_clsEnabled_702_, lean_object* v_oldTraces_703_, lean_object* v_msg_704_, lean_object* v_resStartStop_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
uint8_t v_collapsed_boxed_709_; uint8_t v_clsEnabled_boxed_710_; lean_object* v_res_711_; 
v_collapsed_boxed_709_ = lean_unbox(v_collapsed_699_);
v_clsEnabled_boxed_710_ = lean_unbox(v_clsEnabled_702_);
v_res_711_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3(v_cls_698_, v_collapsed_boxed_709_, v_tag_700_, v_opts_701_, v_clsEnabled_boxed_710_, v_oldTraces_703_, v_msg_704_, v_resStartStop_705_, v___y_706_, v___y_707_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec_ref(v_opts_701_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5___redArg(lean_object* v_msg_712_, lean_object* v___y_713_, lean_object* v___y_714_){
_start:
{
lean_object* v_ref_716_; lean_object* v___x_717_; lean_object* v_a_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_726_; 
v_ref_716_ = lean_ctor_get(v___y_713_, 5);
v___x_717_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0(v_msg_712_, v___y_713_, v___y_714_);
v_a_718_ = lean_ctor_get(v___x_717_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_726_ == 0)
{
v___x_720_ = v___x_717_;
v_isShared_721_ = v_isSharedCheck_726_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_a_718_);
lean_dec(v___x_717_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_726_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_722_; lean_object* v___x_724_; 
lean_inc(v_ref_716_);
v___x_722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_722_, 0, v_ref_716_);
lean_ctor_set(v___x_722_, 1, v_a_718_);
if (v_isShared_721_ == 0)
{
lean_ctor_set_tag(v___x_720_, 1);
lean_ctor_set(v___x_720_, 0, v___x_722_);
v___x_724_ = v___x_720_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v___x_722_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5___redArg___boxed(lean_object* v_msg_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5___redArg(v_msg_727_, v___y_728_, v___y_729_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0(lean_object* v_cls_735_, lean_object* v_msg_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v_ref_740_; lean_object* v___x_741_; lean_object* v_a_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_786_; 
v_ref_740_ = lean_ctor_get(v___y_737_, 5);
v___x_741_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0(v_msg_736_, v___y_737_, v___y_738_);
v_a_742_ = lean_ctor_get(v___x_741_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_741_);
if (v_isSharedCheck_786_ == 0)
{
v___x_744_ = v___x_741_;
v_isShared_745_ = v_isSharedCheck_786_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_a_742_);
lean_dec(v___x_741_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_786_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_746_; lean_object* v_traceState_747_; lean_object* v_env_748_; lean_object* v_nextMacroScope_749_; lean_object* v_ngen_750_; lean_object* v_auxDeclNGen_751_; lean_object* v_cache_752_; lean_object* v_messages_753_; lean_object* v_infoState_754_; lean_object* v_snapshotTasks_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_785_; 
v___x_746_ = lean_st_ref_take(v___y_738_);
v_traceState_747_ = lean_ctor_get(v___x_746_, 4);
v_env_748_ = lean_ctor_get(v___x_746_, 0);
v_nextMacroScope_749_ = lean_ctor_get(v___x_746_, 1);
v_ngen_750_ = lean_ctor_get(v___x_746_, 2);
v_auxDeclNGen_751_ = lean_ctor_get(v___x_746_, 3);
v_cache_752_ = lean_ctor_get(v___x_746_, 5);
v_messages_753_ = lean_ctor_get(v___x_746_, 6);
v_infoState_754_ = lean_ctor_get(v___x_746_, 7);
v_snapshotTasks_755_ = lean_ctor_get(v___x_746_, 8);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_785_ == 0)
{
v___x_757_ = v___x_746_;
v_isShared_758_ = v_isSharedCheck_785_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_snapshotTasks_755_);
lean_inc(v_infoState_754_);
lean_inc(v_messages_753_);
lean_inc(v_cache_752_);
lean_inc(v_traceState_747_);
lean_inc(v_auxDeclNGen_751_);
lean_inc(v_ngen_750_);
lean_inc(v_nextMacroScope_749_);
lean_inc(v_env_748_);
lean_dec(v___x_746_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_785_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
uint64_t v_tid_759_; lean_object* v_traces_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_784_; 
v_tid_759_ = lean_ctor_get_uint64(v_traceState_747_, sizeof(void*)*1);
v_traces_760_ = lean_ctor_get(v_traceState_747_, 0);
v_isSharedCheck_784_ = !lean_is_exclusive(v_traceState_747_);
if (v_isSharedCheck_784_ == 0)
{
v___x_762_ = v_traceState_747_;
v_isShared_763_ = v_isSharedCheck_784_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_traces_760_);
lean_dec(v_traceState_747_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_784_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_764_; double v___x_765_; uint8_t v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_774_; 
v___x_764_ = lean_box(0);
v___x_765_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2);
v___x_766_ = 0;
v___x_767_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0___closed__0));
v___x_768_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_768_, 0, v_cls_735_);
lean_ctor_set(v___x_768_, 1, v___x_764_);
lean_ctor_set(v___x_768_, 2, v___x_767_);
lean_ctor_set_float(v___x_768_, sizeof(void*)*3, v___x_765_);
lean_ctor_set_float(v___x_768_, sizeof(void*)*3 + 8, v___x_765_);
lean_ctor_set_uint8(v___x_768_, sizeof(void*)*3 + 16, v___x_766_);
v___x_769_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0___closed__1));
v___x_770_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_770_, 0, v___x_768_);
lean_ctor_set(v___x_770_, 1, v_a_742_);
lean_ctor_set(v___x_770_, 2, v___x_769_);
lean_inc(v_ref_740_);
v___x_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_771_, 0, v_ref_740_);
lean_ctor_set(v___x_771_, 1, v___x_770_);
v___x_772_ = l_Lean_PersistentArray_push___redArg(v_traces_760_, v___x_771_);
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 0, v___x_772_);
v___x_774_ = v___x_762_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_772_);
lean_ctor_set_uint64(v_reuseFailAlloc_783_, sizeof(void*)*1, v_tid_759_);
v___x_774_ = v_reuseFailAlloc_783_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
lean_object* v___x_776_; 
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 4, v___x_774_);
v___x_776_ = v___x_757_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_env_748_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v_nextMacroScope_749_);
lean_ctor_set(v_reuseFailAlloc_782_, 2, v_ngen_750_);
lean_ctor_set(v_reuseFailAlloc_782_, 3, v_auxDeclNGen_751_);
lean_ctor_set(v_reuseFailAlloc_782_, 4, v___x_774_);
lean_ctor_set(v_reuseFailAlloc_782_, 5, v_cache_752_);
lean_ctor_set(v_reuseFailAlloc_782_, 6, v_messages_753_);
lean_ctor_set(v_reuseFailAlloc_782_, 7, v_infoState_754_);
lean_ctor_set(v_reuseFailAlloc_782_, 8, v_snapshotTasks_755_);
v___x_776_ = v_reuseFailAlloc_782_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_780_; 
v___x_777_ = lean_st_ref_set(v___y_738_, v___x_776_);
v___x_778_ = lean_box(0);
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 0, v___x_778_);
v___x_780_ = v___x_744_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v___x_778_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0___boxed(lean_object* v_cls_787_, lean_object* v_msg_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0(v_cls_787_, v_msg_788_, v___y_789_, v___y_790_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
return v_res_792_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6(void){
_start:
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_803_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__3));
v___x_804_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__5));
v___x_805_ = l_Lean_Name_append(v___x_804_, v___x_803_);
return v___x_805_;
}
}
static double _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9(void){
_start:
{
lean_object* v___x_808_; double v___x_809_; 
v___x_808_ = lean_unsigned_to_nat(1000000000u);
v___x_809_ = lean_float_of_nat(v___x_808_);
return v___x_809_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12(void){
_start:
{
lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_812_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__11));
v___x_813_ = l_Lean_stringToMessageData(v___x_812_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load(lean_object* v_lratPath_815_, uint8_t v_trimProofs_816_, lean_object* v_a_817_, lean_object* v_a_818_){
_start:
{
lean_object* v___x_820_; 
v___x_820_ = l_IO_FS_readBinFile(v_lratPath_815_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v_options_821_; lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_1256_; 
v_options_821_ = lean_ctor_get(v_a_817_, 2);
v_a_822_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_824_ = v___x_820_;
v_isShared_825_ = v_isSharedCheck_1256_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_820_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_1256_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v_ref_826_; lean_object* v_inheritedTraceOptions_827_; uint8_t v_hasTrace_828_; lean_object* v___f_829_; lean_object* v___f_830_; lean_object* v___x_831_; lean_object* v_proof_833_; lean_object* v___y_834_; lean_object* v_options_835_; lean_object* v_inheritedTraceOptions_836_; lean_object* v___y_837_; lean_object* v_proof_869_; lean_object* v___y_870_; lean_object* v___y_871_; lean_object* v___y_877_; lean_object* v___y_878_; lean_object* v___y_879_; uint8_t v___x_881_; lean_object* v___x_882_; lean_object* v___y_884_; lean_object* v___y_885_; lean_object* v___y_886_; lean_object* v___y_887_; lean_object* v___y_888_; uint8_t v___y_889_; lean_object* v_a_890_; lean_object* v___y_900_; lean_object* v___y_901_; lean_object* v___y_902_; lean_object* v___y_903_; lean_object* v___y_904_; uint8_t v___y_905_; lean_object* v_a_906_; lean_object* v___y_909_; lean_object* v___y_910_; lean_object* v___y_911_; lean_object* v___y_912_; uint8_t v___y_913_; lean_object* v___y_914_; lean_object* v_a_915_; lean_object* v___y_928_; lean_object* v___y_929_; lean_object* v___y_930_; lean_object* v___y_931_; uint8_t v___y_932_; lean_object* v___y_933_; lean_object* v_a_934_; lean_object* v___y_937_; lean_object* v___y_938_; lean_object* v___y_939_; lean_object* v___y_940_; uint8_t v___y_941_; lean_object* v___y_942_; lean_object* v___y_1016_; lean_object* v___y_1017_; lean_object* v___y_1018_; lean_object* v___y_1019_; lean_object* v_a_1093_; lean_object* v___y_1115_; 
v_ref_826_ = lean_ctor_get(v_a_817_, 5);
v_inheritedTraceOptions_827_ = lean_ctor_get(v_a_817_, 13);
v_hasTrace_828_ = lean_ctor_get_uint8(v_options_821_, sizeof(void*)*1);
v___f_829_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__0));
v___f_830_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__1), 2, 1);
lean_closure_set(v___f_830_, 0, v_a_822_);
v___x_831_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__3));
v___x_881_ = 1;
v___x_882_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0___closed__0));
if (v_hasTrace_828_ == 0)
{
lean_object* v___x_1117_; 
v___x_1117_ = l_IO_lazyPure___redArg(v___f_830_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1118_; 
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
lean_inc(v_a_1118_);
lean_dec_ref_known(v___x_1117_, 1);
if (lean_obj_tag(v_a_1118_) == 0)
{
lean_object* v_a_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
v_a_1119_ = lean_ctor_get(v_a_1118_, 0);
lean_inc(v_a_1119_);
lean_dec_ref_known(v_a_1118_, 1);
v___x_1120_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12);
v___x_1121_ = l_Lean_stringToMessageData(v_a_1119_);
v___x_1122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1120_);
lean_ctor_set(v___x_1122_, 1, v___x_1121_);
v___x_1123_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5___redArg(v___x_1122_, v_a_817_, v_a_818_);
v___y_1115_ = v___x_1123_;
goto v___jp_1114_;
}
else
{
lean_object* v_a_1124_; 
v_a_1124_ = lean_ctor_get(v_a_1118_, 0);
lean_inc(v_a_1124_);
lean_dec_ref_known(v_a_1118_, 1);
v_a_1093_ = v_a_1124_;
goto v___jp_1092_;
}
}
else
{
lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1136_; 
lean_del_object(v___x_824_);
v_a_1125_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1127_ = v___x_1117_;
v_isShared_1128_ = v_isSharedCheck_1136_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v___x_1117_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1136_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1134_; 
v___x_1129_ = lean_io_error_to_string(v_a_1125_);
v___x_1130_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1129_);
v___x_1131_ = l_Lean_MessageData_ofFormat(v___x_1130_);
lean_inc(v_ref_826_);
v___x_1132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1132_, 0, v_ref_826_);
lean_ctor_set(v___x_1132_, 1, v___x_1131_);
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 0, v___x_1132_);
v___x_1134_ = v___x_1127_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v___x_1132_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
}
}
else
{
lean_object* v___f_1137_; lean_object* v___x_1138_; uint8_t v___x_1139_; lean_object* v___y_1141_; lean_object* v___y_1142_; lean_object* v_a_1143_; lean_object* v___y_1156_; lean_object* v___y_1157_; lean_object* v_a_1158_; lean_object* v___y_1161_; lean_object* v___y_1162_; lean_object* v_a_1163_; lean_object* v___y_1166_; lean_object* v___y_1167_; lean_object* v_a_1168_; lean_object* v___y_1178_; lean_object* v___y_1179_; lean_object* v_a_1180_; lean_object* v___y_1183_; lean_object* v___y_1184_; lean_object* v_a_1185_; 
v___f_1137_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__13));
v___x_1138_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6);
v___x_1139_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_827_, v_options_821_, v___x_1138_);
if (v___x_1139_ == 0)
{
lean_object* v___x_1234_; uint8_t v___x_1235_; 
v___x_1234_ = l_Lean_trace_profiler;
v___x_1235_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_options_821_, v___x_1234_);
if (v___x_1235_ == 0)
{
lean_object* v___x_1236_; 
v___x_1236_ = l_IO_lazyPure___redArg(v___f_830_);
if (lean_obj_tag(v___x_1236_) == 0)
{
lean_object* v_a_1237_; 
v_a_1237_ = lean_ctor_get(v___x_1236_, 0);
lean_inc(v_a_1237_);
lean_dec_ref_known(v___x_1236_, 1);
if (lean_obj_tag(v_a_1237_) == 0)
{
lean_object* v_a_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v_a_1238_ = lean_ctor_get(v_a_1237_, 0);
lean_inc(v_a_1238_);
lean_dec_ref_known(v_a_1237_, 1);
v___x_1239_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12);
v___x_1240_ = l_Lean_stringToMessageData(v_a_1238_);
v___x_1241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1239_);
lean_ctor_set(v___x_1241_, 1, v___x_1240_);
v___x_1242_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5___redArg(v___x_1241_, v_a_817_, v_a_818_);
v___y_1115_ = v___x_1242_;
goto v___jp_1114_;
}
else
{
lean_object* v_a_1243_; 
v_a_1243_ = lean_ctor_get(v_a_1237_, 0);
lean_inc(v_a_1243_);
lean_dec_ref_known(v_a_1237_, 1);
v_a_1093_ = v_a_1243_;
goto v___jp_1092_;
}
}
else
{
lean_object* v_a_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1255_; 
lean_del_object(v___x_824_);
v_a_1244_ = lean_ctor_get(v___x_1236_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1246_ = v___x_1236_;
v_isShared_1247_ = v_isSharedCheck_1255_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_a_1244_);
lean_dec(v___x_1236_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1255_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1253_; 
v___x_1248_ = lean_io_error_to_string(v_a_1244_);
v___x_1249_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1248_);
v___x_1250_ = l_Lean_MessageData_ofFormat(v___x_1249_);
lean_inc(v_ref_826_);
v___x_1251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1251_, 0, v_ref_826_);
lean_ctor_set(v___x_1251_, 1, v___x_1250_);
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 0, v___x_1251_);
v___x_1253_ = v___x_1246_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v___x_1251_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
}
else
{
goto v___jp_1187_;
}
}
else
{
goto v___jp_1187_;
}
v___jp_1140_:
{
lean_object* v___x_1144_; double v___x_1145_; double v___x_1146_; double v___x_1147_; double v___x_1148_; double v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1144_ = lean_io_mono_nanos_now();
v___x_1145_ = lean_float_of_nat(v___y_1142_);
v___x_1146_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9);
v___x_1147_ = lean_float_div(v___x_1145_, v___x_1146_);
v___x_1148_ = lean_float_of_nat(v___x_1144_);
v___x_1149_ = lean_float_div(v___x_1148_, v___x_1146_);
v___x_1150_ = lean_box_float(v___x_1147_);
v___x_1151_ = lean_box_float(v___x_1149_);
v___x_1152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1150_);
lean_ctor_set(v___x_1152_, 1, v___x_1151_);
v___x_1153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1153_, 0, v_a_1143_);
lean_ctor_set(v___x_1153_, 1, v___x_1152_);
v___x_1154_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3(v___x_831_, v___x_881_, v___x_882_, v_options_821_, v___x_1139_, v___y_1141_, v___f_1137_, v___x_1153_, v_a_817_, v_a_818_);
v___y_1115_ = v___x_1154_;
goto v___jp_1114_;
}
v___jp_1155_:
{
lean_object* v___x_1159_; 
v___x_1159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1159_, 0, v_a_1158_);
v___y_1141_ = v___y_1156_;
v___y_1142_ = v___y_1157_;
v_a_1143_ = v___x_1159_;
goto v___jp_1140_;
}
v___jp_1160_:
{
lean_object* v___x_1164_; 
v___x_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1164_, 0, v_a_1163_);
v___y_1141_ = v___y_1161_;
v___y_1142_ = v___y_1162_;
v_a_1143_ = v___x_1164_;
goto v___jp_1140_;
}
v___jp_1165_:
{
lean_object* v___x_1169_; double v___x_1170_; double v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1169_ = lean_io_get_num_heartbeats();
v___x_1170_ = lean_float_of_nat(v___y_1167_);
v___x_1171_ = lean_float_of_nat(v___x_1169_);
v___x_1172_ = lean_box_float(v___x_1170_);
v___x_1173_ = lean_box_float(v___x_1171_);
v___x_1174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1172_);
lean_ctor_set(v___x_1174_, 1, v___x_1173_);
v___x_1175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1175_, 0, v_a_1168_);
lean_ctor_set(v___x_1175_, 1, v___x_1174_);
v___x_1176_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3(v___x_831_, v___x_881_, v___x_882_, v_options_821_, v___x_1139_, v___y_1166_, v___f_1137_, v___x_1175_, v_a_817_, v_a_818_);
v___y_1115_ = v___x_1176_;
goto v___jp_1114_;
}
v___jp_1177_:
{
lean_object* v___x_1181_; 
v___x_1181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1181_, 0, v_a_1180_);
v___y_1166_ = v___y_1178_;
v___y_1167_ = v___y_1179_;
v_a_1168_ = v___x_1181_;
goto v___jp_1165_;
}
v___jp_1182_:
{
lean_object* v___x_1186_; 
v___x_1186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1186_, 0, v_a_1185_);
v___y_1166_ = v___y_1183_;
v___y_1167_ = v___y_1184_;
v_a_1168_ = v___x_1186_;
goto v___jp_1165_;
}
v___jp_1187_:
{
lean_object* v___x_1188_; lean_object* v_a_1189_; lean_object* v___x_1190_; uint8_t v___x_1191_; 
v___x_1188_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg(v_a_818_);
v_a_1189_ = lean_ctor_get(v___x_1188_, 0);
lean_inc(v_a_1189_);
lean_dec_ref(v___x_1188_);
v___x_1190_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1191_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_options_821_, v___x_1190_);
if (v___x_1191_ == 0)
{
lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1192_ = lean_io_mono_nanos_now();
v___x_1193_ = l_IO_lazyPure___redArg(v___f_830_);
if (lean_obj_tag(v___x_1193_) == 0)
{
lean_object* v_a_1194_; 
v_a_1194_ = lean_ctor_get(v___x_1193_, 0);
lean_inc(v_a_1194_);
lean_dec_ref_known(v___x_1193_, 1);
if (lean_obj_tag(v_a_1194_) == 0)
{
lean_object* v_a_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v_a_1200_; 
v_a_1195_ = lean_ctor_get(v_a_1194_, 0);
lean_inc(v_a_1195_);
lean_dec_ref_known(v_a_1194_, 1);
v___x_1196_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12);
v___x_1197_ = l_Lean_stringToMessageData(v_a_1195_);
v___x_1198_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1196_);
lean_ctor_set(v___x_1198_, 1, v___x_1197_);
v___x_1199_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5___redArg(v___x_1198_, v_a_817_, v_a_818_);
v_a_1200_ = lean_ctor_get(v___x_1199_, 0);
lean_inc(v_a_1200_);
lean_dec_ref(v___x_1199_);
v___y_1156_ = v_a_1189_;
v___y_1157_ = v___x_1192_;
v_a_1158_ = v_a_1200_;
goto v___jp_1155_;
}
else
{
lean_object* v_a_1201_; 
v_a_1201_ = lean_ctor_get(v_a_1194_, 0);
lean_inc(v_a_1201_);
lean_dec_ref_known(v_a_1194_, 1);
v___y_1161_ = v_a_1189_;
v___y_1162_ = v___x_1192_;
v_a_1163_ = v_a_1201_;
goto v___jp_1160_;
}
}
else
{
lean_object* v_a_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1212_; 
v_a_1202_ = lean_ctor_get(v___x_1193_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1193_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1204_ = v___x_1193_;
v_isShared_1205_ = v_isSharedCheck_1212_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_a_1202_);
lean_dec(v___x_1193_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1212_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1206_; lean_object* v___x_1208_; 
v___x_1206_ = lean_io_error_to_string(v_a_1202_);
if (v_isShared_1205_ == 0)
{
lean_ctor_set_tag(v___x_1204_, 3);
lean_ctor_set(v___x_1204_, 0, v___x_1206_);
v___x_1208_ = v___x_1204_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v___x_1206_);
v___x_1208_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1209_ = l_Lean_MessageData_ofFormat(v___x_1208_);
lean_inc(v_ref_826_);
v___x_1210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1210_, 0, v_ref_826_);
lean_ctor_set(v___x_1210_, 1, v___x_1209_);
v___y_1156_ = v_a_1189_;
v___y_1157_ = v___x_1192_;
v_a_1158_ = v___x_1210_;
goto v___jp_1155_;
}
}
}
}
else
{
lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1213_ = lean_io_get_num_heartbeats();
v___x_1214_ = l_IO_lazyPure___redArg(v___f_830_);
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_object* v_a_1215_; 
v_a_1215_ = lean_ctor_get(v___x_1214_, 0);
lean_inc(v_a_1215_);
lean_dec_ref_known(v___x_1214_, 1);
if (lean_obj_tag(v_a_1215_) == 0)
{
lean_object* v_a_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v_a_1221_; 
v_a_1216_ = lean_ctor_get(v_a_1215_, 0);
lean_inc(v_a_1216_);
lean_dec_ref_known(v_a_1215_, 1);
v___x_1217_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12);
v___x_1218_ = l_Lean_stringToMessageData(v_a_1216_);
v___x_1219_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1217_);
lean_ctor_set(v___x_1219_, 1, v___x_1218_);
v___x_1220_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5___redArg(v___x_1219_, v_a_817_, v_a_818_);
v_a_1221_ = lean_ctor_get(v___x_1220_, 0);
lean_inc(v_a_1221_);
lean_dec_ref(v___x_1220_);
v___y_1178_ = v_a_1189_;
v___y_1179_ = v___x_1213_;
v_a_1180_ = v_a_1221_;
goto v___jp_1177_;
}
else
{
lean_object* v_a_1222_; 
v_a_1222_ = lean_ctor_get(v_a_1215_, 0);
lean_inc(v_a_1222_);
lean_dec_ref_known(v_a_1215_, 1);
v___y_1183_ = v_a_1189_;
v___y_1184_ = v___x_1213_;
v_a_1185_ = v_a_1222_;
goto v___jp_1182_;
}
}
else
{
lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1233_; 
v_a_1223_ = lean_ctor_get(v___x_1214_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1225_ = v___x_1214_;
v_isShared_1226_ = v_isSharedCheck_1233_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v___x_1214_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1233_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1227_; lean_object* v___x_1229_; 
v___x_1227_ = lean_io_error_to_string(v_a_1223_);
if (v_isShared_1226_ == 0)
{
lean_ctor_set_tag(v___x_1225_, 3);
lean_ctor_set(v___x_1225_, 0, v___x_1227_);
v___x_1229_ = v___x_1225_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v___x_1227_);
v___x_1229_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1230_ = l_Lean_MessageData_ofFormat(v___x_1229_);
lean_inc(v_ref_826_);
v___x_1231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1231_, 0, v_ref_826_);
lean_ctor_set(v___x_1231_, 1, v___x_1230_);
v___y_1178_ = v_a_1189_;
v___y_1179_ = v___x_1213_;
v_a_1180_ = v___x_1231_;
goto v___jp_1177_;
}
}
}
}
}
}
v___jp_832_:
{
lean_object* v___x_838_; uint8_t v___x_839_; 
v___x_838_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6);
v___x_839_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_836_, v_options_835_, v___x_838_);
if (v___x_839_ == 0)
{
lean_object* v___x_841_; 
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 0, v_proof_833_);
v___x_841_ = v___x_824_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_proof_833_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
else
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
lean_del_object(v___x_824_);
v___x_843_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__7));
v___x_844_ = lean_array_get_size(v_proof_833_);
v___x_845_ = l_Nat_reprFast(v___x_844_);
v___x_846_ = lean_string_append(v___x_843_, v___x_845_);
lean_dec_ref(v___x_845_);
v___x_847_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__8));
v___x_848_ = lean_string_append(v___x_846_, v___x_847_);
v___x_849_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_849_, 0, v___x_848_);
v___x_850_ = l_Lean_MessageData_ofFormat(v___x_849_);
v___x_851_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0(v___x_831_, v___x_850_, v___y_834_, v___y_837_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_858_; 
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_858_ == 0)
{
lean_object* v_unused_859_; 
v_unused_859_ = lean_ctor_get(v___x_851_, 0);
lean_dec(v_unused_859_);
v___x_853_ = v___x_851_;
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
else
{
lean_dec(v___x_851_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_856_; 
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 0, v_proof_833_);
v___x_856_ = v___x_853_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_proof_833_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
else
{
lean_object* v_a_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_867_; 
lean_dec_ref(v_proof_833_);
v_a_860_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_867_ == 0)
{
v___x_862_ = v___x_851_;
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_dec(v___x_851_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_865_; 
if (v_isShared_863_ == 0)
{
v___x_865_ = v___x_862_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_a_860_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
}
}
v___jp_868_:
{
lean_object* v_options_872_; uint8_t v_hasTrace_873_; 
v_options_872_ = lean_ctor_get(v___y_870_, 2);
v_hasTrace_873_ = lean_ctor_get_uint8(v_options_872_, sizeof(void*)*1);
if (v_hasTrace_873_ == 0)
{
lean_object* v___x_874_; 
lean_del_object(v___x_824_);
v___x_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_874_, 0, v_proof_869_);
return v___x_874_;
}
else
{
lean_object* v_inheritedTraceOptions_875_; 
v_inheritedTraceOptions_875_ = lean_ctor_get(v___y_870_, 13);
v_proof_833_ = v_proof_869_;
v___y_834_ = v___y_870_;
v_options_835_ = v_options_872_;
v_inheritedTraceOptions_836_ = v_inheritedTraceOptions_875_;
v___y_837_ = v___y_871_;
goto v___jp_832_;
}
}
v___jp_876_:
{
if (lean_obj_tag(v___y_879_) == 0)
{
lean_object* v_a_880_; 
v_a_880_ = lean_ctor_get(v___y_879_, 0);
lean_inc(v_a_880_);
lean_dec_ref_known(v___y_879_, 1);
v_proof_869_ = v_a_880_;
v___y_870_ = v___y_877_;
v___y_871_ = v___y_878_;
goto v___jp_868_;
}
else
{
lean_del_object(v___x_824_);
return v___y_879_;
}
}
v___jp_883_:
{
lean_object* v___x_891_; double v___x_892_; double v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_891_ = lean_io_get_num_heartbeats();
v___x_892_ = lean_float_of_nat(v___y_888_);
v___x_893_ = lean_float_of_nat(v___x_891_);
v___x_894_ = lean_box_float(v___x_892_);
v___x_895_ = lean_box_float(v___x_893_);
v___x_896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_896_, 0, v___x_894_);
lean_ctor_set(v___x_896_, 1, v___x_895_);
v___x_897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_897_, 0, v_a_890_);
lean_ctor_set(v___x_897_, 1, v___x_896_);
v___x_898_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3(v___x_831_, v___x_881_, v___x_882_, v___y_886_, v___y_889_, v___y_885_, v___f_829_, v___x_897_, v___y_884_, v___y_887_);
v___y_877_ = v___y_884_;
v___y_878_ = v___y_887_;
v___y_879_ = v___x_898_;
goto v___jp_876_;
}
v___jp_899_:
{
lean_object* v___x_907_; 
v___x_907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_907_, 0, v_a_906_);
v___y_884_ = v___y_902_;
v___y_885_ = v___y_901_;
v___y_886_ = v___y_900_;
v___y_887_ = v___y_904_;
v___y_888_ = v___y_903_;
v___y_889_ = v___y_905_;
v_a_890_ = v___x_907_;
goto v___jp_883_;
}
v___jp_908_:
{
lean_object* v___x_916_; double v___x_917_; double v___x_918_; double v___x_919_; double v___x_920_; double v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_916_ = lean_io_mono_nanos_now();
v___x_917_ = lean_float_of_nat(v___y_914_);
v___x_918_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9);
v___x_919_ = lean_float_div(v___x_917_, v___x_918_);
v___x_920_ = lean_float_of_nat(v___x_916_);
v___x_921_ = lean_float_div(v___x_920_, v___x_918_);
v___x_922_ = lean_box_float(v___x_919_);
v___x_923_ = lean_box_float(v___x_921_);
v___x_924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_924_, 0, v___x_922_);
lean_ctor_set(v___x_924_, 1, v___x_923_);
v___x_925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_925_, 0, v_a_915_);
lean_ctor_set(v___x_925_, 1, v___x_924_);
v___x_926_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3(v___x_831_, v___x_881_, v___x_882_, v___y_911_, v___y_913_, v___y_910_, v___f_829_, v___x_925_, v___y_909_, v___y_912_);
v___y_877_ = v___y_909_;
v___y_878_ = v___y_912_;
v___y_879_ = v___x_926_;
goto v___jp_876_;
}
v___jp_927_:
{
lean_object* v___x_935_; 
v___x_935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_935_, 0, v_a_934_);
v___y_909_ = v___y_930_;
v___y_910_ = v___y_929_;
v___y_911_ = v___y_928_;
v___y_912_ = v___y_931_;
v___y_913_ = v___y_932_;
v___y_914_ = v___y_933_;
v_a_915_ = v___x_935_;
goto v___jp_908_;
}
v___jp_936_:
{
lean_object* v___x_943_; lean_object* v_a_944_; lean_object* v___x_945_; uint8_t v___x_946_; 
v___x_943_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg(v___y_940_);
v_a_944_ = lean_ctor_get(v___x_943_, 0);
lean_inc(v_a_944_);
lean_dec_ref(v___x_943_);
v___x_945_ = l_Lean_trace_profiler_useHeartbeats;
v___x_946_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v___y_938_, v___x_945_);
if (v___x_946_ == 0)
{
lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_947_ = lean_io_mono_nanos_now();
v___x_948_ = l_IO_lazyPure___redArg(v___y_942_);
if (lean_obj_tag(v___x_948_) == 0)
{
lean_object* v_a_949_; lean_object* v___x_950_; 
v_a_949_ = lean_ctor_get(v___x_948_, 0);
lean_inc(v_a_949_);
lean_dec_ref_known(v___x_948_, 1);
v___x_950_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__4___redArg(v_a_949_);
if (lean_obj_tag(v___x_950_) == 0)
{
lean_object* v_a_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_958_; 
v_a_951_ = lean_ctor_get(v___x_950_, 0);
v_isSharedCheck_958_ = !lean_is_exclusive(v___x_950_);
if (v_isSharedCheck_958_ == 0)
{
v___x_953_ = v___x_950_;
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_a_951_);
lean_dec(v___x_950_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_956_; 
if (v_isShared_954_ == 0)
{
lean_ctor_set_tag(v___x_953_, 1);
v___x_956_ = v___x_953_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_a_951_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
v___y_909_ = v___y_939_;
v___y_910_ = v_a_944_;
v___y_911_ = v___y_938_;
v___y_912_ = v___y_940_;
v___y_913_ = v___y_941_;
v___y_914_ = v___x_947_;
v_a_915_ = v___x_956_;
goto v___jp_908_;
}
}
}
else
{
lean_object* v_a_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_969_; 
v_a_959_ = lean_ctor_get(v___x_950_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_950_);
if (v_isSharedCheck_969_ == 0)
{
v___x_961_ = v___x_950_;
v_isShared_962_ = v_isSharedCheck_969_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_a_959_);
lean_dec(v___x_950_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_969_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_963_; lean_object* v___x_965_; 
v___x_963_ = lean_io_error_to_string(v_a_959_);
if (v_isShared_962_ == 0)
{
lean_ctor_set_tag(v___x_961_, 3);
lean_ctor_set(v___x_961_, 0, v___x_963_);
v___x_965_ = v___x_961_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v___x_963_);
v___x_965_ = v_reuseFailAlloc_968_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = l_Lean_MessageData_ofFormat(v___x_965_);
lean_inc(v___y_937_);
v___x_967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_967_, 0, v___y_937_);
lean_ctor_set(v___x_967_, 1, v___x_966_);
v___y_928_ = v___y_938_;
v___y_929_ = v_a_944_;
v___y_930_ = v___y_939_;
v___y_931_ = v___y_940_;
v___y_932_ = v___y_941_;
v___y_933_ = v___x_947_;
v_a_934_ = v___x_967_;
goto v___jp_927_;
}
}
}
}
else
{
lean_object* v_a_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_980_; 
v_a_970_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_980_ == 0)
{
v___x_972_ = v___x_948_;
v_isShared_973_ = v_isSharedCheck_980_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_dec(v___x_948_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_980_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_974_; lean_object* v___x_976_; 
v___x_974_ = lean_io_error_to_string(v_a_970_);
if (v_isShared_973_ == 0)
{
lean_ctor_set_tag(v___x_972_, 3);
lean_ctor_set(v___x_972_, 0, v___x_974_);
v___x_976_ = v___x_972_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v___x_974_);
v___x_976_ = v_reuseFailAlloc_979_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_977_ = l_Lean_MessageData_ofFormat(v___x_976_);
lean_inc(v___y_937_);
v___x_978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_978_, 0, v___y_937_);
lean_ctor_set(v___x_978_, 1, v___x_977_);
v___y_928_ = v___y_938_;
v___y_929_ = v_a_944_;
v___y_930_ = v___y_939_;
v___y_931_ = v___y_940_;
v___y_932_ = v___y_941_;
v___y_933_ = v___x_947_;
v_a_934_ = v___x_978_;
goto v___jp_927_;
}
}
}
}
else
{
lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_981_ = lean_io_get_num_heartbeats();
v___x_982_ = l_IO_lazyPure___redArg(v___y_942_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_object* v_a_983_; lean_object* v___x_984_; 
v_a_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_a_983_);
lean_dec_ref_known(v___x_982_, 1);
v___x_984_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__4___redArg(v_a_983_);
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
v___y_884_ = v___y_939_;
v___y_885_ = v_a_944_;
v___y_886_ = v___y_938_;
v___y_887_ = v___y_940_;
v___y_888_ = v___x_981_;
v___y_889_ = v___y_941_;
v_a_890_ = v___x_990_;
goto v___jp_883_;
}
}
}
else
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1003_; 
v_a_993_ = lean_ctor_get(v___x_984_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_995_ = v___x_984_;
v_isShared_996_ = v_isSharedCheck_1003_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_984_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1003_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_997_; lean_object* v___x_999_; 
v___x_997_ = lean_io_error_to_string(v_a_993_);
if (v_isShared_996_ == 0)
{
lean_ctor_set_tag(v___x_995_, 3);
lean_ctor_set(v___x_995_, 0, v___x_997_);
v___x_999_ = v___x_995_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v___x_997_);
v___x_999_ = v_reuseFailAlloc_1002_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_1000_ = l_Lean_MessageData_ofFormat(v___x_999_);
lean_inc(v___y_937_);
v___x_1001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___y_937_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
v___y_900_ = v___y_938_;
v___y_901_ = v_a_944_;
v___y_902_ = v___y_939_;
v___y_903_ = v___x_981_;
v___y_904_ = v___y_940_;
v___y_905_ = v___y_941_;
v_a_906_ = v___x_1001_;
goto v___jp_899_;
}
}
}
}
else
{
lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1014_; 
v_a_1004_ = lean_ctor_get(v___x_982_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1006_ = v___x_982_;
v_isShared_1007_ = v_isSharedCheck_1014_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v___x_982_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1014_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1008_; lean_object* v___x_1010_; 
v___x_1008_ = lean_io_error_to_string(v_a_1004_);
if (v_isShared_1007_ == 0)
{
lean_ctor_set_tag(v___x_1006_, 3);
lean_ctor_set(v___x_1006_, 0, v___x_1008_);
v___x_1010_ = v___x_1006_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v___x_1008_);
v___x_1010_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1011_ = l_Lean_MessageData_ofFormat(v___x_1010_);
lean_inc(v___y_937_);
v___x_1012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___y_937_);
lean_ctor_set(v___x_1012_, 1, v___x_1011_);
v___y_900_ = v___y_938_;
v___y_901_ = v_a_944_;
v___y_902_ = v___y_939_;
v___y_903_ = v___x_981_;
v___y_904_ = v___y_940_;
v___y_905_ = v___y_941_;
v_a_906_ = v___x_1012_;
goto v___jp_899_;
}
}
}
}
}
v___jp_1015_:
{
if (v_trimProofs_816_ == 0)
{
lean_dec_ref(v___y_1017_);
v_proof_869_ = v___y_1016_;
v___y_870_ = v___y_1018_;
v___y_871_ = v___y_1019_;
goto v___jp_868_;
}
else
{
lean_object* v_options_1020_; uint8_t v_hasTrace_1021_; 
lean_dec_ref(v___y_1016_);
v_options_1020_ = lean_ctor_get(v___y_1018_, 2);
v_hasTrace_1021_ = lean_ctor_get_uint8(v_options_1020_, sizeof(void*)*1);
if (v_hasTrace_1021_ == 0)
{
lean_object* v_ref_1022_; lean_object* v___x_1023_; 
lean_del_object(v___x_824_);
v_ref_1022_ = lean_ctor_get(v___y_1018_, 5);
v___x_1023_ = l_IO_lazyPure___redArg(v___y_1017_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_object* v_a_1024_; lean_object* v___x_1025_; 
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
lean_inc(v_a_1024_);
lean_dec_ref_known(v___x_1023_, 1);
v___x_1025_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__4___redArg(v_a_1024_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1033_; 
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1028_ = v___x_1025_;
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_1025_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1031_; 
if (v_isShared_1029_ == 0)
{
v___x_1031_ = v___x_1028_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_a_1026_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
}
else
{
lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1045_; 
v_a_1034_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1036_ = v___x_1025_;
v_isShared_1037_ = v_isSharedCheck_1045_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v___x_1025_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1045_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1043_; 
v___x_1038_ = lean_io_error_to_string(v_a_1034_);
v___x_1039_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1038_);
v___x_1040_ = l_Lean_MessageData_ofFormat(v___x_1039_);
lean_inc(v_ref_1022_);
v___x_1041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1041_, 0, v_ref_1022_);
lean_ctor_set(v___x_1041_, 1, v___x_1040_);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 0, v___x_1041_);
v___x_1043_ = v___x_1036_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v___x_1041_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
}
else
{
lean_object* v_a_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1057_; 
v_a_1046_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1048_ = v___x_1023_;
v_isShared_1049_ = v_isSharedCheck_1057_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_a_1046_);
lean_dec(v___x_1023_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1057_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1055_; 
v___x_1050_ = lean_io_error_to_string(v_a_1046_);
v___x_1051_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1050_);
v___x_1052_ = l_Lean_MessageData_ofFormat(v___x_1051_);
lean_inc(v_ref_1022_);
v___x_1053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1053_, 0, v_ref_1022_);
lean_ctor_set(v___x_1053_, 1, v___x_1052_);
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 0, v___x_1053_);
v___x_1055_ = v___x_1048_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v___x_1053_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
}
else
{
lean_object* v_ref_1058_; lean_object* v_inheritedTraceOptions_1059_; lean_object* v___x_1060_; uint8_t v___x_1061_; 
v_ref_1058_ = lean_ctor_get(v___y_1018_, 5);
v_inheritedTraceOptions_1059_ = lean_ctor_get(v___y_1018_, 13);
v___x_1060_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6);
v___x_1061_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1059_, v_options_1020_, v___x_1060_);
if (v___x_1061_ == 0)
{
lean_object* v___x_1062_; uint8_t v___x_1063_; 
v___x_1062_ = l_Lean_trace_profiler;
v___x_1063_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_options_1020_, v___x_1062_);
if (v___x_1063_ == 0)
{
lean_object* v___x_1064_; 
v___x_1064_ = l_IO_lazyPure___redArg(v___y_1017_);
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_object* v_a_1065_; lean_object* v___x_1066_; 
v_a_1065_ = lean_ctor_get(v___x_1064_, 0);
lean_inc(v_a_1065_);
lean_dec_ref_known(v___x_1064_, 1);
v___x_1066_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__4___redArg(v_a_1065_);
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_object* v_a_1067_; 
v_a_1067_ = lean_ctor_get(v___x_1066_, 0);
lean_inc(v_a_1067_);
lean_dec_ref_known(v___x_1066_, 1);
v_proof_833_ = v_a_1067_;
v___y_834_ = v___y_1018_;
v_options_835_ = v_options_1020_;
v_inheritedTraceOptions_836_ = v_inheritedTraceOptions_1059_;
v___y_837_ = v___y_1019_;
goto v___jp_832_;
}
else
{
lean_object* v_a_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1079_; 
lean_del_object(v___x_824_);
v_a_1068_ = lean_ctor_get(v___x_1066_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1070_ = v___x_1066_;
v_isShared_1071_ = v_isSharedCheck_1079_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_a_1068_);
lean_dec(v___x_1066_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1079_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1077_; 
v___x_1072_ = lean_io_error_to_string(v_a_1068_);
v___x_1073_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1072_);
v___x_1074_ = l_Lean_MessageData_ofFormat(v___x_1073_);
lean_inc(v_ref_1058_);
v___x_1075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1075_, 0, v_ref_1058_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
if (v_isShared_1071_ == 0)
{
lean_ctor_set(v___x_1070_, 0, v___x_1075_);
v___x_1077_ = v___x_1070_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v___x_1075_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
}
}
else
{
lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1091_; 
lean_del_object(v___x_824_);
v_a_1080_ = lean_ctor_get(v___x_1064_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1082_ = v___x_1064_;
v_isShared_1083_ = v_isSharedCheck_1091_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_1064_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1091_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1089_; 
v___x_1084_ = lean_io_error_to_string(v_a_1080_);
v___x_1085_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1084_);
v___x_1086_ = l_Lean_MessageData_ofFormat(v___x_1085_);
lean_inc(v_ref_1058_);
v___x_1087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1087_, 0, v_ref_1058_);
lean_ctor_set(v___x_1087_, 1, v___x_1086_);
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 0, v___x_1087_);
v___x_1089_ = v___x_1082_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v___x_1087_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
}
else
{
v___y_937_ = v_ref_1058_;
v___y_938_ = v_options_1020_;
v___y_939_ = v___y_1018_;
v___y_940_ = v___y_1019_;
v___y_941_ = v___x_1061_;
v___y_942_ = v___y_1017_;
goto v___jp_936_;
}
}
else
{
v___y_937_ = v_ref_1058_;
v___y_938_ = v_options_1020_;
v___y_939_ = v___y_1018_;
v___y_940_ = v___y_1019_;
v___y_941_ = v___x_1061_;
v___y_942_ = v___y_1017_;
goto v___jp_936_;
}
}
}
}
v___jp_1092_:
{
lean_object* v___f_1094_; 
lean_inc_ref(v_a_1093_);
v___f_1094_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__2___boxed), 2, 1);
lean_closure_set(v___f_1094_, 0, v_a_1093_);
if (v_hasTrace_828_ == 0)
{
v___y_1016_ = v_a_1093_;
v___y_1017_ = v___f_1094_;
v___y_1018_ = v_a_817_;
v___y_1019_ = v_a_818_;
goto v___jp_1015_;
}
else
{
lean_object* v___x_1095_; uint8_t v___x_1096_; 
v___x_1095_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6);
v___x_1096_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_827_, v_options_821_, v___x_1095_);
if (v___x_1096_ == 0)
{
v___y_1016_ = v_a_1093_;
v___y_1017_ = v___f_1094_;
v___y_1018_ = v_a_817_;
v___y_1019_ = v_a_818_;
goto v___jp_1015_;
}
else
{
lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1097_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__7));
v___x_1098_ = lean_array_get_size(v_a_1093_);
v___x_1099_ = l_Nat_reprFast(v___x_1098_);
v___x_1100_ = lean_string_append(v___x_1097_, v___x_1099_);
lean_dec_ref(v___x_1099_);
v___x_1101_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__10));
v___x_1102_ = lean_string_append(v___x_1100_, v___x_1101_);
v___x_1103_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1102_);
v___x_1104_ = l_Lean_MessageData_ofFormat(v___x_1103_);
v___x_1105_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0(v___x_831_, v___x_1104_, v_a_817_, v_a_818_);
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_dec_ref_known(v___x_1105_, 1);
v___y_1016_ = v_a_1093_;
v___y_1017_ = v___f_1094_;
v___y_1018_ = v_a_817_;
v___y_1019_ = v_a_818_;
goto v___jp_1015_;
}
else
{
lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1113_; 
lean_dec_ref(v___f_1094_);
lean_dec_ref(v_a_1093_);
lean_del_object(v___x_824_);
v_a_1106_ = lean_ctor_get(v___x_1105_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1108_ = v___x_1105_;
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v___x_1105_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1111_; 
if (v_isShared_1109_ == 0)
{
v___x_1111_ = v___x_1108_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_a_1106_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
}
}
}
v___jp_1114_:
{
if (lean_obj_tag(v___y_1115_) == 0)
{
lean_object* v_a_1116_; 
v_a_1116_ = lean_ctor_get(v___y_1115_, 0);
lean_inc(v_a_1116_);
lean_dec_ref_known(v___y_1115_, 1);
v_a_1093_ = v_a_1116_;
goto v___jp_1092_;
}
else
{
lean_del_object(v___x_824_);
return v___y_1115_;
}
}
}
}
else
{
lean_object* v_a_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1269_; 
v_a_1257_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1259_ = v___x_820_;
v_isShared_1260_ = v_isSharedCheck_1269_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_a_1257_);
lean_dec(v___x_820_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1269_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v_ref_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1267_; 
v_ref_1261_ = lean_ctor_get(v_a_817_, 5);
v___x_1262_ = lean_io_error_to_string(v_a_1257_);
v___x_1263_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1262_);
v___x_1264_ = l_Lean_MessageData_ofFormat(v___x_1263_);
lean_inc(v_ref_1261_);
v___x_1265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1265_, 0, v_ref_1261_);
lean_ctor_set(v___x_1265_, 1, v___x_1264_);
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 0, v___x_1265_);
v___x_1267_ = v___x_1259_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v___x_1265_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___boxed(lean_object* v_lratPath_1270_, lean_object* v_trimProofs_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_){
_start:
{
uint8_t v_trimProofs_boxed_1275_; lean_object* v_res_1276_; 
v_trimProofs_boxed_1275_ = lean_unbox(v_trimProofs_1271_);
v_res_1276_ = l_Lean_Meta_Tactic_BVDecide_LratCert_load(v_lratPath_1270_, v_trimProofs_boxed_1275_, v_a_1272_, v_a_1273_);
lean_dec(v_a_1273_);
lean_dec_ref(v_a_1272_);
lean_dec_ref(v_lratPath_1270_);
return v_res_1276_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__6(lean_object* v_00_u03b1_1277_, lean_object* v_x_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v___x_1282_; 
v___x_1282_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__6___redArg(v_x_1278_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__6___boxed(lean_object* v_00_u03b1_1283_, lean_object* v_x_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_){
_start:
{
lean_object* v_res_1288_; 
v_res_1288_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__6(v_00_u03b1_1283_, v_x_1284_, v___y_1285_, v___y_1286_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
return v_res_1288_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5(lean_object* v_00_u03b1_1289_, lean_object* v_msg_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_){
_start:
{
lean_object* v___x_1294_; 
v___x_1294_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5___redArg(v_msg_1290_, v___y_1291_, v___y_1292_);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5___boxed(lean_object* v_00_u03b1_1295_, lean_object* v_msg_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_){
_start:
{
lean_object* v_res_1300_; 
v_res_1300_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5(v_00_u03b1_1295_, v_msg_1296_, v___y_1297_, v___y_1298_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
return v_res_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(lean_object* v_lratPath_1301_, uint8_t v_trimProofs_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_){
_start:
{
lean_object* v___x_1306_; 
v___x_1306_ = l_Lean_Meta_Tactic_BVDecide_LratCert_load(v_lratPath_1301_, v_trimProofs_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1306_) == 0)
{
lean_object* v_a_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1315_; 
v_a_1307_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1315_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1315_ == 0)
{
v___x_1309_ = v___x_1306_;
v_isShared_1310_ = v_isSharedCheck_1315_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_a_1307_);
lean_dec(v___x_1306_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1315_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1311_; lean_object* v___x_1313_; 
v___x_1311_ = l_Std_Tactic_BVDecide_LRAT_lratProofToString(v_a_1307_);
lean_dec(v_a_1307_);
if (v_isShared_1310_ == 0)
{
lean_ctor_set(v___x_1309_, 0, v___x_1311_);
v___x_1313_ = v___x_1309_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v___x_1311_);
v___x_1313_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
return v___x_1313_;
}
}
}
else
{
lean_object* v_a_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1323_; 
v_a_1316_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1318_ = v___x_1306_;
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_a_1316_);
lean_dec(v___x_1306_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1321_; 
if (v_isShared_1319_ == 0)
{
v___x_1321_ = v___x_1318_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_a_1316_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
return v___x_1321_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile___boxed(lean_object* v_lratPath_1324_, lean_object* v_trimProofs_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_){
_start:
{
uint8_t v_trimProofs_boxed_1329_; lean_object* v_res_1330_; 
v_trimProofs_boxed_1329_ = lean_unbox(v_trimProofs_1325_);
v_res_1330_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_1324_, v_trimProofs_boxed_1329_, v_a_1326_, v_a_1327_);
lean_dec(v_a_1327_);
lean_dec_ref(v_a_1326_);
lean_dec_ref(v_lratPath_1324_);
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg___lam__0(lean_object* v_snd_1331_, lean_object* v___y_1332_, lean_object* v_a_x3f_1333_){
_start:
{
lean_object* v___x_1335_; 
v___x_1335_ = lean_io_remove_file(v_snd_1331_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v_a_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1343_; 
v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1338_ = v___x_1335_;
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_a_1336_);
lean_dec(v___x_1335_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v___x_1341_; 
if (v_isShared_1339_ == 0)
{
v___x_1341_ = v___x_1338_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_a_1336_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
}
else
{
lean_object* v_a_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1356_; 
v_a_1344_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1346_ = v___x_1335_;
v_isShared_1347_ = v_isSharedCheck_1356_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_a_1344_);
lean_dec(v___x_1335_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1356_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v_ref_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1354_; 
v_ref_1348_ = lean_ctor_get(v___y_1332_, 5);
v___x_1349_ = lean_io_error_to_string(v_a_1344_);
v___x_1350_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1349_);
v___x_1351_ = l_Lean_MessageData_ofFormat(v___x_1350_);
lean_inc(v_ref_1348_);
v___x_1352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1352_, 0, v_ref_1348_);
lean_ctor_set(v___x_1352_, 1, v___x_1351_);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 0, v___x_1352_);
v___x_1354_ = v___x_1346_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v___x_1352_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg___lam__0___boxed(lean_object* v_snd_1357_, lean_object* v___y_1358_, lean_object* v_a_x3f_1359_, lean_object* v___y_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg___lam__0(v_snd_1357_, v___y_1358_, v_a_x3f_1359_);
lean_dec(v_a_x3f_1359_);
lean_dec_ref(v___y_1358_);
lean_dec_ref(v_snd_1357_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg(lean_object* v_f_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_){
_start:
{
lean_object* v___x_1366_; 
v___x_1366_ = lean_io_create_tempfile();
if (lean_obj_tag(v___x_1366_) == 0)
{
lean_object* v_a_1367_; lean_object* v_fst_1368_; lean_object* v_snd_1369_; lean_object* v_r_1370_; 
v_a_1367_ = lean_ctor_get(v___x_1366_, 0);
lean_inc(v_a_1367_);
lean_dec_ref_known(v___x_1366_, 1);
v_fst_1368_ = lean_ctor_get(v_a_1367_, 0);
lean_inc(v_fst_1368_);
v_snd_1369_ = lean_ctor_get(v_a_1367_, 1);
lean_inc_n(v_snd_1369_, 2);
lean_dec(v_a_1367_);
lean_inc(v___y_1364_);
lean_inc_ref(v___y_1363_);
v_r_1370_ = lean_apply_5(v_f_1362_, v_fst_1368_, v_snd_1369_, v___y_1363_, v___y_1364_, lean_box(0));
if (lean_obj_tag(v_r_1370_) == 0)
{
lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1395_; 
v_a_1371_ = lean_ctor_get(v_r_1370_, 0);
v_isSharedCheck_1395_ = !lean_is_exclusive(v_r_1370_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1373_ = v_r_1370_;
v_isShared_1374_ = v_isSharedCheck_1395_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v_r_1370_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1395_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1376_; 
lean_inc(v_a_1371_);
if (v_isShared_1374_ == 0)
{
lean_ctor_set_tag(v___x_1373_, 1);
v___x_1376_ = v___x_1373_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_a_1371_);
v___x_1376_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
lean_object* v___x_1377_; 
v___x_1377_ = l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg___lam__0(v_snd_1369_, v___y_1363_, v___x_1376_);
lean_dec_ref(v___x_1376_);
lean_dec(v_snd_1369_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1384_; 
v_isSharedCheck_1384_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1384_ == 0)
{
lean_object* v_unused_1385_; 
v_unused_1385_ = lean_ctor_get(v___x_1377_, 0);
lean_dec(v_unused_1385_);
v___x_1379_ = v___x_1377_;
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
else
{
lean_dec(v___x_1377_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1382_; 
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 0, v_a_1371_);
v___x_1382_ = v___x_1379_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_a_1371_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
}
else
{
lean_object* v_a_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1393_; 
lean_dec(v_a_1371_);
v_a_1386_ = lean_ctor_get(v___x_1377_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1388_ = v___x_1377_;
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_a_1386_);
lean_dec(v___x_1377_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1391_; 
if (v_isShared_1389_ == 0)
{
v___x_1391_ = v___x_1388_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_a_1386_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
}
}
}
}
else
{
lean_object* v_a_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
v_a_1396_ = lean_ctor_get(v_r_1370_, 0);
lean_inc(v_a_1396_);
lean_dec_ref_known(v_r_1370_, 1);
v___x_1397_ = lean_box(0);
v___x_1398_ = l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg___lam__0(v_snd_1369_, v___y_1363_, v___x_1397_);
lean_dec(v_snd_1369_);
if (lean_obj_tag(v___x_1398_) == 0)
{
lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1405_; 
v_isSharedCheck_1405_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1405_ == 0)
{
lean_object* v_unused_1406_; 
v_unused_1406_ = lean_ctor_get(v___x_1398_, 0);
lean_dec(v_unused_1406_);
v___x_1400_ = v___x_1398_;
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
else
{
lean_dec(v___x_1398_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1403_; 
if (v_isShared_1401_ == 0)
{
lean_ctor_set_tag(v___x_1400_, 1);
lean_ctor_set(v___x_1400_, 0, v_a_1396_);
v___x_1403_ = v___x_1400_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v_a_1396_);
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
lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1414_; 
lean_dec(v_a_1396_);
v_a_1407_ = lean_ctor_get(v___x_1398_, 0);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1409_ = v___x_1398_;
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_dec(v___x_1398_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1412_; 
if (v_isShared_1410_ == 0)
{
v___x_1412_ = v___x_1409_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_a_1407_);
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
else
{
lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1427_; 
lean_dec_ref(v_f_1362_);
v_a_1415_ = lean_ctor_get(v___x_1366_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1366_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1417_ = v___x_1366_;
v_isShared_1418_ = v_isSharedCheck_1427_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_dec(v___x_1366_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1427_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v_ref_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1425_; 
v_ref_1419_ = lean_ctor_get(v___y_1363_, 5);
v___x_1420_ = lean_io_error_to_string(v_a_1415_);
v___x_1421_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1421_, 0, v___x_1420_);
v___x_1422_ = l_Lean_MessageData_ofFormat(v___x_1421_);
lean_inc(v_ref_1419_);
v___x_1423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1423_, 0, v_ref_1419_);
lean_ctor_set(v___x_1423_, 1, v___x_1422_);
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 0, v___x_1423_);
v___x_1425_ = v___x_1417_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v___x_1423_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg___boxed(lean_object* v_f_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg(v_f_1428_, v___y_1429_, v___y_1430_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
return v_res_1432_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3(lean_object* v_00_u03b1_1433_, lean_object* v_f_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_){
_start:
{
lean_object* v___x_1438_; 
v___x_1438_ = l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg(v_f_1434_, v___y_1435_, v___y_1436_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___boxed(lean_object* v_00_u03b1_1439_, lean_object* v_f_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_){
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3(v_00_u03b1_1439_, v_f_1440_, v___y_1441_, v___y_1442_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__0(lean_object* v_cnf_1445_, lean_object* v_x_1446_){
_start:
{
lean_object* v___x_1447_; 
v___x_1447_ = l_Std_Sat_CNF_dimacs(v_cnf_1445_);
return v___x_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__0___boxed(lean_object* v_cnf_1448_, lean_object* v_x_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_Lean_Meta_Tactic_BVDecide_runExternal___lam__0(v_cnf_1448_, v_x_1449_);
lean_dec_ref(v_cnf_1448_);
return v_res_1450_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1454_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1___closed__1));
v___x_1455_ = l_Lean_MessageData_ofFormat(v___x_1454_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1(lean_object* v_x_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_){
_start:
{
lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___x_1460_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1___closed__2, &l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1___closed__2);
v___x_1461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1460_);
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1___boxed(lean_object* v_x_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_){
_start:
{
lean_object* v_res_1466_; 
v_res_1466_ = l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1(v_x_1462_, v___y_1463_, v___y_1464_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec_ref(v_x_1462_);
return v_res_1466_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2___closed__2(void){
_start:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1470_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2___closed__1));
v___x_1471_ = l_Lean_MessageData_ofFormat(v___x_1470_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2(lean_object* v_x_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
lean_object* v___x_1476_; lean_object* v___x_1477_; 
v___x_1476_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2___closed__2, &l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2___closed__2);
v___x_1477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1477_, 0, v___x_1476_);
return v___x_1477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2___boxed(lean_object* v_x_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_){
_start:
{
lean_object* v_res_1482_; 
v_res_1482_ = l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2(v_x_1478_, v___y_1479_, v___y_1480_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
lean_dec_ref(v_x_1478_);
return v_res_1482_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3___closed__2(void){
_start:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1486_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3___closed__1));
v___x_1487_ = l_Lean_MessageData_ofFormat(v___x_1486_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3(lean_object* v_x_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___x_1492_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3___closed__2, &l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3___closed__2);
v___x_1493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1493_, 0, v___x_1492_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3___boxed(lean_object* v_x_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_){
_start:
{
lean_object* v_res_1498_; 
v_res_1498_ = l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3(v_x_1494_, v___y_1495_, v___y_1496_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
lean_dec_ref(v_x_1494_);
return v_res_1498_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2_spec__4(lean_object* v_e_1499_){
_start:
{
if (lean_obj_tag(v_e_1499_) == 0)
{
uint8_t v___x_1500_; 
v___x_1500_ = 2;
return v___x_1500_;
}
else
{
uint8_t v___x_1501_; 
v___x_1501_ = 0;
return v___x_1501_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2_spec__4___boxed(lean_object* v_e_1502_){
_start:
{
uint8_t v_res_1503_; lean_object* v_r_1504_; 
v_res_1503_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2_spec__4(v_e_1502_);
lean_dec_ref(v_e_1502_);
v_r_1504_ = lean_box(v_res_1503_);
return v_r_1504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2(lean_object* v_cls_1505_, uint8_t v_collapsed_1506_, lean_object* v_tag_1507_, lean_object* v_opts_1508_, uint8_t v_clsEnabled_1509_, lean_object* v_oldTraces_1510_, lean_object* v_msg_1511_, lean_object* v_resStartStop_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_){
_start:
{
lean_object* v_fst_1516_; lean_object* v_snd_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1607_; 
v_fst_1516_ = lean_ctor_get(v_resStartStop_1512_, 0);
v_snd_1517_ = lean_ctor_get(v_resStartStop_1512_, 1);
v_isSharedCheck_1607_ = !lean_is_exclusive(v_resStartStop_1512_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1519_ = v_resStartStop_1512_;
v_isShared_1520_ = v_isSharedCheck_1607_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_snd_1517_);
lean_inc(v_fst_1516_);
lean_dec(v_resStartStop_1512_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1607_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v___y_1522_; lean_object* v___y_1523_; lean_object* v_data_1524_; lean_object* v_fst_1527_; lean_object* v_snd_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1606_; 
v_fst_1527_ = lean_ctor_get(v_snd_1517_, 0);
v_snd_1528_ = lean_ctor_get(v_snd_1517_, 1);
v_isSharedCheck_1606_ = !lean_is_exclusive(v_snd_1517_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1530_ = v_snd_1517_;
v_isShared_1531_ = v_isSharedCheck_1606_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_snd_1528_);
lean_inc(v_fst_1527_);
lean_dec(v_snd_1517_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1606_;
goto v_resetjp_1529_;
}
v___jp_1521_:
{
lean_object* v___x_1525_; 
lean_inc(v___y_1523_);
v___x_1525_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5(v_oldTraces_1510_, v_data_1524_, v___y_1523_, v___y_1522_, v___y_1513_, v___y_1514_);
if (lean_obj_tag(v___x_1525_) == 0)
{
lean_object* v___x_1526_; 
lean_dec_ref_known(v___x_1525_, 1);
v___x_1526_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__6___redArg(v_fst_1516_);
return v___x_1526_;
}
else
{
lean_dec(v_fst_1516_);
return v___x_1525_;
}
}
v_resetjp_1529_:
{
lean_object* v___x_1532_; uint8_t v___x_1533_; lean_object* v___y_1535_; lean_object* v_a_1536_; uint8_t v___y_1560_; double v___y_1591_; 
v___x_1532_ = l_Lean_trace_profiler;
v___x_1533_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_opts_1508_, v___x_1532_);
if (v___x_1533_ == 0)
{
v___y_1560_ = v___x_1533_;
goto v___jp_1559_;
}
else
{
lean_object* v___x_1596_; uint8_t v___x_1597_; 
v___x_1596_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1597_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_opts_1508_, v___x_1596_);
if (v___x_1597_ == 0)
{
lean_object* v___x_1598_; lean_object* v___x_1599_; double v___x_1600_; double v___x_1601_; double v___x_1602_; 
v___x_1598_ = l_Lean_trace_profiler_threshold;
v___x_1599_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(v_opts_1508_, v___x_1598_);
v___x_1600_ = lean_float_of_nat(v___x_1599_);
v___x_1601_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__5);
v___x_1602_ = lean_float_div(v___x_1600_, v___x_1601_);
v___y_1591_ = v___x_1602_;
goto v___jp_1590_;
}
else
{
lean_object* v___x_1603_; lean_object* v___x_1604_; double v___x_1605_; 
v___x_1603_ = l_Lean_trace_profiler_threshold;
v___x_1604_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(v_opts_1508_, v___x_1603_);
v___x_1605_ = lean_float_of_nat(v___x_1604_);
v___y_1591_ = v___x_1605_;
goto v___jp_1590_;
}
}
v___jp_1534_:
{
uint8_t v_result_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1542_; 
v_result_1537_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2_spec__4(v_fst_1516_);
v___x_1538_ = l_Lean_TraceResult_toEmoji(v_result_1537_);
v___x_1539_ = l_Lean_stringToMessageData(v___x_1538_);
v___x_1540_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__1);
if (v_isShared_1531_ == 0)
{
lean_ctor_set_tag(v___x_1530_, 7);
lean_ctor_set(v___x_1530_, 1, v___x_1540_);
lean_ctor_set(v___x_1530_, 0, v___x_1539_);
v___x_1542_ = v___x_1530_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v___x_1539_);
lean_ctor_set(v_reuseFailAlloc_1553_, 1, v___x_1540_);
v___x_1542_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
lean_object* v_m_1544_; 
if (v_isShared_1520_ == 0)
{
lean_ctor_set_tag(v___x_1519_, 7);
lean_ctor_set(v___x_1519_, 1, v_a_1536_);
lean_ctor_set(v___x_1519_, 0, v___x_1542_);
v_m_1544_ = v___x_1519_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v___x_1542_);
lean_ctor_set(v_reuseFailAlloc_1552_, 1, v_a_1536_);
v_m_1544_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; double v___x_1547_; lean_object* v_data_1548_; 
v___x_1545_ = lean_box(v_result_1537_);
v___x_1546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1545_);
v___x_1547_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2);
lean_inc_ref(v_tag_1507_);
lean_inc_ref(v___x_1546_);
lean_inc(v_cls_1505_);
v_data_1548_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1548_, 0, v_cls_1505_);
lean_ctor_set(v_data_1548_, 1, v___x_1546_);
lean_ctor_set(v_data_1548_, 2, v_tag_1507_);
lean_ctor_set_float(v_data_1548_, sizeof(void*)*3, v___x_1547_);
lean_ctor_set_float(v_data_1548_, sizeof(void*)*3 + 8, v___x_1547_);
lean_ctor_set_uint8(v_data_1548_, sizeof(void*)*3 + 16, v_collapsed_1506_);
if (v___x_1533_ == 0)
{
lean_dec_ref_known(v___x_1546_, 1);
lean_dec(v_snd_1528_);
lean_dec(v_fst_1527_);
lean_dec_ref(v_tag_1507_);
lean_dec(v_cls_1505_);
v___y_1522_ = v_m_1544_;
v___y_1523_ = v___y_1535_;
v_data_1524_ = v_data_1548_;
goto v___jp_1521_;
}
else
{
lean_object* v_data_1549_; double v___x_1550_; double v___x_1551_; 
lean_dec_ref_known(v_data_1548_, 3);
v_data_1549_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1549_, 0, v_cls_1505_);
lean_ctor_set(v_data_1549_, 1, v___x_1546_);
lean_ctor_set(v_data_1549_, 2, v_tag_1507_);
v___x_1550_ = lean_unbox_float(v_fst_1527_);
lean_dec(v_fst_1527_);
lean_ctor_set_float(v_data_1549_, sizeof(void*)*3, v___x_1550_);
v___x_1551_ = lean_unbox_float(v_snd_1528_);
lean_dec(v_snd_1528_);
lean_ctor_set_float(v_data_1549_, sizeof(void*)*3 + 8, v___x_1551_);
lean_ctor_set_uint8(v_data_1549_, sizeof(void*)*3 + 16, v_collapsed_1506_);
v___y_1522_ = v_m_1544_;
v___y_1523_ = v___y_1535_;
v_data_1524_ = v_data_1549_;
goto v___jp_1521_;
}
}
}
}
v___jp_1554_:
{
lean_object* v_ref_1555_; lean_object* v___x_1556_; 
v_ref_1555_ = lean_ctor_get(v___y_1513_, 5);
lean_inc(v___y_1514_);
lean_inc_ref(v___y_1513_);
lean_inc(v_fst_1516_);
v___x_1556_ = lean_apply_4(v_msg_1511_, v_fst_1516_, v___y_1513_, v___y_1514_, lean_box(0));
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v_a_1557_; 
v_a_1557_ = lean_ctor_get(v___x_1556_, 0);
lean_inc(v_a_1557_);
lean_dec_ref_known(v___x_1556_, 1);
v___y_1535_ = v_ref_1555_;
v_a_1536_ = v_a_1557_;
goto v___jp_1534_;
}
else
{
lean_object* v___x_1558_; 
lean_dec_ref_known(v___x_1556_, 1);
v___x_1558_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__4);
v___y_1535_ = v_ref_1555_;
v_a_1536_ = v___x_1558_;
goto v___jp_1534_;
}
}
v___jp_1559_:
{
if (v_clsEnabled_1509_ == 0)
{
if (v___y_1560_ == 0)
{
lean_object* v___x_1561_; lean_object* v_traceState_1562_; lean_object* v_env_1563_; lean_object* v_nextMacroScope_1564_; lean_object* v_ngen_1565_; lean_object* v_auxDeclNGen_1566_; lean_object* v_cache_1567_; lean_object* v_messages_1568_; lean_object* v_infoState_1569_; lean_object* v_snapshotTasks_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1589_; 
lean_del_object(v___x_1530_);
lean_dec(v_snd_1528_);
lean_dec(v_fst_1527_);
lean_del_object(v___x_1519_);
lean_dec_ref(v_msg_1511_);
lean_dec_ref(v_tag_1507_);
lean_dec(v_cls_1505_);
v___x_1561_ = lean_st_ref_take(v___y_1514_);
v_traceState_1562_ = lean_ctor_get(v___x_1561_, 4);
v_env_1563_ = lean_ctor_get(v___x_1561_, 0);
v_nextMacroScope_1564_ = lean_ctor_get(v___x_1561_, 1);
v_ngen_1565_ = lean_ctor_get(v___x_1561_, 2);
v_auxDeclNGen_1566_ = lean_ctor_get(v___x_1561_, 3);
v_cache_1567_ = lean_ctor_get(v___x_1561_, 5);
v_messages_1568_ = lean_ctor_get(v___x_1561_, 6);
v_infoState_1569_ = lean_ctor_get(v___x_1561_, 7);
v_snapshotTasks_1570_ = lean_ctor_get(v___x_1561_, 8);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1561_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1572_ = v___x_1561_;
v_isShared_1573_ = v_isSharedCheck_1589_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_snapshotTasks_1570_);
lean_inc(v_infoState_1569_);
lean_inc(v_messages_1568_);
lean_inc(v_cache_1567_);
lean_inc(v_traceState_1562_);
lean_inc(v_auxDeclNGen_1566_);
lean_inc(v_ngen_1565_);
lean_inc(v_nextMacroScope_1564_);
lean_inc(v_env_1563_);
lean_dec(v___x_1561_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1589_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
uint64_t v_tid_1574_; lean_object* v_traces_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1588_; 
v_tid_1574_ = lean_ctor_get_uint64(v_traceState_1562_, sizeof(void*)*1);
v_traces_1575_ = lean_ctor_get(v_traceState_1562_, 0);
v_isSharedCheck_1588_ = !lean_is_exclusive(v_traceState_1562_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1577_ = v_traceState_1562_;
v_isShared_1578_ = v_isSharedCheck_1588_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_traces_1575_);
lean_dec(v_traceState_1562_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1588_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1579_; lean_object* v___x_1581_; 
v___x_1579_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1510_, v_traces_1575_);
lean_dec_ref(v_traces_1575_);
if (v_isShared_1578_ == 0)
{
lean_ctor_set(v___x_1577_, 0, v___x_1579_);
v___x_1581_ = v___x_1577_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v___x_1579_);
lean_ctor_set_uint64(v_reuseFailAlloc_1587_, sizeof(void*)*1, v_tid_1574_);
v___x_1581_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
lean_object* v___x_1583_; 
if (v_isShared_1573_ == 0)
{
lean_ctor_set(v___x_1572_, 4, v___x_1581_);
v___x_1583_ = v___x_1572_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_env_1563_);
lean_ctor_set(v_reuseFailAlloc_1586_, 1, v_nextMacroScope_1564_);
lean_ctor_set(v_reuseFailAlloc_1586_, 2, v_ngen_1565_);
lean_ctor_set(v_reuseFailAlloc_1586_, 3, v_auxDeclNGen_1566_);
lean_ctor_set(v_reuseFailAlloc_1586_, 4, v___x_1581_);
lean_ctor_set(v_reuseFailAlloc_1586_, 5, v_cache_1567_);
lean_ctor_set(v_reuseFailAlloc_1586_, 6, v_messages_1568_);
lean_ctor_set(v_reuseFailAlloc_1586_, 7, v_infoState_1569_);
lean_ctor_set(v_reuseFailAlloc_1586_, 8, v_snapshotTasks_1570_);
v___x_1583_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1584_ = lean_st_ref_set(v___y_1514_, v___x_1583_);
v___x_1585_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__6___redArg(v_fst_1516_);
return v___x_1585_;
}
}
}
}
}
else
{
goto v___jp_1554_;
}
}
else
{
goto v___jp_1554_;
}
}
v___jp_1590_:
{
double v___x_1592_; double v___x_1593_; double v___x_1594_; uint8_t v___x_1595_; 
v___x_1592_ = lean_unbox_float(v_snd_1528_);
v___x_1593_ = lean_unbox_float(v_fst_1527_);
v___x_1594_ = lean_float_sub(v___x_1592_, v___x_1593_);
v___x_1595_ = lean_float_decLt(v___y_1591_, v___x_1594_);
v___y_1560_ = v___x_1595_;
goto v___jp_1559_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2___boxed(lean_object* v_cls_1608_, lean_object* v_collapsed_1609_, lean_object* v_tag_1610_, lean_object* v_opts_1611_, lean_object* v_clsEnabled_1612_, lean_object* v_oldTraces_1613_, lean_object* v_msg_1614_, lean_object* v_resStartStop_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_){
_start:
{
uint8_t v_collapsed_boxed_1619_; uint8_t v_clsEnabled_boxed_1620_; lean_object* v_res_1621_; 
v_collapsed_boxed_1619_ = lean_unbox(v_collapsed_1609_);
v_clsEnabled_boxed_1620_ = lean_unbox(v_clsEnabled_1612_);
v_res_1621_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2(v_cls_1608_, v_collapsed_boxed_1619_, v_tag_1610_, v_opts_1611_, v_clsEnabled_boxed_1620_, v_oldTraces_1613_, v_msg_1614_, v_resStartStop_1615_, v___y_1616_, v___y_1617_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
lean_dec_ref(v_opts_1611_);
return v_res_1621_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0_spec__0(lean_object* v_e_1622_){
_start:
{
if (lean_obj_tag(v_e_1622_) == 0)
{
uint8_t v___x_1623_; 
v___x_1623_ = 2;
return v___x_1623_;
}
else
{
uint8_t v___x_1624_; 
v___x_1624_ = 0;
return v___x_1624_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0_spec__0___boxed(lean_object* v_e_1625_){
_start:
{
uint8_t v_res_1626_; lean_object* v_r_1627_; 
v_res_1626_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0_spec__0(v_e_1625_);
lean_dec_ref(v_e_1625_);
v_r_1627_ = lean_box(v_res_1626_);
return v_r_1627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0(lean_object* v_cls_1628_, uint8_t v_collapsed_1629_, lean_object* v_tag_1630_, lean_object* v_opts_1631_, uint8_t v_clsEnabled_1632_, lean_object* v_oldTraces_1633_, lean_object* v_msg_1634_, lean_object* v_resStartStop_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_){
_start:
{
lean_object* v_fst_1639_; lean_object* v_snd_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1738_; 
v_fst_1639_ = lean_ctor_get(v_resStartStop_1635_, 0);
v_snd_1640_ = lean_ctor_get(v_resStartStop_1635_, 1);
v_isSharedCheck_1738_ = !lean_is_exclusive(v_resStartStop_1635_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1642_ = v_resStartStop_1635_;
v_isShared_1643_ = v_isSharedCheck_1738_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_snd_1640_);
lean_inc(v_fst_1639_);
lean_dec(v_resStartStop_1635_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1738_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___y_1645_; lean_object* v___y_1646_; lean_object* v_data_1647_; lean_object* v_fst_1658_; lean_object* v_snd_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1737_; 
v_fst_1658_ = lean_ctor_get(v_snd_1640_, 0);
v_snd_1659_ = lean_ctor_get(v_snd_1640_, 1);
v_isSharedCheck_1737_ = !lean_is_exclusive(v_snd_1640_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1661_ = v_snd_1640_;
v_isShared_1662_ = v_isSharedCheck_1737_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_snd_1659_);
lean_inc(v_fst_1658_);
lean_dec(v_snd_1640_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1737_;
goto v_resetjp_1660_;
}
v___jp_1644_:
{
lean_object* v___x_1648_; 
lean_inc(v___y_1646_);
v___x_1648_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5(v_oldTraces_1633_, v_data_1647_, v___y_1646_, v___y_1645_, v___y_1636_, v___y_1637_);
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_object* v___x_1649_; 
lean_dec_ref_known(v___x_1648_, 1);
v___x_1649_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__6___redArg(v_fst_1639_);
return v___x_1649_;
}
else
{
lean_object* v_a_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1657_; 
lean_dec(v_fst_1639_);
v_a_1650_ = lean_ctor_get(v___x_1648_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1652_ = v___x_1648_;
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_a_1650_);
lean_dec(v___x_1648_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1655_; 
if (v_isShared_1653_ == 0)
{
v___x_1655_ = v___x_1652_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_a_1650_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
}
}
}
}
v_resetjp_1660_:
{
lean_object* v___x_1663_; uint8_t v___x_1664_; lean_object* v___y_1666_; lean_object* v_a_1667_; uint8_t v___y_1691_; double v___y_1722_; 
v___x_1663_ = l_Lean_trace_profiler;
v___x_1664_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_opts_1631_, v___x_1663_);
if (v___x_1664_ == 0)
{
v___y_1691_ = v___x_1664_;
goto v___jp_1690_;
}
else
{
lean_object* v___x_1727_; uint8_t v___x_1728_; 
v___x_1727_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1728_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_opts_1631_, v___x_1727_);
if (v___x_1728_ == 0)
{
lean_object* v___x_1729_; lean_object* v___x_1730_; double v___x_1731_; double v___x_1732_; double v___x_1733_; 
v___x_1729_ = l_Lean_trace_profiler_threshold;
v___x_1730_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(v_opts_1631_, v___x_1729_);
v___x_1731_ = lean_float_of_nat(v___x_1730_);
v___x_1732_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__5);
v___x_1733_ = lean_float_div(v___x_1731_, v___x_1732_);
v___y_1722_ = v___x_1733_;
goto v___jp_1721_;
}
else
{
lean_object* v___x_1734_; lean_object* v___x_1735_; double v___x_1736_; 
v___x_1734_ = l_Lean_trace_profiler_threshold;
v___x_1735_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(v_opts_1631_, v___x_1734_);
v___x_1736_ = lean_float_of_nat(v___x_1735_);
v___y_1722_ = v___x_1736_;
goto v___jp_1721_;
}
}
v___jp_1665_:
{
uint8_t v_result_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1673_; 
v_result_1668_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0_spec__0(v_fst_1639_);
v___x_1669_ = l_Lean_TraceResult_toEmoji(v_result_1668_);
v___x_1670_ = l_Lean_stringToMessageData(v___x_1669_);
v___x_1671_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__1);
if (v_isShared_1662_ == 0)
{
lean_ctor_set_tag(v___x_1661_, 7);
lean_ctor_set(v___x_1661_, 1, v___x_1671_);
lean_ctor_set(v___x_1661_, 0, v___x_1670_);
v___x_1673_ = v___x_1661_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v___x_1670_);
lean_ctor_set(v_reuseFailAlloc_1684_, 1, v___x_1671_);
v___x_1673_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
lean_object* v_m_1675_; 
if (v_isShared_1643_ == 0)
{
lean_ctor_set_tag(v___x_1642_, 7);
lean_ctor_set(v___x_1642_, 1, v_a_1667_);
lean_ctor_set(v___x_1642_, 0, v___x_1673_);
v_m_1675_ = v___x_1642_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v___x_1673_);
lean_ctor_set(v_reuseFailAlloc_1683_, 1, v_a_1667_);
v_m_1675_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
lean_object* v___x_1676_; lean_object* v___x_1677_; double v___x_1678_; lean_object* v_data_1679_; 
v___x_1676_ = lean_box(v_result_1668_);
v___x_1677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1676_);
v___x_1678_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2);
lean_inc_ref(v_tag_1630_);
lean_inc_ref(v___x_1677_);
lean_inc(v_cls_1628_);
v_data_1679_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1679_, 0, v_cls_1628_);
lean_ctor_set(v_data_1679_, 1, v___x_1677_);
lean_ctor_set(v_data_1679_, 2, v_tag_1630_);
lean_ctor_set_float(v_data_1679_, sizeof(void*)*3, v___x_1678_);
lean_ctor_set_float(v_data_1679_, sizeof(void*)*3 + 8, v___x_1678_);
lean_ctor_set_uint8(v_data_1679_, sizeof(void*)*3 + 16, v_collapsed_1629_);
if (v___x_1664_ == 0)
{
lean_dec_ref_known(v___x_1677_, 1);
lean_dec(v_snd_1659_);
lean_dec(v_fst_1658_);
lean_dec_ref(v_tag_1630_);
lean_dec(v_cls_1628_);
v___y_1645_ = v_m_1675_;
v___y_1646_ = v___y_1666_;
v_data_1647_ = v_data_1679_;
goto v___jp_1644_;
}
else
{
lean_object* v_data_1680_; double v___x_1681_; double v___x_1682_; 
lean_dec_ref_known(v_data_1679_, 3);
v_data_1680_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1680_, 0, v_cls_1628_);
lean_ctor_set(v_data_1680_, 1, v___x_1677_);
lean_ctor_set(v_data_1680_, 2, v_tag_1630_);
v___x_1681_ = lean_unbox_float(v_fst_1658_);
lean_dec(v_fst_1658_);
lean_ctor_set_float(v_data_1680_, sizeof(void*)*3, v___x_1681_);
v___x_1682_ = lean_unbox_float(v_snd_1659_);
lean_dec(v_snd_1659_);
lean_ctor_set_float(v_data_1680_, sizeof(void*)*3 + 8, v___x_1682_);
lean_ctor_set_uint8(v_data_1680_, sizeof(void*)*3 + 16, v_collapsed_1629_);
v___y_1645_ = v_m_1675_;
v___y_1646_ = v___y_1666_;
v_data_1647_ = v_data_1680_;
goto v___jp_1644_;
}
}
}
}
v___jp_1685_:
{
lean_object* v_ref_1686_; lean_object* v___x_1687_; 
v_ref_1686_ = lean_ctor_get(v___y_1636_, 5);
lean_inc(v___y_1637_);
lean_inc_ref(v___y_1636_);
lean_inc(v_fst_1639_);
v___x_1687_ = lean_apply_4(v_msg_1634_, v_fst_1639_, v___y_1636_, v___y_1637_, lean_box(0));
if (lean_obj_tag(v___x_1687_) == 0)
{
lean_object* v_a_1688_; 
v_a_1688_ = lean_ctor_get(v___x_1687_, 0);
lean_inc(v_a_1688_);
lean_dec_ref_known(v___x_1687_, 1);
v___y_1666_ = v_ref_1686_;
v_a_1667_ = v_a_1688_;
goto v___jp_1665_;
}
else
{
lean_object* v___x_1689_; 
lean_dec_ref_known(v___x_1687_, 1);
v___x_1689_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__4);
v___y_1666_ = v_ref_1686_;
v_a_1667_ = v___x_1689_;
goto v___jp_1665_;
}
}
v___jp_1690_:
{
if (v_clsEnabled_1632_ == 0)
{
if (v___y_1691_ == 0)
{
lean_object* v___x_1692_; lean_object* v_traceState_1693_; lean_object* v_env_1694_; lean_object* v_nextMacroScope_1695_; lean_object* v_ngen_1696_; lean_object* v_auxDeclNGen_1697_; lean_object* v_cache_1698_; lean_object* v_messages_1699_; lean_object* v_infoState_1700_; lean_object* v_snapshotTasks_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1720_; 
lean_del_object(v___x_1661_);
lean_dec(v_snd_1659_);
lean_dec(v_fst_1658_);
lean_del_object(v___x_1642_);
lean_dec_ref(v_msg_1634_);
lean_dec_ref(v_tag_1630_);
lean_dec(v_cls_1628_);
v___x_1692_ = lean_st_ref_take(v___y_1637_);
v_traceState_1693_ = lean_ctor_get(v___x_1692_, 4);
v_env_1694_ = lean_ctor_get(v___x_1692_, 0);
v_nextMacroScope_1695_ = lean_ctor_get(v___x_1692_, 1);
v_ngen_1696_ = lean_ctor_get(v___x_1692_, 2);
v_auxDeclNGen_1697_ = lean_ctor_get(v___x_1692_, 3);
v_cache_1698_ = lean_ctor_get(v___x_1692_, 5);
v_messages_1699_ = lean_ctor_get(v___x_1692_, 6);
v_infoState_1700_ = lean_ctor_get(v___x_1692_, 7);
v_snapshotTasks_1701_ = lean_ctor_get(v___x_1692_, 8);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1692_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1703_ = v___x_1692_;
v_isShared_1704_ = v_isSharedCheck_1720_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_snapshotTasks_1701_);
lean_inc(v_infoState_1700_);
lean_inc(v_messages_1699_);
lean_inc(v_cache_1698_);
lean_inc(v_traceState_1693_);
lean_inc(v_auxDeclNGen_1697_);
lean_inc(v_ngen_1696_);
lean_inc(v_nextMacroScope_1695_);
lean_inc(v_env_1694_);
lean_dec(v___x_1692_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1720_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
uint64_t v_tid_1705_; lean_object* v_traces_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1719_; 
v_tid_1705_ = lean_ctor_get_uint64(v_traceState_1693_, sizeof(void*)*1);
v_traces_1706_ = lean_ctor_get(v_traceState_1693_, 0);
v_isSharedCheck_1719_ = !lean_is_exclusive(v_traceState_1693_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1708_ = v_traceState_1693_;
v_isShared_1709_ = v_isSharedCheck_1719_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_traces_1706_);
lean_dec(v_traceState_1693_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1719_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1710_; lean_object* v___x_1712_; 
v___x_1710_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1633_, v_traces_1706_);
lean_dec_ref(v_traces_1706_);
if (v_isShared_1709_ == 0)
{
lean_ctor_set(v___x_1708_, 0, v___x_1710_);
v___x_1712_ = v___x_1708_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v___x_1710_);
lean_ctor_set_uint64(v_reuseFailAlloc_1718_, sizeof(void*)*1, v_tid_1705_);
v___x_1712_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
lean_object* v___x_1714_; 
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 4, v___x_1712_);
v___x_1714_ = v___x_1703_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_env_1694_);
lean_ctor_set(v_reuseFailAlloc_1717_, 1, v_nextMacroScope_1695_);
lean_ctor_set(v_reuseFailAlloc_1717_, 2, v_ngen_1696_);
lean_ctor_set(v_reuseFailAlloc_1717_, 3, v_auxDeclNGen_1697_);
lean_ctor_set(v_reuseFailAlloc_1717_, 4, v___x_1712_);
lean_ctor_set(v_reuseFailAlloc_1717_, 5, v_cache_1698_);
lean_ctor_set(v_reuseFailAlloc_1717_, 6, v_messages_1699_);
lean_ctor_set(v_reuseFailAlloc_1717_, 7, v_infoState_1700_);
lean_ctor_set(v_reuseFailAlloc_1717_, 8, v_snapshotTasks_1701_);
v___x_1714_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; 
v___x_1715_ = lean_st_ref_set(v___y_1637_, v___x_1714_);
v___x_1716_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__6___redArg(v_fst_1639_);
return v___x_1716_;
}
}
}
}
}
else
{
goto v___jp_1685_;
}
}
else
{
goto v___jp_1685_;
}
}
v___jp_1721_:
{
double v___x_1723_; double v___x_1724_; double v___x_1725_; uint8_t v___x_1726_; 
v___x_1723_ = lean_unbox_float(v_snd_1659_);
v___x_1724_ = lean_unbox_float(v_fst_1658_);
v___x_1725_ = lean_float_sub(v___x_1723_, v___x_1724_);
v___x_1726_ = lean_float_decLt(v___y_1722_, v___x_1725_);
v___y_1691_ = v___x_1726_;
goto v___jp_1690_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0___boxed(lean_object* v_cls_1739_, lean_object* v_collapsed_1740_, lean_object* v_tag_1741_, lean_object* v_opts_1742_, lean_object* v_clsEnabled_1743_, lean_object* v_oldTraces_1744_, lean_object* v_msg_1745_, lean_object* v_resStartStop_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_){
_start:
{
uint8_t v_collapsed_boxed_1750_; uint8_t v_clsEnabled_boxed_1751_; lean_object* v_res_1752_; 
v_collapsed_boxed_1750_ = lean_unbox(v_collapsed_1740_);
v_clsEnabled_boxed_1751_ = lean_unbox(v_clsEnabled_1743_);
v_res_1752_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0(v_cls_1739_, v_collapsed_boxed_1750_, v_tag_1741_, v_opts_1742_, v_clsEnabled_boxed_1751_, v_oldTraces_1744_, v_msg_1745_, v_resStartStop_1746_, v___y_1747_, v___y_1748_);
lean_dec(v___y_1748_);
lean_dec_ref(v___y_1747_);
lean_dec_ref(v_opts_1742_);
return v_res_1752_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1_spec__2(lean_object* v_e_1753_){
_start:
{
if (lean_obj_tag(v_e_1753_) == 0)
{
uint8_t v___x_1754_; 
v___x_1754_ = 2;
return v___x_1754_;
}
else
{
uint8_t v___x_1755_; 
v___x_1755_ = 0;
return v___x_1755_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1_spec__2___boxed(lean_object* v_e_1756_){
_start:
{
uint8_t v_res_1757_; lean_object* v_r_1758_; 
v_res_1757_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1_spec__2(v_e_1756_);
lean_dec_ref(v_e_1756_);
v_r_1758_ = lean_box(v_res_1757_);
return v_r_1758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1(lean_object* v_cls_1759_, uint8_t v_collapsed_1760_, lean_object* v_tag_1761_, lean_object* v_opts_1762_, uint8_t v_clsEnabled_1763_, lean_object* v_oldTraces_1764_, lean_object* v_msg_1765_, lean_object* v_resStartStop_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_){
_start:
{
lean_object* v_fst_1770_; lean_object* v_snd_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1869_; 
v_fst_1770_ = lean_ctor_get(v_resStartStop_1766_, 0);
v_snd_1771_ = lean_ctor_get(v_resStartStop_1766_, 1);
v_isSharedCheck_1869_ = !lean_is_exclusive(v_resStartStop_1766_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1773_ = v_resStartStop_1766_;
v_isShared_1774_ = v_isSharedCheck_1869_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_snd_1771_);
lean_inc(v_fst_1770_);
lean_dec(v_resStartStop_1766_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1869_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___y_1776_; lean_object* v___y_1777_; lean_object* v_data_1778_; lean_object* v_fst_1789_; lean_object* v_snd_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1868_; 
v_fst_1789_ = lean_ctor_get(v_snd_1771_, 0);
v_snd_1790_ = lean_ctor_get(v_snd_1771_, 1);
v_isSharedCheck_1868_ = !lean_is_exclusive(v_snd_1771_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1792_ = v_snd_1771_;
v_isShared_1793_ = v_isSharedCheck_1868_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_snd_1790_);
lean_inc(v_fst_1789_);
lean_dec(v_snd_1771_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1868_;
goto v_resetjp_1791_;
}
v___jp_1775_:
{
lean_object* v___x_1779_; 
lean_inc(v___y_1776_);
v___x_1779_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5(v_oldTraces_1764_, v_data_1778_, v___y_1776_, v___y_1777_, v___y_1767_, v___y_1768_);
if (lean_obj_tag(v___x_1779_) == 0)
{
lean_object* v___x_1780_; 
lean_dec_ref_known(v___x_1779_, 1);
v___x_1780_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__6___redArg(v_fst_1770_);
return v___x_1780_;
}
else
{
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1788_; 
lean_dec(v_fst_1770_);
v_a_1781_ = lean_ctor_get(v___x_1779_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1783_ = v___x_1779_;
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v___x_1779_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1786_; 
if (v_isShared_1784_ == 0)
{
v___x_1786_ = v___x_1783_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_a_1781_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
}
v_resetjp_1791_:
{
lean_object* v___x_1794_; uint8_t v___x_1795_; lean_object* v___y_1797_; lean_object* v_a_1798_; uint8_t v___y_1822_; double v___y_1853_; 
v___x_1794_ = l_Lean_trace_profiler;
v___x_1795_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_opts_1762_, v___x_1794_);
if (v___x_1795_ == 0)
{
v___y_1822_ = v___x_1795_;
goto v___jp_1821_;
}
else
{
lean_object* v___x_1858_; uint8_t v___x_1859_; 
v___x_1858_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1859_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_opts_1762_, v___x_1858_);
if (v___x_1859_ == 0)
{
lean_object* v___x_1860_; lean_object* v___x_1861_; double v___x_1862_; double v___x_1863_; double v___x_1864_; 
v___x_1860_ = l_Lean_trace_profiler_threshold;
v___x_1861_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(v_opts_1762_, v___x_1860_);
v___x_1862_ = lean_float_of_nat(v___x_1861_);
v___x_1863_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__5);
v___x_1864_ = lean_float_div(v___x_1862_, v___x_1863_);
v___y_1853_ = v___x_1864_;
goto v___jp_1852_;
}
else
{
lean_object* v___x_1865_; lean_object* v___x_1866_; double v___x_1867_; 
v___x_1865_ = l_Lean_trace_profiler_threshold;
v___x_1866_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(v_opts_1762_, v___x_1865_);
v___x_1867_ = lean_float_of_nat(v___x_1866_);
v___y_1853_ = v___x_1867_;
goto v___jp_1852_;
}
}
v___jp_1796_:
{
uint8_t v_result_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1804_; 
v_result_1799_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1_spec__2(v_fst_1770_);
v___x_1800_ = l_Lean_TraceResult_toEmoji(v_result_1799_);
v___x_1801_ = l_Lean_stringToMessageData(v___x_1800_);
v___x_1802_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__1);
if (v_isShared_1793_ == 0)
{
lean_ctor_set_tag(v___x_1792_, 7);
lean_ctor_set(v___x_1792_, 1, v___x_1802_);
lean_ctor_set(v___x_1792_, 0, v___x_1801_);
v___x_1804_ = v___x_1792_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v___x_1801_);
lean_ctor_set(v_reuseFailAlloc_1815_, 1, v___x_1802_);
v___x_1804_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
lean_object* v_m_1806_; 
if (v_isShared_1774_ == 0)
{
lean_ctor_set_tag(v___x_1773_, 7);
lean_ctor_set(v___x_1773_, 1, v_a_1798_);
lean_ctor_set(v___x_1773_, 0, v___x_1804_);
v_m_1806_ = v___x_1773_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v___x_1804_);
lean_ctor_set(v_reuseFailAlloc_1814_, 1, v_a_1798_);
v_m_1806_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
lean_object* v___x_1807_; lean_object* v___x_1808_; double v___x_1809_; lean_object* v_data_1810_; 
v___x_1807_ = lean_box(v_result_1799_);
v___x_1808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1807_);
v___x_1809_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2);
lean_inc_ref(v_tag_1761_);
lean_inc_ref(v___x_1808_);
lean_inc(v_cls_1759_);
v_data_1810_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1810_, 0, v_cls_1759_);
lean_ctor_set(v_data_1810_, 1, v___x_1808_);
lean_ctor_set(v_data_1810_, 2, v_tag_1761_);
lean_ctor_set_float(v_data_1810_, sizeof(void*)*3, v___x_1809_);
lean_ctor_set_float(v_data_1810_, sizeof(void*)*3 + 8, v___x_1809_);
lean_ctor_set_uint8(v_data_1810_, sizeof(void*)*3 + 16, v_collapsed_1760_);
if (v___x_1795_ == 0)
{
lean_dec_ref_known(v___x_1808_, 1);
lean_dec(v_snd_1790_);
lean_dec(v_fst_1789_);
lean_dec_ref(v_tag_1761_);
lean_dec(v_cls_1759_);
v___y_1776_ = v___y_1797_;
v___y_1777_ = v_m_1806_;
v_data_1778_ = v_data_1810_;
goto v___jp_1775_;
}
else
{
lean_object* v_data_1811_; double v___x_1812_; double v___x_1813_; 
lean_dec_ref_known(v_data_1810_, 3);
v_data_1811_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1811_, 0, v_cls_1759_);
lean_ctor_set(v_data_1811_, 1, v___x_1808_);
lean_ctor_set(v_data_1811_, 2, v_tag_1761_);
v___x_1812_ = lean_unbox_float(v_fst_1789_);
lean_dec(v_fst_1789_);
lean_ctor_set_float(v_data_1811_, sizeof(void*)*3, v___x_1812_);
v___x_1813_ = lean_unbox_float(v_snd_1790_);
lean_dec(v_snd_1790_);
lean_ctor_set_float(v_data_1811_, sizeof(void*)*3 + 8, v___x_1813_);
lean_ctor_set_uint8(v_data_1811_, sizeof(void*)*3 + 16, v_collapsed_1760_);
v___y_1776_ = v___y_1797_;
v___y_1777_ = v_m_1806_;
v_data_1778_ = v_data_1811_;
goto v___jp_1775_;
}
}
}
}
v___jp_1816_:
{
lean_object* v_ref_1817_; lean_object* v___x_1818_; 
v_ref_1817_ = lean_ctor_get(v___y_1767_, 5);
lean_inc(v___y_1768_);
lean_inc_ref(v___y_1767_);
lean_inc(v_fst_1770_);
v___x_1818_ = lean_apply_4(v_msg_1765_, v_fst_1770_, v___y_1767_, v___y_1768_, lean_box(0));
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_object* v_a_1819_; 
v_a_1819_ = lean_ctor_get(v___x_1818_, 0);
lean_inc(v_a_1819_);
lean_dec_ref_known(v___x_1818_, 1);
v___y_1797_ = v_ref_1817_;
v_a_1798_ = v_a_1819_;
goto v___jp_1796_;
}
else
{
lean_object* v___x_1820_; 
lean_dec_ref_known(v___x_1818_, 1);
v___x_1820_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__4);
v___y_1797_ = v_ref_1817_;
v_a_1798_ = v___x_1820_;
goto v___jp_1796_;
}
}
v___jp_1821_:
{
if (v_clsEnabled_1763_ == 0)
{
if (v___y_1822_ == 0)
{
lean_object* v___x_1823_; lean_object* v_traceState_1824_; lean_object* v_env_1825_; lean_object* v_nextMacroScope_1826_; lean_object* v_ngen_1827_; lean_object* v_auxDeclNGen_1828_; lean_object* v_cache_1829_; lean_object* v_messages_1830_; lean_object* v_infoState_1831_; lean_object* v_snapshotTasks_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1851_; 
lean_del_object(v___x_1792_);
lean_dec(v_snd_1790_);
lean_dec(v_fst_1789_);
lean_del_object(v___x_1773_);
lean_dec_ref(v_msg_1765_);
lean_dec_ref(v_tag_1761_);
lean_dec(v_cls_1759_);
v___x_1823_ = lean_st_ref_take(v___y_1768_);
v_traceState_1824_ = lean_ctor_get(v___x_1823_, 4);
v_env_1825_ = lean_ctor_get(v___x_1823_, 0);
v_nextMacroScope_1826_ = lean_ctor_get(v___x_1823_, 1);
v_ngen_1827_ = lean_ctor_get(v___x_1823_, 2);
v_auxDeclNGen_1828_ = lean_ctor_get(v___x_1823_, 3);
v_cache_1829_ = lean_ctor_get(v___x_1823_, 5);
v_messages_1830_ = lean_ctor_get(v___x_1823_, 6);
v_infoState_1831_ = lean_ctor_get(v___x_1823_, 7);
v_snapshotTasks_1832_ = lean_ctor_get(v___x_1823_, 8);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1823_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1834_ = v___x_1823_;
v_isShared_1835_ = v_isSharedCheck_1851_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_snapshotTasks_1832_);
lean_inc(v_infoState_1831_);
lean_inc(v_messages_1830_);
lean_inc(v_cache_1829_);
lean_inc(v_traceState_1824_);
lean_inc(v_auxDeclNGen_1828_);
lean_inc(v_ngen_1827_);
lean_inc(v_nextMacroScope_1826_);
lean_inc(v_env_1825_);
lean_dec(v___x_1823_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1851_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
uint64_t v_tid_1836_; lean_object* v_traces_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1850_; 
v_tid_1836_ = lean_ctor_get_uint64(v_traceState_1824_, sizeof(void*)*1);
v_traces_1837_ = lean_ctor_get(v_traceState_1824_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v_traceState_1824_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1839_ = v_traceState_1824_;
v_isShared_1840_ = v_isSharedCheck_1850_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_traces_1837_);
lean_dec(v_traceState_1824_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1850_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v___x_1841_; lean_object* v___x_1843_; 
v___x_1841_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1764_, v_traces_1837_);
lean_dec_ref(v_traces_1837_);
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 0, v___x_1841_);
v___x_1843_ = v___x_1839_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v___x_1841_);
lean_ctor_set_uint64(v_reuseFailAlloc_1849_, sizeof(void*)*1, v_tid_1836_);
v___x_1843_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
lean_object* v___x_1845_; 
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 4, v___x_1843_);
v___x_1845_ = v___x_1834_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_env_1825_);
lean_ctor_set(v_reuseFailAlloc_1848_, 1, v_nextMacroScope_1826_);
lean_ctor_set(v_reuseFailAlloc_1848_, 2, v_ngen_1827_);
lean_ctor_set(v_reuseFailAlloc_1848_, 3, v_auxDeclNGen_1828_);
lean_ctor_set(v_reuseFailAlloc_1848_, 4, v___x_1843_);
lean_ctor_set(v_reuseFailAlloc_1848_, 5, v_cache_1829_);
lean_ctor_set(v_reuseFailAlloc_1848_, 6, v_messages_1830_);
lean_ctor_set(v_reuseFailAlloc_1848_, 7, v_infoState_1831_);
lean_ctor_set(v_reuseFailAlloc_1848_, 8, v_snapshotTasks_1832_);
v___x_1845_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1846_ = lean_st_ref_set(v___y_1768_, v___x_1845_);
v___x_1847_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__6___redArg(v_fst_1770_);
return v___x_1847_;
}
}
}
}
}
else
{
goto v___jp_1816_;
}
}
else
{
goto v___jp_1816_;
}
}
v___jp_1852_:
{
double v___x_1854_; double v___x_1855_; double v___x_1856_; uint8_t v___x_1857_; 
v___x_1854_ = lean_unbox_float(v_snd_1790_);
v___x_1855_ = lean_unbox_float(v_fst_1789_);
v___x_1856_ = lean_float_sub(v___x_1854_, v___x_1855_);
v___x_1857_ = lean_float_decLt(v___y_1853_, v___x_1856_);
v___y_1822_ = v___x_1857_;
goto v___jp_1821_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1___boxed(lean_object* v_cls_1870_, lean_object* v_collapsed_1871_, lean_object* v_tag_1872_, lean_object* v_opts_1873_, lean_object* v_clsEnabled_1874_, lean_object* v_oldTraces_1875_, lean_object* v_msg_1876_, lean_object* v_resStartStop_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_){
_start:
{
uint8_t v_collapsed_boxed_1881_; uint8_t v_clsEnabled_boxed_1882_; lean_object* v_res_1883_; 
v_collapsed_boxed_1881_ = lean_unbox(v_collapsed_1871_);
v_clsEnabled_boxed_1882_ = lean_unbox(v_clsEnabled_1874_);
v_res_1883_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1(v_cls_1870_, v_collapsed_boxed_1881_, v_tag_1872_, v_opts_1873_, v_clsEnabled_boxed_1882_, v_oldTraces_1875_, v_msg_1876_, v_resStartStop_1877_, v___y_1878_, v___y_1879_);
lean_dec(v___y_1879_);
lean_dec_ref(v___y_1878_);
lean_dec_ref(v_opts_1873_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__4(lean_object* v___f_1884_, lean_object* v_lratPath_1885_, uint8_t v_trimProofs_1886_, lean_object* v___f_1887_, lean_object* v_solver_1888_, lean_object* v_timeout_1889_, uint8_t v_binaryProofs_1890_, uint8_t v_solverMode_1891_, lean_object* v___f_1892_, lean_object* v___f_1893_, lean_object* v_cnfHandle_1894_, lean_object* v_cnfPath_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_){
_start:
{
lean_object* v___y_1900_; lean_object* v_options_1918_; lean_object* v_ref_1919_; lean_object* v_inheritedTraceOptions_1920_; uint8_t v_hasTrace_1921_; lean_object* v___x_1922_; uint8_t v___x_1923_; lean_object* v___x_1924_; uint8_t v___y_1926_; lean_object* v___y_1927_; lean_object* v___y_1928_; lean_object* v___y_1929_; lean_object* v_a_1930_; lean_object* v___y_1943_; uint8_t v___y_1944_; lean_object* v___y_1945_; lean_object* v___y_1946_; lean_object* v_a_1947_; uint8_t v___y_1957_; lean_object* v___y_1958_; lean_object* v___y_2000_; lean_object* v___y_2032_; lean_object* v___y_2033_; uint8_t v___y_2034_; lean_object* v___y_2035_; lean_object* v_a_2036_; lean_object* v___y_2049_; lean_object* v___y_2050_; uint8_t v___y_2051_; lean_object* v___y_2052_; lean_object* v_a_2053_; lean_object* v___y_2063_; uint8_t v___y_2064_; lean_object* v___y_2113_; 
v_options_1918_ = lean_ctor_get(v___y_1896_, 2);
v_ref_1919_ = lean_ctor_get(v___y_1896_, 5);
v_inheritedTraceOptions_1920_ = lean_ctor_get(v___y_1896_, 13);
v_hasTrace_1921_ = lean_ctor_get_uint8(v_options_1918_, sizeof(void*)*1);
v___x_1922_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__3));
v___x_1923_ = 1;
v___x_1924_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0___closed__0));
if (v_hasTrace_1921_ == 0)
{
lean_object* v___x_2122_; 
lean_dec_ref(v___f_1893_);
v___x_2122_ = l_IO_lazyPure___redArg(v___f_1892_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v_a_2123_; lean_object* v___x_2124_; 
v_a_2123_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_a_2123_);
lean_dec_ref_known(v___x_2122_, 1);
v___x_2124_ = lean_io_prim_handle_put_str(v_cnfHandle_1894_, v_a_2123_);
lean_dec(v_a_2123_);
if (lean_obj_tag(v___x_2124_) == 0)
{
lean_object* v___x_2125_; 
lean_dec_ref_known(v___x_2124_, 1);
v___x_2125_ = lean_io_prim_handle_flush(v_cnfHandle_1894_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_dec_ref_known(v___x_2125_, 1);
goto v___jp_2105_;
}
else
{
lean_object* v_a_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2137_; 
lean_dec_ref(v_cnfPath_1895_);
lean_dec_ref(v_solver_1888_);
lean_dec_ref(v___f_1887_);
lean_dec_ref(v_lratPath_1885_);
lean_dec_ref(v___f_1884_);
v_a_2126_ = lean_ctor_get(v___x_2125_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2128_ = v___x_2125_;
v_isShared_2129_ = v_isSharedCheck_2137_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_a_2126_);
lean_dec(v___x_2125_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2137_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2135_; 
v___x_2130_ = lean_io_error_to_string(v_a_2126_);
v___x_2131_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2131_, 0, v___x_2130_);
v___x_2132_ = l_Lean_MessageData_ofFormat(v___x_2131_);
lean_inc(v_ref_1919_);
v___x_2133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2133_, 0, v_ref_1919_);
lean_ctor_set(v___x_2133_, 1, v___x_2132_);
if (v_isShared_2129_ == 0)
{
lean_ctor_set(v___x_2128_, 0, v___x_2133_);
v___x_2135_ = v___x_2128_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v___x_2133_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
}
}
}
}
else
{
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2149_; 
lean_dec_ref(v_cnfPath_1895_);
lean_dec_ref(v_solver_1888_);
lean_dec_ref(v___f_1887_);
lean_dec_ref(v_lratPath_1885_);
lean_dec_ref(v___f_1884_);
v_a_2138_ = lean_ctor_get(v___x_2124_, 0);
v_isSharedCheck_2149_ = !lean_is_exclusive(v___x_2124_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2140_ = v___x_2124_;
v_isShared_2141_ = v_isSharedCheck_2149_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_2124_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2149_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2147_; 
v___x_2142_ = lean_io_error_to_string(v_a_2138_);
v___x_2143_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2142_);
v___x_2144_ = l_Lean_MessageData_ofFormat(v___x_2143_);
lean_inc(v_ref_1919_);
v___x_2145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2145_, 0, v_ref_1919_);
lean_ctor_set(v___x_2145_, 1, v___x_2144_);
if (v_isShared_2141_ == 0)
{
lean_ctor_set(v___x_2140_, 0, v___x_2145_);
v___x_2147_ = v___x_2140_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v___x_2145_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
}
}
else
{
lean_object* v_a_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2161_; 
lean_dec_ref(v_cnfPath_1895_);
lean_dec_ref(v_solver_1888_);
lean_dec_ref(v___f_1887_);
lean_dec_ref(v_lratPath_1885_);
lean_dec_ref(v___f_1884_);
v_a_2150_ = lean_ctor_get(v___x_2122_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2152_ = v___x_2122_;
v_isShared_2153_ = v_isSharedCheck_2161_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_a_2150_);
lean_dec(v___x_2122_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2161_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2159_; 
v___x_2154_ = lean_io_error_to_string(v_a_2150_);
v___x_2155_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2154_);
v___x_2156_ = l_Lean_MessageData_ofFormat(v___x_2155_);
lean_inc(v_ref_1919_);
v___x_2157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2157_, 0, v_ref_1919_);
lean_ctor_set(v___x_2157_, 1, v___x_2156_);
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 0, v___x_2157_);
v___x_2159_ = v___x_2152_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v___x_2157_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
}
else
{
lean_object* v___x_2162_; uint8_t v___x_2163_; lean_object* v___y_2165_; lean_object* v___y_2166_; lean_object* v_a_2167_; lean_object* v___y_2180_; lean_object* v___y_2181_; lean_object* v_a_2182_; lean_object* v___y_2185_; lean_object* v___y_2186_; lean_object* v_a_2187_; lean_object* v___y_2197_; lean_object* v___y_2198_; lean_object* v_a_2199_; 
v___x_2162_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6);
v___x_2163_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1920_, v_options_1918_, v___x_2162_);
if (v___x_2163_ == 0)
{
lean_object* v___x_2298_; uint8_t v___x_2299_; 
v___x_2298_ = l_Lean_trace_profiler;
v___x_2299_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_options_1918_, v___x_2298_);
if (v___x_2299_ == 0)
{
lean_object* v___x_2300_; 
lean_dec_ref(v___f_1893_);
v___x_2300_ = l_IO_lazyPure___redArg(v___f_1892_);
if (lean_obj_tag(v___x_2300_) == 0)
{
lean_object* v_a_2301_; lean_object* v___x_2302_; 
v_a_2301_ = lean_ctor_get(v___x_2300_, 0);
lean_inc(v_a_2301_);
lean_dec_ref_known(v___x_2300_, 1);
v___x_2302_ = lean_io_prim_handle_put_str(v_cnfHandle_1894_, v_a_2301_);
lean_dec(v_a_2301_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v___x_2303_; 
lean_dec_ref_known(v___x_2302_, 1);
v___x_2303_ = lean_io_prim_handle_flush(v_cnfHandle_1894_);
if (lean_obj_tag(v___x_2303_) == 0)
{
lean_dec_ref_known(v___x_2303_, 1);
goto v___jp_2105_;
}
else
{
lean_object* v_a_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2315_; 
lean_dec_ref(v_cnfPath_1895_);
lean_dec_ref(v_solver_1888_);
lean_dec_ref(v___f_1887_);
lean_dec_ref(v_lratPath_1885_);
lean_dec_ref(v___f_1884_);
v_a_2304_ = lean_ctor_get(v___x_2303_, 0);
v_isSharedCheck_2315_ = !lean_is_exclusive(v___x_2303_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2306_ = v___x_2303_;
v_isShared_2307_ = v_isSharedCheck_2315_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_a_2304_);
lean_dec(v___x_2303_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2315_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2313_; 
v___x_2308_ = lean_io_error_to_string(v_a_2304_);
v___x_2309_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2309_, 0, v___x_2308_);
v___x_2310_ = l_Lean_MessageData_ofFormat(v___x_2309_);
lean_inc(v_ref_1919_);
v___x_2311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2311_, 0, v_ref_1919_);
lean_ctor_set(v___x_2311_, 1, v___x_2310_);
if (v_isShared_2307_ == 0)
{
lean_ctor_set(v___x_2306_, 0, v___x_2311_);
v___x_2313_ = v___x_2306_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v___x_2311_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
}
}
else
{
lean_object* v_a_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2327_; 
lean_dec_ref(v_cnfPath_1895_);
lean_dec_ref(v_solver_1888_);
lean_dec_ref(v___f_1887_);
lean_dec_ref(v_lratPath_1885_);
lean_dec_ref(v___f_1884_);
v_a_2316_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2327_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2327_ == 0)
{
v___x_2318_ = v___x_2302_;
v_isShared_2319_ = v_isSharedCheck_2327_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_a_2316_);
lean_dec(v___x_2302_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2327_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2325_; 
v___x_2320_ = lean_io_error_to_string(v_a_2316_);
v___x_2321_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2320_);
v___x_2322_ = l_Lean_MessageData_ofFormat(v___x_2321_);
lean_inc(v_ref_1919_);
v___x_2323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2323_, 0, v_ref_1919_);
lean_ctor_set(v___x_2323_, 1, v___x_2322_);
if (v_isShared_2319_ == 0)
{
lean_ctor_set(v___x_2318_, 0, v___x_2323_);
v___x_2325_ = v___x_2318_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v___x_2323_);
v___x_2325_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
return v___x_2325_;
}
}
}
}
else
{
lean_object* v_a_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2339_; 
lean_dec_ref(v_cnfPath_1895_);
lean_dec_ref(v_solver_1888_);
lean_dec_ref(v___f_1887_);
lean_dec_ref(v_lratPath_1885_);
lean_dec_ref(v___f_1884_);
v_a_2328_ = lean_ctor_get(v___x_2300_, 0);
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2300_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2330_ = v___x_2300_;
v_isShared_2331_ = v_isSharedCheck_2339_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_a_2328_);
lean_dec(v___x_2300_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2339_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2337_; 
v___x_2332_ = lean_io_error_to_string(v_a_2328_);
v___x_2333_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2333_, 0, v___x_2332_);
v___x_2334_ = l_Lean_MessageData_ofFormat(v___x_2333_);
lean_inc(v_ref_1919_);
v___x_2335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2335_, 0, v_ref_1919_);
lean_ctor_set(v___x_2335_, 1, v___x_2334_);
if (v_isShared_2331_ == 0)
{
lean_ctor_set(v___x_2330_, 0, v___x_2335_);
v___x_2337_ = v___x_2330_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v___x_2335_);
v___x_2337_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
return v___x_2337_;
}
}
}
}
else
{
goto v___jp_2201_;
}
}
else
{
goto v___jp_2201_;
}
v___jp_2164_:
{
lean_object* v___x_2168_; double v___x_2169_; double v___x_2170_; double v___x_2171_; double v___x_2172_; double v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2168_ = lean_io_mono_nanos_now();
v___x_2169_ = lean_float_of_nat(v___y_2166_);
v___x_2170_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9);
v___x_2171_ = lean_float_div(v___x_2169_, v___x_2170_);
v___x_2172_ = lean_float_of_nat(v___x_2168_);
v___x_2173_ = lean_float_div(v___x_2172_, v___x_2170_);
v___x_2174_ = lean_box_float(v___x_2171_);
v___x_2175_ = lean_box_float(v___x_2173_);
v___x_2176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2176_, 0, v___x_2174_);
lean_ctor_set(v___x_2176_, 1, v___x_2175_);
v___x_2177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2177_, 0, v_a_2167_);
lean_ctor_set(v___x_2177_, 1, v___x_2176_);
v___x_2178_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2(v___x_1922_, v___x_1923_, v___x_1924_, v_options_1918_, v___x_2163_, v___y_2165_, v___f_1893_, v___x_2177_, v___y_1896_, v___y_1897_);
v___y_2113_ = v___x_2178_;
goto v___jp_2112_;
}
v___jp_2179_:
{
lean_object* v___x_2183_; 
v___x_2183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2183_, 0, v_a_2182_);
v___y_2165_ = v___y_2180_;
v___y_2166_ = v___y_2181_;
v_a_2167_ = v___x_2183_;
goto v___jp_2164_;
}
v___jp_2184_:
{
lean_object* v___x_2188_; double v___x_2189_; double v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; 
v___x_2188_ = lean_io_get_num_heartbeats();
v___x_2189_ = lean_float_of_nat(v___y_2185_);
v___x_2190_ = lean_float_of_nat(v___x_2188_);
v___x_2191_ = lean_box_float(v___x_2189_);
v___x_2192_ = lean_box_float(v___x_2190_);
v___x_2193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2193_, 0, v___x_2191_);
lean_ctor_set(v___x_2193_, 1, v___x_2192_);
v___x_2194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2194_, 0, v_a_2187_);
lean_ctor_set(v___x_2194_, 1, v___x_2193_);
v___x_2195_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2(v___x_1922_, v___x_1923_, v___x_1924_, v_options_1918_, v___x_2163_, v___y_2186_, v___f_1893_, v___x_2194_, v___y_1896_, v___y_1897_);
v___y_2113_ = v___x_2195_;
goto v___jp_2112_;
}
v___jp_2196_:
{
lean_object* v___x_2200_; 
v___x_2200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2200_, 0, v_a_2199_);
v___y_2185_ = v___y_2197_;
v___y_2186_ = v___y_2198_;
v_a_2187_ = v___x_2200_;
goto v___jp_2184_;
}
v___jp_2201_:
{
lean_object* v___x_2202_; lean_object* v_a_2203_; lean_object* v___x_2204_; uint8_t v___x_2205_; 
v___x_2202_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg(v___y_1897_);
v_a_2203_ = lean_ctor_get(v___x_2202_, 0);
lean_inc(v_a_2203_);
lean_dec_ref(v___x_2202_);
v___x_2204_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2205_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_options_1918_, v___x_2204_);
if (v___x_2205_ == 0)
{
lean_object* v___x_2206_; lean_object* v___x_2207_; 
v___x_2206_ = lean_io_mono_nanos_now();
v___x_2207_ = l_IO_lazyPure___redArg(v___f_1892_);
if (lean_obj_tag(v___x_2207_) == 0)
{
lean_object* v_a_2208_; lean_object* v___x_2209_; 
v_a_2208_ = lean_ctor_get(v___x_2207_, 0);
lean_inc(v_a_2208_);
lean_dec_ref_known(v___x_2207_, 1);
v___x_2209_ = lean_io_prim_handle_put_str(v_cnfHandle_1894_, v_a_2208_);
lean_dec(v_a_2208_);
if (lean_obj_tag(v___x_2209_) == 0)
{
lean_object* v___x_2210_; 
lean_dec_ref_known(v___x_2209_, 1);
v___x_2210_ = lean_io_prim_handle_flush(v_cnfHandle_1894_);
if (lean_obj_tag(v___x_2210_) == 0)
{
lean_object* v_a_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2218_; 
v_a_2211_ = lean_ctor_get(v___x_2210_, 0);
v_isSharedCheck_2218_ = !lean_is_exclusive(v___x_2210_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_2213_ = v___x_2210_;
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_a_2211_);
lean_dec(v___x_2210_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v___x_2216_; 
if (v_isShared_2214_ == 0)
{
lean_ctor_set_tag(v___x_2213_, 1);
v___x_2216_ = v___x_2213_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v_a_2211_);
v___x_2216_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
v___y_2165_ = v_a_2203_;
v___y_2166_ = v___x_2206_;
v_a_2167_ = v___x_2216_;
goto v___jp_2164_;
}
}
}
else
{
lean_object* v_a_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2229_; 
v_a_2219_ = lean_ctor_get(v___x_2210_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2210_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2221_ = v___x_2210_;
v_isShared_2222_ = v_isSharedCheck_2229_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_a_2219_);
lean_dec(v___x_2210_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2229_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
lean_object* v___x_2223_; lean_object* v___x_2225_; 
v___x_2223_ = lean_io_error_to_string(v_a_2219_);
if (v_isShared_2222_ == 0)
{
lean_ctor_set_tag(v___x_2221_, 3);
lean_ctor_set(v___x_2221_, 0, v___x_2223_);
v___x_2225_ = v___x_2221_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v___x_2223_);
v___x_2225_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; 
v___x_2226_ = l_Lean_MessageData_ofFormat(v___x_2225_);
lean_inc(v_ref_1919_);
v___x_2227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2227_, 0, v_ref_1919_);
lean_ctor_set(v___x_2227_, 1, v___x_2226_);
v___y_2180_ = v_a_2203_;
v___y_2181_ = v___x_2206_;
v_a_2182_ = v___x_2227_;
goto v___jp_2179_;
}
}
}
}
else
{
lean_object* v_a_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2240_; 
v_a_2230_ = lean_ctor_get(v___x_2209_, 0);
v_isSharedCheck_2240_ = !lean_is_exclusive(v___x_2209_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2232_ = v___x_2209_;
v_isShared_2233_ = v_isSharedCheck_2240_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v___x_2209_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2240_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___x_2234_; lean_object* v___x_2236_; 
v___x_2234_ = lean_io_error_to_string(v_a_2230_);
if (v_isShared_2233_ == 0)
{
lean_ctor_set_tag(v___x_2232_, 3);
lean_ctor_set(v___x_2232_, 0, v___x_2234_);
v___x_2236_ = v___x_2232_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v___x_2234_);
v___x_2236_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___x_2237_ = l_Lean_MessageData_ofFormat(v___x_2236_);
lean_inc(v_ref_1919_);
v___x_2238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2238_, 0, v_ref_1919_);
lean_ctor_set(v___x_2238_, 1, v___x_2237_);
v___y_2180_ = v_a_2203_;
v___y_2181_ = v___x_2206_;
v_a_2182_ = v___x_2238_;
goto v___jp_2179_;
}
}
}
}
else
{
lean_object* v_a_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2251_; 
v_a_2241_ = lean_ctor_get(v___x_2207_, 0);
v_isSharedCheck_2251_ = !lean_is_exclusive(v___x_2207_);
if (v_isSharedCheck_2251_ == 0)
{
v___x_2243_ = v___x_2207_;
v_isShared_2244_ = v_isSharedCheck_2251_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_a_2241_);
lean_dec(v___x_2207_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2251_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2245_; lean_object* v___x_2247_; 
v___x_2245_ = lean_io_error_to_string(v_a_2241_);
if (v_isShared_2244_ == 0)
{
lean_ctor_set_tag(v___x_2243_, 3);
lean_ctor_set(v___x_2243_, 0, v___x_2245_);
v___x_2247_ = v___x_2243_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v___x_2245_);
v___x_2247_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2248_ = l_Lean_MessageData_ofFormat(v___x_2247_);
lean_inc(v_ref_1919_);
v___x_2249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2249_, 0, v_ref_1919_);
lean_ctor_set(v___x_2249_, 1, v___x_2248_);
v___y_2180_ = v_a_2203_;
v___y_2181_ = v___x_2206_;
v_a_2182_ = v___x_2249_;
goto v___jp_2179_;
}
}
}
}
else
{
lean_object* v___x_2252_; lean_object* v___x_2253_; 
v___x_2252_ = lean_io_get_num_heartbeats();
v___x_2253_ = l_IO_lazyPure___redArg(v___f_1892_);
if (lean_obj_tag(v___x_2253_) == 0)
{
lean_object* v_a_2254_; lean_object* v___x_2255_; 
v_a_2254_ = lean_ctor_get(v___x_2253_, 0);
lean_inc(v_a_2254_);
lean_dec_ref_known(v___x_2253_, 1);
v___x_2255_ = lean_io_prim_handle_put_str(v_cnfHandle_1894_, v_a_2254_);
lean_dec(v_a_2254_);
if (lean_obj_tag(v___x_2255_) == 0)
{
lean_object* v___x_2256_; 
lean_dec_ref_known(v___x_2255_, 1);
v___x_2256_ = lean_io_prim_handle_flush(v_cnfHandle_1894_);
if (lean_obj_tag(v___x_2256_) == 0)
{
lean_object* v_a_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2264_; 
v_a_2257_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2264_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2259_ = v___x_2256_;
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_a_2257_);
lean_dec(v___x_2256_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v___x_2262_; 
if (v_isShared_2260_ == 0)
{
lean_ctor_set_tag(v___x_2259_, 1);
v___x_2262_ = v___x_2259_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v_a_2257_);
v___x_2262_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
v___y_2185_ = v___x_2252_;
v___y_2186_ = v_a_2203_;
v_a_2187_ = v___x_2262_;
goto v___jp_2184_;
}
}
}
else
{
lean_object* v_a_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2275_; 
v_a_2265_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2275_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2267_ = v___x_2256_;
v_isShared_2268_ = v_isSharedCheck_2275_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_a_2265_);
lean_dec(v___x_2256_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2275_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v___x_2269_; lean_object* v___x_2271_; 
v___x_2269_ = lean_io_error_to_string(v_a_2265_);
if (v_isShared_2268_ == 0)
{
lean_ctor_set_tag(v___x_2267_, 3);
lean_ctor_set(v___x_2267_, 0, v___x_2269_);
v___x_2271_ = v___x_2267_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v___x_2269_);
v___x_2271_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___x_2272_ = l_Lean_MessageData_ofFormat(v___x_2271_);
lean_inc(v_ref_1919_);
v___x_2273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2273_, 0, v_ref_1919_);
lean_ctor_set(v___x_2273_, 1, v___x_2272_);
v___y_2197_ = v___x_2252_;
v___y_2198_ = v_a_2203_;
v_a_2199_ = v___x_2273_;
goto v___jp_2196_;
}
}
}
}
else
{
lean_object* v_a_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2286_; 
v_a_2276_ = lean_ctor_get(v___x_2255_, 0);
v_isSharedCheck_2286_ = !lean_is_exclusive(v___x_2255_);
if (v_isSharedCheck_2286_ == 0)
{
v___x_2278_ = v___x_2255_;
v_isShared_2279_ = v_isSharedCheck_2286_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_a_2276_);
lean_dec(v___x_2255_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2286_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v___x_2280_; lean_object* v___x_2282_; 
v___x_2280_ = lean_io_error_to_string(v_a_2276_);
if (v_isShared_2279_ == 0)
{
lean_ctor_set_tag(v___x_2278_, 3);
lean_ctor_set(v___x_2278_, 0, v___x_2280_);
v___x_2282_ = v___x_2278_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v___x_2280_);
v___x_2282_ = v_reuseFailAlloc_2285_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
lean_object* v___x_2283_; lean_object* v___x_2284_; 
v___x_2283_ = l_Lean_MessageData_ofFormat(v___x_2282_);
lean_inc(v_ref_1919_);
v___x_2284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2284_, 0, v_ref_1919_);
lean_ctor_set(v___x_2284_, 1, v___x_2283_);
v___y_2197_ = v___x_2252_;
v___y_2198_ = v_a_2203_;
v_a_2199_ = v___x_2284_;
goto v___jp_2196_;
}
}
}
}
else
{
lean_object* v_a_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2297_; 
v_a_2287_ = lean_ctor_get(v___x_2253_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2253_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2289_ = v___x_2253_;
v_isShared_2290_ = v_isSharedCheck_2297_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_a_2287_);
lean_dec(v___x_2253_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2297_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
lean_object* v___x_2291_; lean_object* v___x_2293_; 
v___x_2291_ = lean_io_error_to_string(v_a_2287_);
if (v_isShared_2290_ == 0)
{
lean_ctor_set_tag(v___x_2289_, 3);
lean_ctor_set(v___x_2289_, 0, v___x_2291_);
v___x_2293_ = v___x_2289_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v___x_2291_);
v___x_2293_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
lean_object* v___x_2294_; lean_object* v___x_2295_; 
v___x_2294_ = l_Lean_MessageData_ofFormat(v___x_2293_);
lean_inc(v_ref_1919_);
v___x_2295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2295_, 0, v_ref_1919_);
lean_ctor_set(v___x_2295_, 1, v___x_2294_);
v___y_2197_ = v___x_2252_;
v___y_2198_ = v_a_2203_;
v_a_2199_ = v___x_2295_;
goto v___jp_2196_;
}
}
}
}
}
}
v___jp_1899_:
{
if (lean_obj_tag(v___y_1900_) == 0)
{
lean_object* v_a_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1909_; 
v_a_1901_ = lean_ctor_get(v___y_1900_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___y_1900_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1903_ = v___y_1900_;
v_isShared_1904_ = v_isSharedCheck_1909_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_a_1901_);
lean_dec(v___y_1900_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1909_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1905_; lean_object* v___x_1907_; 
v___x_1905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1905_, 0, v_a_1901_);
if (v_isShared_1904_ == 0)
{
lean_ctor_set(v___x_1903_, 0, v___x_1905_);
v___x_1907_ = v___x_1903_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v___x_1905_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
return v___x_1907_;
}
}
}
else
{
lean_object* v_a_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1917_; 
v_a_1910_ = lean_ctor_get(v___y_1900_, 0);
v_isSharedCheck_1917_ = !lean_is_exclusive(v___y_1900_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1912_ = v___y_1900_;
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_a_1910_);
lean_dec(v___y_1900_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1915_; 
if (v_isShared_1913_ == 0)
{
v___x_1915_ = v___x_1912_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_a_1910_);
v___x_1915_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
return v___x_1915_;
}
}
}
}
v___jp_1925_:
{
lean_object* v___x_1931_; double v___x_1932_; double v___x_1933_; double v___x_1934_; double v___x_1935_; double v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; 
v___x_1931_ = lean_io_mono_nanos_now();
v___x_1932_ = lean_float_of_nat(v___y_1927_);
v___x_1933_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9);
v___x_1934_ = lean_float_div(v___x_1932_, v___x_1933_);
v___x_1935_ = lean_float_of_nat(v___x_1931_);
v___x_1936_ = lean_float_div(v___x_1935_, v___x_1933_);
v___x_1937_ = lean_box_float(v___x_1934_);
v___x_1938_ = lean_box_float(v___x_1936_);
v___x_1939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1939_, 0, v___x_1937_);
lean_ctor_set(v___x_1939_, 1, v___x_1938_);
v___x_1940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1940_, 0, v_a_1930_);
lean_ctor_set(v___x_1940_, 1, v___x_1939_);
v___x_1941_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0(v___x_1922_, v___x_1923_, v___x_1924_, v___y_1929_, v___y_1926_, v___y_1928_, v___f_1884_, v___x_1940_, v___y_1896_, v___y_1897_);
v___y_1900_ = v___x_1941_;
goto v___jp_1899_;
}
v___jp_1942_:
{
lean_object* v___x_1948_; double v___x_1949_; double v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; 
v___x_1948_ = lean_io_get_num_heartbeats();
v___x_1949_ = lean_float_of_nat(v___y_1943_);
v___x_1950_ = lean_float_of_nat(v___x_1948_);
v___x_1951_ = lean_box_float(v___x_1949_);
v___x_1952_ = lean_box_float(v___x_1950_);
v___x_1953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1953_, 0, v___x_1951_);
lean_ctor_set(v___x_1953_, 1, v___x_1952_);
v___x_1954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1954_, 0, v_a_1947_);
lean_ctor_set(v___x_1954_, 1, v___x_1953_);
v___x_1955_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0(v___x_1922_, v___x_1923_, v___x_1924_, v___y_1946_, v___y_1944_, v___y_1945_, v___f_1884_, v___x_1954_, v___y_1896_, v___y_1897_);
v___y_1900_ = v___x_1955_;
goto v___jp_1899_;
}
v___jp_1956_:
{
lean_object* v___x_1959_; lean_object* v_a_1960_; lean_object* v___x_1961_; uint8_t v___x_1962_; 
v___x_1959_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg(v___y_1897_);
v_a_1960_ = lean_ctor_get(v___x_1959_, 0);
lean_inc(v_a_1960_);
lean_dec_ref(v___x_1959_);
v___x_1961_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1962_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v___y_1958_, v___x_1961_);
if (v___x_1962_ == 0)
{
lean_object* v___x_1963_; lean_object* v___x_1964_; 
v___x_1963_ = lean_io_mono_nanos_now();
v___x_1964_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_1885_, v_trimProofs_1886_, v___y_1896_, v___y_1897_);
lean_dec_ref(v_lratPath_1885_);
if (lean_obj_tag(v___x_1964_) == 0)
{
lean_object* v_a_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1972_; 
v_a_1965_ = lean_ctor_get(v___x_1964_, 0);
v_isSharedCheck_1972_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1967_ = v___x_1964_;
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_a_1965_);
lean_dec(v___x_1964_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1970_; 
if (v_isShared_1968_ == 0)
{
lean_ctor_set_tag(v___x_1967_, 1);
v___x_1970_ = v___x_1967_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_a_1965_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
v___y_1926_ = v___y_1957_;
v___y_1927_ = v___x_1963_;
v___y_1928_ = v_a_1960_;
v___y_1929_ = v___y_1958_;
v_a_1930_ = v___x_1970_;
goto v___jp_1925_;
}
}
}
else
{
lean_object* v_a_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1980_; 
v_a_1973_ = lean_ctor_get(v___x_1964_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1975_ = v___x_1964_;
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_a_1973_);
lean_dec(v___x_1964_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1978_; 
if (v_isShared_1976_ == 0)
{
lean_ctor_set_tag(v___x_1975_, 0);
v___x_1978_ = v___x_1975_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_a_1973_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
v___y_1926_ = v___y_1957_;
v___y_1927_ = v___x_1963_;
v___y_1928_ = v_a_1960_;
v___y_1929_ = v___y_1958_;
v_a_1930_ = v___x_1978_;
goto v___jp_1925_;
}
}
}
}
else
{
lean_object* v___x_1981_; lean_object* v___x_1982_; 
v___x_1981_ = lean_io_get_num_heartbeats();
v___x_1982_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_1885_, v_trimProofs_1886_, v___y_1896_, v___y_1897_);
lean_dec_ref(v_lratPath_1885_);
if (lean_obj_tag(v___x_1982_) == 0)
{
lean_object* v_a_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_1990_; 
v_a_1983_ = lean_ctor_get(v___x_1982_, 0);
v_isSharedCheck_1990_ = !lean_is_exclusive(v___x_1982_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1985_ = v___x_1982_;
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_a_1983_);
lean_dec(v___x_1982_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1988_; 
if (v_isShared_1986_ == 0)
{
lean_ctor_set_tag(v___x_1985_, 1);
v___x_1988_ = v___x_1985_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_a_1983_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
v___y_1943_ = v___x_1981_;
v___y_1944_ = v___y_1957_;
v___y_1945_ = v_a_1960_;
v___y_1946_ = v___y_1958_;
v_a_1947_ = v___x_1988_;
goto v___jp_1942_;
}
}
}
else
{
lean_object* v_a_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_1998_; 
v_a_1991_ = lean_ctor_get(v___x_1982_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___x_1982_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1993_ = v___x_1982_;
v_isShared_1994_ = v_isSharedCheck_1998_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_a_1991_);
lean_dec(v___x_1982_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_1998_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v___x_1996_; 
if (v_isShared_1994_ == 0)
{
lean_ctor_set_tag(v___x_1993_, 0);
v___x_1996_ = v___x_1993_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v_a_1991_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
v___y_1943_ = v___x_1981_;
v___y_1944_ = v___y_1957_;
v___y_1945_ = v_a_1960_;
v___y_1946_ = v___y_1958_;
v_a_1947_ = v___x_1996_;
goto v___jp_1942_;
}
}
}
}
}
v___jp_1999_:
{
if (lean_obj_tag(v___y_2000_) == 0)
{
lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2022_; 
v_a_2001_ = lean_ctor_get(v___y_2000_, 0);
v_isSharedCheck_2022_ = !lean_is_exclusive(v___y_2000_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_2003_ = v___y_2000_;
v_isShared_2004_ = v_isSharedCheck_2022_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_dec(v___y_2000_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2022_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
if (lean_obj_tag(v_a_2001_) == 0)
{
lean_object* v_assignment_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2015_; 
lean_dec_ref(v_lratPath_1885_);
lean_dec_ref(v___f_1884_);
v_assignment_2005_ = lean_ctor_get(v_a_2001_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v_a_2001_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2007_ = v_a_2001_;
v_isShared_2008_ = v_isSharedCheck_2015_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_assignment_2005_);
lean_dec(v_a_2001_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2015_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2010_; 
if (v_isShared_2008_ == 0)
{
v___x_2010_ = v___x_2007_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_assignment_2005_);
v___x_2010_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
lean_object* v___x_2012_; 
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 0, v___x_2010_);
v___x_2012_ = v___x_2003_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v___x_2010_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
}
}
else
{
lean_del_object(v___x_2003_);
lean_dec(v_a_2001_);
if (v_hasTrace_1921_ == 0)
{
lean_object* v___x_2016_; 
lean_dec_ref(v___f_1884_);
v___x_2016_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_1885_, v_trimProofs_1886_, v___y_1896_, v___y_1897_);
lean_dec_ref(v_lratPath_1885_);
v___y_1900_ = v___x_2016_;
goto v___jp_1899_;
}
else
{
lean_object* v___x_2017_; uint8_t v___x_2018_; 
v___x_2017_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6);
v___x_2018_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1920_, v_options_1918_, v___x_2017_);
if (v___x_2018_ == 0)
{
lean_object* v___x_2019_; uint8_t v___x_2020_; 
v___x_2019_ = l_Lean_trace_profiler;
v___x_2020_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_options_1918_, v___x_2019_);
if (v___x_2020_ == 0)
{
lean_object* v___x_2021_; 
lean_dec_ref(v___f_1884_);
v___x_2021_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_1885_, v_trimProofs_1886_, v___y_1896_, v___y_1897_);
lean_dec_ref(v_lratPath_1885_);
v___y_1900_ = v___x_2021_;
goto v___jp_1899_;
}
else
{
v___y_1957_ = v___x_2018_;
v___y_1958_ = v_options_1918_;
goto v___jp_1956_;
}
}
else
{
v___y_1957_ = v___x_2018_;
v___y_1958_ = v_options_1918_;
goto v___jp_1956_;
}
}
}
}
}
else
{
lean_object* v_a_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2030_; 
lean_dec_ref(v_lratPath_1885_);
lean_dec_ref(v___f_1884_);
v_a_2023_ = lean_ctor_get(v___y_2000_, 0);
v_isSharedCheck_2030_ = !lean_is_exclusive(v___y_2000_);
if (v_isSharedCheck_2030_ == 0)
{
v___x_2025_ = v___y_2000_;
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_a_2023_);
lean_dec(v___y_2000_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v___x_2028_; 
if (v_isShared_2026_ == 0)
{
v___x_2028_ = v___x_2025_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v_a_2023_);
v___x_2028_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
return v___x_2028_;
}
}
}
}
v___jp_2031_:
{
lean_object* v___x_2037_; double v___x_2038_; double v___x_2039_; double v___x_2040_; double v___x_2041_; double v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2037_ = lean_io_mono_nanos_now();
v___x_2038_ = lean_float_of_nat(v___y_2033_);
v___x_2039_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9);
v___x_2040_ = lean_float_div(v___x_2038_, v___x_2039_);
v___x_2041_ = lean_float_of_nat(v___x_2037_);
v___x_2042_ = lean_float_div(v___x_2041_, v___x_2039_);
v___x_2043_ = lean_box_float(v___x_2040_);
v___x_2044_ = lean_box_float(v___x_2042_);
v___x_2045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2045_, 0, v___x_2043_);
lean_ctor_set(v___x_2045_, 1, v___x_2044_);
v___x_2046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2046_, 0, v_a_2036_);
lean_ctor_set(v___x_2046_, 1, v___x_2045_);
v___x_2047_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1(v___x_1922_, v___x_1923_, v___x_1924_, v___y_2032_, v___y_2034_, v___y_2035_, v___f_1887_, v___x_2046_, v___y_1896_, v___y_1897_);
v___y_2000_ = v___x_2047_;
goto v___jp_1999_;
}
v___jp_2048_:
{
lean_object* v___x_2054_; double v___x_2055_; double v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; 
v___x_2054_ = lean_io_get_num_heartbeats();
v___x_2055_ = lean_float_of_nat(v___y_2049_);
v___x_2056_ = lean_float_of_nat(v___x_2054_);
v___x_2057_ = lean_box_float(v___x_2055_);
v___x_2058_ = lean_box_float(v___x_2056_);
v___x_2059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2057_);
lean_ctor_set(v___x_2059_, 1, v___x_2058_);
v___x_2060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2060_, 0, v_a_2053_);
lean_ctor_set(v___x_2060_, 1, v___x_2059_);
v___x_2061_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1(v___x_1922_, v___x_1923_, v___x_1924_, v___y_2050_, v___y_2051_, v___y_2052_, v___f_1887_, v___x_2060_, v___y_1896_, v___y_1897_);
v___y_2000_ = v___x_2061_;
goto v___jp_1999_;
}
v___jp_2062_:
{
lean_object* v___x_2065_; lean_object* v_a_2066_; lean_object* v___x_2067_; uint8_t v___x_2068_; 
v___x_2065_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg(v___y_1897_);
v_a_2066_ = lean_ctor_get(v___x_2065_, 0);
lean_inc(v_a_2066_);
lean_dec_ref(v___x_2065_);
v___x_2067_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2068_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v___y_2063_, v___x_2067_);
if (v___x_2068_ == 0)
{
lean_object* v___x_2069_; lean_object* v___x_2070_; 
v___x_2069_ = lean_io_mono_nanos_now();
lean_inc_ref(v_lratPath_1885_);
v___x_2070_ = l_Lean_Meta_Tactic_BVDecide_External_satQuery(v_solver_1888_, v_cnfPath_1895_, v_lratPath_1885_, v_timeout_1889_, v_binaryProofs_1890_, v_solverMode_1891_, v___y_1896_, v___y_1897_);
if (lean_obj_tag(v___x_2070_) == 0)
{
lean_object* v_a_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2078_; 
v_a_2071_ = lean_ctor_get(v___x_2070_, 0);
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2070_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2073_ = v___x_2070_;
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_a_2071_);
lean_dec(v___x_2070_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2076_; 
if (v_isShared_2074_ == 0)
{
lean_ctor_set_tag(v___x_2073_, 1);
v___x_2076_ = v___x_2073_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_a_2071_);
v___x_2076_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
v___y_2032_ = v___y_2063_;
v___y_2033_ = v___x_2069_;
v___y_2034_ = v___y_2064_;
v___y_2035_ = v_a_2066_;
v_a_2036_ = v___x_2076_;
goto v___jp_2031_;
}
}
}
else
{
lean_object* v_a_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2086_; 
v_a_2079_ = lean_ctor_get(v___x_2070_, 0);
v_isSharedCheck_2086_ = !lean_is_exclusive(v___x_2070_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2081_ = v___x_2070_;
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_a_2079_);
lean_dec(v___x_2070_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v___x_2084_; 
if (v_isShared_2082_ == 0)
{
lean_ctor_set_tag(v___x_2081_, 0);
v___x_2084_ = v___x_2081_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_a_2079_);
v___x_2084_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
v___y_2032_ = v___y_2063_;
v___y_2033_ = v___x_2069_;
v___y_2034_ = v___y_2064_;
v___y_2035_ = v_a_2066_;
v_a_2036_ = v___x_2084_;
goto v___jp_2031_;
}
}
}
}
else
{
lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2087_ = lean_io_get_num_heartbeats();
lean_inc_ref(v_lratPath_1885_);
v___x_2088_ = l_Lean_Meta_Tactic_BVDecide_External_satQuery(v_solver_1888_, v_cnfPath_1895_, v_lratPath_1885_, v_timeout_1889_, v_binaryProofs_1890_, v_solverMode_1891_, v___y_1896_, v___y_1897_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2096_; 
v_a_2089_ = lean_ctor_get(v___x_2088_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2091_ = v___x_2088_;
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_dec(v___x_2088_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2094_; 
if (v_isShared_2092_ == 0)
{
lean_ctor_set_tag(v___x_2091_, 1);
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
v___y_2049_ = v___x_2087_;
v___y_2050_ = v___y_2063_;
v___y_2051_ = v___y_2064_;
v___y_2052_ = v_a_2066_;
v_a_2053_ = v___x_2094_;
goto v___jp_2048_;
}
}
}
else
{
lean_object* v_a_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2104_; 
v_a_2097_ = lean_ctor_get(v___x_2088_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2099_ = v___x_2088_;
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_a_2097_);
lean_dec(v___x_2088_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2102_; 
if (v_isShared_2100_ == 0)
{
lean_ctor_set_tag(v___x_2099_, 0);
v___x_2102_ = v___x_2099_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_a_2097_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
v___y_2049_ = v___x_2087_;
v___y_2050_ = v___y_2063_;
v___y_2051_ = v___y_2064_;
v___y_2052_ = v_a_2066_;
v_a_2053_ = v___x_2102_;
goto v___jp_2048_;
}
}
}
}
}
v___jp_2105_:
{
if (v_hasTrace_1921_ == 0)
{
lean_object* v___x_2106_; 
lean_dec_ref(v___f_1887_);
lean_inc_ref(v_lratPath_1885_);
v___x_2106_ = l_Lean_Meta_Tactic_BVDecide_External_satQuery(v_solver_1888_, v_cnfPath_1895_, v_lratPath_1885_, v_timeout_1889_, v_binaryProofs_1890_, v_solverMode_1891_, v___y_1896_, v___y_1897_);
v___y_2000_ = v___x_2106_;
goto v___jp_1999_;
}
else
{
lean_object* v___x_2107_; uint8_t v___x_2108_; 
v___x_2107_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6);
v___x_2108_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1920_, v_options_1918_, v___x_2107_);
if (v___x_2108_ == 0)
{
lean_object* v___x_2109_; uint8_t v___x_2110_; 
v___x_2109_ = l_Lean_trace_profiler;
v___x_2110_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_options_1918_, v___x_2109_);
if (v___x_2110_ == 0)
{
lean_object* v___x_2111_; 
lean_dec_ref(v___f_1887_);
lean_inc_ref(v_lratPath_1885_);
v___x_2111_ = l_Lean_Meta_Tactic_BVDecide_External_satQuery(v_solver_1888_, v_cnfPath_1895_, v_lratPath_1885_, v_timeout_1889_, v_binaryProofs_1890_, v_solverMode_1891_, v___y_1896_, v___y_1897_);
v___y_2000_ = v___x_2111_;
goto v___jp_1999_;
}
else
{
v___y_2063_ = v_options_1918_;
v___y_2064_ = v___x_2108_;
goto v___jp_2062_;
}
}
else
{
v___y_2063_ = v_options_1918_;
v___y_2064_ = v___x_2108_;
goto v___jp_2062_;
}
}
}
v___jp_2112_:
{
if (lean_obj_tag(v___y_2113_) == 0)
{
lean_dec_ref_known(v___y_2113_, 1);
goto v___jp_2105_;
}
else
{
lean_object* v_a_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2121_; 
lean_dec_ref(v_cnfPath_1895_);
lean_dec_ref(v_solver_1888_);
lean_dec_ref(v___f_1887_);
lean_dec_ref(v_lratPath_1885_);
lean_dec_ref(v___f_1884_);
v_a_2114_ = lean_ctor_get(v___y_2113_, 0);
v_isSharedCheck_2121_ = !lean_is_exclusive(v___y_2113_);
if (v_isSharedCheck_2121_ == 0)
{
v___x_2116_ = v___y_2113_;
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_a_2114_);
lean_dec(v___y_2113_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v___x_2119_; 
if (v_isShared_2117_ == 0)
{
v___x_2119_ = v___x_2116_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v_a_2114_);
v___x_2119_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
return v___x_2119_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__4___boxed(lean_object* v___f_2340_, lean_object* v_lratPath_2341_, lean_object* v_trimProofs_2342_, lean_object* v___f_2343_, lean_object* v_solver_2344_, lean_object* v_timeout_2345_, lean_object* v_binaryProofs_2346_, lean_object* v_solverMode_2347_, lean_object* v___f_2348_, lean_object* v___f_2349_, lean_object* v_cnfHandle_2350_, lean_object* v_cnfPath_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_){
_start:
{
uint8_t v_trimProofs_boxed_2355_; uint8_t v_binaryProofs_boxed_2356_; uint8_t v_solverMode_boxed_2357_; lean_object* v_res_2358_; 
v_trimProofs_boxed_2355_ = lean_unbox(v_trimProofs_2342_);
v_binaryProofs_boxed_2356_ = lean_unbox(v_binaryProofs_2346_);
v_solverMode_boxed_2357_ = lean_unbox(v_solverMode_2347_);
v_res_2358_ = l_Lean_Meta_Tactic_BVDecide_runExternal___lam__4(v___f_2340_, v_lratPath_2341_, v_trimProofs_boxed_2355_, v___f_2343_, v_solver_2344_, v_timeout_2345_, v_binaryProofs_boxed_2356_, v_solverMode_boxed_2357_, v___f_2348_, v___f_2349_, v_cnfHandle_2350_, v_cnfPath_2351_, v___y_2352_, v___y_2353_);
lean_dec(v___y_2353_);
lean_dec_ref(v___y_2352_);
lean_dec(v_cnfHandle_2350_);
lean_dec(v_timeout_2345_);
return v_res_2358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal(lean_object* v_cnf_2362_, lean_object* v_solver_2363_, lean_object* v_lratPath_2364_, uint8_t v_trimProofs_2365_, lean_object* v_timeout_2366_, uint8_t v_binaryProofs_2367_, uint8_t v_solverMode_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_){
_start:
{
lean_object* v___f_2372_; lean_object* v___f_2373_; lean_object* v___f_2374_; lean_object* v___f_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___f_2379_; lean_object* v___x_2380_; 
v___f_2372_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_runExternal___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2372_, 0, v_cnf_2362_);
v___f_2373_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_runExternal___closed__0));
v___f_2374_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_runExternal___closed__1));
v___f_2375_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_runExternal___closed__2));
v___x_2376_ = lean_box(v_trimProofs_2365_);
v___x_2377_ = lean_box(v_binaryProofs_2367_);
v___x_2378_ = lean_box(v_solverMode_2368_);
v___f_2379_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_runExternal___lam__4___boxed), 15, 10);
lean_closure_set(v___f_2379_, 0, v___f_2374_);
lean_closure_set(v___f_2379_, 1, v_lratPath_2364_);
lean_closure_set(v___f_2379_, 2, v___x_2376_);
lean_closure_set(v___f_2379_, 3, v___f_2373_);
lean_closure_set(v___f_2379_, 4, v_solver_2363_);
lean_closure_set(v___f_2379_, 5, v_timeout_2366_);
lean_closure_set(v___f_2379_, 6, v___x_2377_);
lean_closure_set(v___f_2379_, 7, v___x_2378_);
lean_closure_set(v___f_2379_, 8, v___f_2372_);
lean_closure_set(v___f_2379_, 9, v___f_2375_);
v___x_2380_ = l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg(v___f_2379_, v_a_2369_, v_a_2370_);
return v___x_2380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___boxed(lean_object* v_cnf_2381_, lean_object* v_solver_2382_, lean_object* v_lratPath_2383_, lean_object* v_trimProofs_2384_, lean_object* v_timeout_2385_, lean_object* v_binaryProofs_2386_, lean_object* v_solverMode_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_){
_start:
{
uint8_t v_trimProofs_boxed_2391_; uint8_t v_binaryProofs_boxed_2392_; uint8_t v_solverMode_boxed_2393_; lean_object* v_res_2394_; 
v_trimProofs_boxed_2391_ = lean_unbox(v_trimProofs_2384_);
v_binaryProofs_boxed_2392_ = lean_unbox(v_binaryProofs_2386_);
v_solverMode_boxed_2393_ = lean_unbox(v_solverMode_2387_);
v_res_2394_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_cnf_2381_, v_solver_2382_, v_lratPath_2383_, v_trimProofs_boxed_2391_, v_timeout_2385_, v_binaryProofs_boxed_2392_, v_solverMode_boxed_2393_, v_a_2388_, v_a_2389_);
lean_dec(v_a_2389_);
lean_dec_ref(v_a_2388_);
return v_res_2394_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Checker(uint8_t builtin);
lean_object* runtime_initialize_Lean_CoreM(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_LRAT_Trim(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Parser(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_External(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_LRAT_Cert(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Checker(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_LRAT_Trim(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_External(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction = _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction();
lean_mark_persistent(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_BVDecide_LRAT_Cert(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Checker(uint8_t builtin);
lean_object* initialize_Lean_CoreM(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Syntax(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_LRAT_Trim(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Parser(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_External(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_BVDecide_LRAT_Cert(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_LRAT_Checker(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_LRAT_Trim(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_LRAT_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_External(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_LRAT_Cert(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_BVDecide_LRAT_Cert(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_BVDecide_LRAT_Cert(builtin);
}
#ifdef __cplusplus
}
#endif
