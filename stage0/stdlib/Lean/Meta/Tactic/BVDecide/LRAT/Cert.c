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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__4_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__6(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__6___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__1 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__1_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3;
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2_spec__4___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1_spec__2___boxed(lean_object*);
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
v___x_302_ = lean_st_ref_put(v___y_275_, v___x_301_);
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5___redArg(lean_object* v_x_405_){
_start:
{
if (lean_obj_tag(v_x_405_) == 0)
{
lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_414_; 
v_a_407_ = lean_ctor_get(v_x_405_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v_x_405_);
if (v_isSharedCheck_414_ == 0)
{
v___x_409_ = v_x_405_;
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_dec(v_x_405_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_412_; 
if (v_isShared_410_ == 0)
{
lean_ctor_set_tag(v___x_409_, 1);
v___x_412_ = v___x_409_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_a_407_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
}
else
{
lean_object* v_a_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_422_; 
v_a_415_ = lean_ctor_get(v_x_405_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v_x_405_);
if (v_isSharedCheck_422_ == 0)
{
v___x_417_ = v_x_405_;
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_a_415_);
lean_dec(v_x_405_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_420_; 
if (v_isShared_418_ == 0)
{
lean_ctor_set_tag(v___x_417_, 0);
v___x_420_ = v___x_417_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_a_415_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5___redArg___boxed(lean_object* v_x_423_, lean_object* v___y_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5___redArg(v_x_423_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__4_spec__6(size_t v_sz_426_, size_t v_i_427_, lean_object* v_bs_428_){
_start:
{
uint8_t v___x_429_; 
v___x_429_ = lean_usize_dec_lt(v_i_427_, v_sz_426_);
if (v___x_429_ == 0)
{
return v_bs_428_;
}
else
{
lean_object* v_v_430_; lean_object* v_msg_431_; lean_object* v___x_432_; lean_object* v_bs_x27_433_; size_t v___x_434_; size_t v___x_435_; lean_object* v___x_436_; 
v_v_430_ = lean_array_uget_borrowed(v_bs_428_, v_i_427_);
v_msg_431_ = lean_ctor_get(v_v_430_, 1);
lean_inc_ref(v_msg_431_);
v___x_432_ = lean_unsigned_to_nat(0u);
v_bs_x27_433_ = lean_array_uset(v_bs_428_, v_i_427_, v___x_432_);
v___x_434_ = ((size_t)1ULL);
v___x_435_ = lean_usize_add(v_i_427_, v___x_434_);
v___x_436_ = lean_array_uset(v_bs_x27_433_, v_i_427_, v_msg_431_);
v_i_427_ = v___x_435_;
v_bs_428_ = v___x_436_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__4_spec__6___boxed(lean_object* v_sz_438_, lean_object* v_i_439_, lean_object* v_bs_440_){
_start:
{
size_t v_sz_boxed_441_; size_t v_i_boxed_442_; lean_object* v_res_443_; 
v_sz_boxed_441_ = lean_unbox_usize(v_sz_438_);
lean_dec(v_sz_438_);
v_i_boxed_442_ = lean_unbox_usize(v_i_439_);
lean_dec(v_i_439_);
v_res_443_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__4_spec__6(v_sz_boxed_441_, v_i_boxed_442_, v_bs_440_);
return v_res_443_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_444_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_445_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__0);
v___x_446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_446_, 0, v___x_445_);
return v___x_446_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_447_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__1);
v___x_448_ = lean_unsigned_to_nat(0u);
v___x_449_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_449_, 0, v___x_448_);
lean_ctor_set(v___x_449_, 1, v___x_448_);
lean_ctor_set(v___x_449_, 2, v___x_448_);
lean_ctor_set(v___x_449_, 3, v___x_448_);
lean_ctor_set(v___x_449_, 4, v___x_447_);
lean_ctor_set(v___x_449_, 5, v___x_447_);
lean_ctor_set(v___x_449_, 6, v___x_447_);
lean_ctor_set(v___x_449_, 7, v___x_447_);
lean_ctor_set(v___x_449_, 8, v___x_447_);
lean_ctor_set(v___x_449_, 9, v___x_447_);
lean_ctor_set(v___x_449_, 10, v___x_447_);
return v___x_449_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_450_ = lean_unsigned_to_nat(32u);
v___x_451_ = lean_mk_empty_array_with_capacity(v___x_450_);
v___x_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_452_, 0, v___x_451_);
return v___x_452_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_453_ = ((size_t)5ULL);
v___x_454_ = lean_unsigned_to_nat(0u);
v___x_455_ = lean_unsigned_to_nat(32u);
v___x_456_ = lean_mk_empty_array_with_capacity(v___x_455_);
v___x_457_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__3);
v___x_458_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_458_, 0, v___x_457_);
lean_ctor_set(v___x_458_, 1, v___x_456_);
lean_ctor_set(v___x_458_, 2, v___x_454_);
lean_ctor_set(v___x_458_, 3, v___x_454_);
lean_ctor_set_usize(v___x_458_, 4, v___x_453_);
return v___x_458_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_459_ = lean_box(1);
v___x_460_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__4);
v___x_461_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__1);
v___x_462_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_462_, 0, v___x_461_);
lean_ctor_set(v___x_462_, 1, v___x_460_);
lean_ctor_set(v___x_462_, 2, v___x_459_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0(lean_object* v_msgData_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
lean_object* v___x_467_; lean_object* v_toCold_468_; lean_object* v_env_469_; lean_object* v_options_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_467_ = lean_st_ref_get(v___y_465_);
v_toCold_468_ = lean_ctor_get(v___y_464_, 0);
v_env_469_ = lean_ctor_get(v___x_467_, 0);
lean_inc_ref(v_env_469_);
lean_dec(v___x_467_);
v_options_470_ = lean_ctor_get(v_toCold_468_, 2);
v___x_471_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__2);
v___x_472_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_470_);
v___x_473_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_473_, 0, v_env_469_);
lean_ctor_set(v___x_473_, 1, v___x_471_);
lean_ctor_set(v___x_473_, 2, v___x_472_);
lean_ctor_set(v___x_473_, 3, v_options_470_);
v___x_474_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
lean_ctor_set(v___x_474_, 1, v_msgData_463_);
v___x_475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_475_, 0, v___x_474_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___boxed(lean_object* v_msgData_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0(v_msgData_476_, v___y_477_, v___y_478_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__4(lean_object* v_oldTraces_481_, lean_object* v_data_482_, lean_object* v_ref_483_, lean_object* v_msg_484_, lean_object* v___y_485_, lean_object* v___y_486_){
_start:
{
lean_object* v_toCold_488_; lean_object* v_currRecDepth_489_; lean_object* v_ref_490_; uint8_t v_diag_491_; uint8_t v_suppressElabErrors_492_; lean_object* v___x_493_; lean_object* v_traceState_494_; lean_object* v_traces_495_; lean_object* v_ref_496_; lean_object* v___x_497_; lean_object* v___x_498_; size_t v_sz_499_; size_t v___x_500_; lean_object* v___x_501_; lean_object* v_msg_502_; lean_object* v___x_503_; lean_object* v_a_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_541_; 
v_toCold_488_ = lean_ctor_get(v___y_485_, 0);
v_currRecDepth_489_ = lean_ctor_get(v___y_485_, 1);
v_ref_490_ = lean_ctor_get(v___y_485_, 2);
v_diag_491_ = lean_ctor_get_uint8(v___y_485_, sizeof(void*)*3);
v_suppressElabErrors_492_ = lean_ctor_get_uint8(v___y_485_, sizeof(void*)*3 + 1);
v___x_493_ = lean_st_ref_get(v___y_486_);
v_traceState_494_ = lean_ctor_get(v___x_493_, 4);
lean_inc_ref(v_traceState_494_);
lean_dec(v___x_493_);
v_traces_495_ = lean_ctor_get(v_traceState_494_, 0);
lean_inc_ref(v_traces_495_);
lean_dec_ref(v_traceState_494_);
v_ref_496_ = l_Lean_replaceRef(v_ref_483_, v_ref_490_);
lean_inc(v_currRecDepth_489_);
lean_inc_ref(v_toCold_488_);
v___x_497_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_497_, 0, v_toCold_488_);
lean_ctor_set(v___x_497_, 1, v_currRecDepth_489_);
lean_ctor_set(v___x_497_, 2, v_ref_496_);
lean_ctor_set_uint8(v___x_497_, sizeof(void*)*3, v_diag_491_);
lean_ctor_set_uint8(v___x_497_, sizeof(void*)*3 + 1, v_suppressElabErrors_492_);
v___x_498_ = l_Lean_PersistentArray_toArray___redArg(v_traces_495_);
lean_dec_ref(v_traces_495_);
v_sz_499_ = lean_array_size(v___x_498_);
v___x_500_ = ((size_t)0ULL);
v___x_501_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__4_spec__6(v_sz_499_, v___x_500_, v___x_498_);
v_msg_502_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_502_, 0, v_data_482_);
lean_ctor_set(v_msg_502_, 1, v_msg_484_);
lean_ctor_set(v_msg_502_, 2, v___x_501_);
v___x_503_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0(v_msg_502_, v___x_497_, v___y_486_);
lean_dec_ref_known(v___x_497_, 3);
v_a_504_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_541_ == 0)
{
v___x_506_ = v___x_503_;
v_isShared_507_ = v_isSharedCheck_541_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_a_504_);
lean_dec(v___x_503_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_541_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_508_; lean_object* v_traceState_509_; lean_object* v_env_510_; lean_object* v_nextMacroScope_511_; lean_object* v_ngen_512_; lean_object* v_auxDeclNGen_513_; lean_object* v_cache_514_; lean_object* v_messages_515_; lean_object* v_infoState_516_; lean_object* v_snapshotTasks_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_540_; 
v___x_508_ = lean_st_ref_take(v___y_486_);
v_traceState_509_ = lean_ctor_get(v___x_508_, 4);
v_env_510_ = lean_ctor_get(v___x_508_, 0);
v_nextMacroScope_511_ = lean_ctor_get(v___x_508_, 1);
v_ngen_512_ = lean_ctor_get(v___x_508_, 2);
v_auxDeclNGen_513_ = lean_ctor_get(v___x_508_, 3);
v_cache_514_ = lean_ctor_get(v___x_508_, 5);
v_messages_515_ = lean_ctor_get(v___x_508_, 6);
v_infoState_516_ = lean_ctor_get(v___x_508_, 7);
v_snapshotTasks_517_ = lean_ctor_get(v___x_508_, 8);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_540_ == 0)
{
v___x_519_ = v___x_508_;
v_isShared_520_ = v_isSharedCheck_540_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_snapshotTasks_517_);
lean_inc(v_infoState_516_);
lean_inc(v_messages_515_);
lean_inc(v_cache_514_);
lean_inc(v_traceState_509_);
lean_inc(v_auxDeclNGen_513_);
lean_inc(v_ngen_512_);
lean_inc(v_nextMacroScope_511_);
lean_inc(v_env_510_);
lean_dec(v___x_508_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_540_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
uint64_t v_tid_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_538_; 
v_tid_521_ = lean_ctor_get_uint64(v_traceState_509_, sizeof(void*)*1);
v_isSharedCheck_538_ = !lean_is_exclusive(v_traceState_509_);
if (v_isSharedCheck_538_ == 0)
{
lean_object* v_unused_539_; 
v_unused_539_ = lean_ctor_get(v_traceState_509_, 0);
lean_dec(v_unused_539_);
v___x_523_ = v_traceState_509_;
v_isShared_524_ = v_isSharedCheck_538_;
goto v_resetjp_522_;
}
else
{
lean_dec(v_traceState_509_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_538_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_528_; 
v___x_525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_525_, 0, v_ref_483_);
lean_ctor_set(v___x_525_, 1, v_a_504_);
v___x_526_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_481_, v___x_525_);
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 0, v___x_526_);
v___x_528_ = v___x_523_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v___x_526_);
lean_ctor_set_uint64(v_reuseFailAlloc_537_, sizeof(void*)*1, v_tid_521_);
v___x_528_ = v_reuseFailAlloc_537_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
lean_object* v___x_530_; 
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 4, v___x_528_);
v___x_530_ = v___x_519_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_env_510_);
lean_ctor_set(v_reuseFailAlloc_536_, 1, v_nextMacroScope_511_);
lean_ctor_set(v_reuseFailAlloc_536_, 2, v_ngen_512_);
lean_ctor_set(v_reuseFailAlloc_536_, 3, v_auxDeclNGen_513_);
lean_ctor_set(v_reuseFailAlloc_536_, 4, v___x_528_);
lean_ctor_set(v_reuseFailAlloc_536_, 5, v_cache_514_);
lean_ctor_set(v_reuseFailAlloc_536_, 6, v_messages_515_);
lean_ctor_set(v_reuseFailAlloc_536_, 7, v_infoState_516_);
lean_ctor_set(v_reuseFailAlloc_536_, 8, v_snapshotTasks_517_);
v___x_530_ = v_reuseFailAlloc_536_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_534_; 
v___x_531_ = lean_st_ref_put(v___y_486_, v___x_530_);
v___x_532_ = lean_box(0);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 0, v___x_532_);
v___x_534_ = v___x_506_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_532_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__4___boxed(lean_object* v_oldTraces_542_, lean_object* v_data_543_, lean_object* v_ref_544_, lean_object* v_msg_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__4(v_oldTraces_542_, v_data_543_, v_ref_544_, v_msg_545_, v___y_546_, v___y_547_);
lean_dec(v___y_547_);
lean_dec_ref(v___y_546_);
return v_res_549_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__6(lean_object* v_e_550_){
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
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__6___boxed(lean_object* v_e_553_){
_start:
{
uint8_t v_res_554_; lean_object* v_r_555_; 
v_res_554_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__6(v_e_553_);
lean_dec_ref(v_e_553_);
v_r_555_ = lean_box(v_res_554_);
return v_r_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(lean_object* v_opts_556_, lean_object* v_opt_557_){
_start:
{
lean_object* v_name_558_; lean_object* v_defValue_559_; lean_object* v_map_560_; lean_object* v___x_561_; 
v_name_558_ = lean_ctor_get(v_opt_557_, 0);
v_defValue_559_ = lean_ctor_get(v_opt_557_, 1);
v_map_560_ = lean_ctor_get(v_opts_556_, 0);
v___x_561_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_560_, v_name_558_);
if (lean_obj_tag(v___x_561_) == 0)
{
lean_inc(v_defValue_559_);
return v_defValue_559_;
}
else
{
lean_object* v_val_562_; 
v_val_562_ = lean_ctor_get(v___x_561_, 0);
lean_inc(v_val_562_);
lean_dec_ref_known(v___x_561_, 1);
if (lean_obj_tag(v_val_562_) == 3)
{
lean_object* v_v_563_; 
v_v_563_ = lean_ctor_get(v_val_562_, 0);
lean_inc(v_v_563_);
lean_dec_ref_known(v_val_562_, 1);
return v_v_563_;
}
else
{
lean_dec(v_val_562_);
lean_inc(v_defValue_559_);
return v_defValue_559_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7___boxed(lean_object* v_opts_564_, lean_object* v_opt_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(v_opts_564_, v_opt_565_);
lean_dec_ref(v_opt_565_);
lean_dec_ref(v_opts_564_);
return v_res_566_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0(void){
_start:
{
lean_object* v___x_567_; double v___x_568_; 
v___x_567_ = lean_unsigned_to_nat(0u);
v___x_568_ = lean_float_of_nat(v___x_567_);
return v___x_568_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2(void){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__1));
v___x_571_ = l_Lean_stringToMessageData(v___x_570_);
return v___x_571_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3(void){
_start:
{
lean_object* v___x_572_; double v___x_573_; 
v___x_572_ = lean_unsigned_to_nat(1000u);
v___x_573_ = lean_float_of_nat(v___x_572_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3(lean_object* v_cls_574_, uint8_t v_collapsed_575_, lean_object* v_tag_576_, lean_object* v_opts_577_, uint8_t v_clsEnabled_578_, lean_object* v_oldTraces_579_, lean_object* v_msg_580_, lean_object* v_resStartStop_581_, lean_object* v___y_582_, lean_object* v___y_583_){
_start:
{
lean_object* v_fst_585_; lean_object* v_snd_586_; lean_object* v___y_588_; lean_object* v___y_589_; lean_object* v_data_590_; lean_object* v_fst_601_; lean_object* v_snd_602_; lean_object* v___x_603_; uint8_t v___x_604_; lean_object* v___y_606_; lean_object* v_a_607_; uint8_t v___y_622_; double v___y_653_; 
v_fst_585_ = lean_ctor_get(v_resStartStop_581_, 0);
lean_inc(v_fst_585_);
v_snd_586_ = lean_ctor_get(v_resStartStop_581_, 1);
lean_inc(v_snd_586_);
lean_dec_ref(v_resStartStop_581_);
v_fst_601_ = lean_ctor_get(v_snd_586_, 0);
lean_inc(v_fst_601_);
v_snd_602_ = lean_ctor_get(v_snd_586_, 1);
lean_inc(v_snd_602_);
lean_dec(v_snd_586_);
v___x_603_ = l_Lean_trace_profiler;
v___x_604_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_opts_577_, v___x_603_);
if (v___x_604_ == 0)
{
v___y_622_ = v___x_604_;
goto v___jp_621_;
}
else
{
lean_object* v___x_658_; uint8_t v___x_659_; 
v___x_658_ = l_Lean_trace_profiler_useHeartbeats;
v___x_659_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_opts_577_, v___x_658_);
if (v___x_659_ == 0)
{
lean_object* v___x_660_; lean_object* v___x_661_; double v___x_662_; double v___x_663_; double v___x_664_; 
v___x_660_ = l_Lean_trace_profiler_threshold;
v___x_661_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(v_opts_577_, v___x_660_);
v___x_662_ = lean_float_of_nat(v___x_661_);
v___x_663_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3);
v___x_664_ = lean_float_div(v___x_662_, v___x_663_);
v___y_653_ = v___x_664_;
goto v___jp_652_;
}
else
{
lean_object* v___x_665_; lean_object* v___x_666_; double v___x_667_; 
v___x_665_ = l_Lean_trace_profiler_threshold;
v___x_666_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(v_opts_577_, v___x_665_);
v___x_667_ = lean_float_of_nat(v___x_666_);
v___y_653_ = v___x_667_;
goto v___jp_652_;
}
}
v___jp_587_:
{
lean_object* v___x_591_; 
lean_inc(v___y_588_);
v___x_591_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__4(v_oldTraces_579_, v_data_590_, v___y_588_, v___y_589_, v___y_582_, v___y_583_);
if (lean_obj_tag(v___x_591_) == 0)
{
lean_object* v___x_592_; 
lean_dec_ref_known(v___x_591_, 1);
v___x_592_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5___redArg(v_fst_585_);
return v___x_592_;
}
else
{
lean_object* v_a_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_600_; 
lean_dec(v_fst_585_);
v_a_593_ = lean_ctor_get(v___x_591_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_600_ == 0)
{
v___x_595_ = v___x_591_;
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_a_593_);
lean_dec(v___x_591_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_598_; 
if (v_isShared_596_ == 0)
{
v___x_598_ = v___x_595_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_a_593_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
}
v___jp_605_:
{
uint8_t v_result_608_; lean_object* v___x_609_; lean_object* v___x_610_; double v___x_611_; lean_object* v_data_612_; 
v_result_608_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__6(v_fst_585_);
v___x_609_ = lean_box(v_result_608_);
v___x_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_610_, 0, v___x_609_);
v___x_611_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0);
lean_inc_ref(v_tag_576_);
lean_inc_ref(v___x_610_);
lean_inc(v_cls_574_);
v_data_612_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_612_, 0, v_cls_574_);
lean_ctor_set(v_data_612_, 1, v___x_610_);
lean_ctor_set(v_data_612_, 2, v_tag_576_);
lean_ctor_set_float(v_data_612_, sizeof(void*)*3, v___x_611_);
lean_ctor_set_float(v_data_612_, sizeof(void*)*3 + 8, v___x_611_);
lean_ctor_set_uint8(v_data_612_, sizeof(void*)*3 + 16, v_collapsed_575_);
if (v___x_604_ == 0)
{
lean_dec_ref_known(v___x_610_, 1);
lean_dec(v_snd_602_);
lean_dec(v_fst_601_);
lean_dec_ref(v_tag_576_);
lean_dec(v_cls_574_);
v___y_588_ = v___y_606_;
v___y_589_ = v_a_607_;
v_data_590_ = v_data_612_;
goto v___jp_587_;
}
else
{
lean_object* v_data_613_; double v___x_614_; double v___x_615_; 
lean_dec_ref_known(v_data_612_, 3);
v_data_613_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_613_, 0, v_cls_574_);
lean_ctor_set(v_data_613_, 1, v___x_610_);
lean_ctor_set(v_data_613_, 2, v_tag_576_);
v___x_614_ = lean_unbox_float(v_fst_601_);
lean_dec(v_fst_601_);
lean_ctor_set_float(v_data_613_, sizeof(void*)*3, v___x_614_);
v___x_615_ = lean_unbox_float(v_snd_602_);
lean_dec(v_snd_602_);
lean_ctor_set_float(v_data_613_, sizeof(void*)*3 + 8, v___x_615_);
lean_ctor_set_uint8(v_data_613_, sizeof(void*)*3 + 16, v_collapsed_575_);
v___y_588_ = v___y_606_;
v___y_589_ = v_a_607_;
v_data_590_ = v_data_613_;
goto v___jp_587_;
}
}
v___jp_616_:
{
lean_object* v_ref_617_; lean_object* v___x_618_; 
v_ref_617_ = lean_ctor_get(v___y_582_, 2);
lean_inc(v___y_583_);
lean_inc_ref(v___y_582_);
lean_inc(v_fst_585_);
v___x_618_ = lean_apply_4(v_msg_580_, v_fst_585_, v___y_582_, v___y_583_, lean_box(0));
if (lean_obj_tag(v___x_618_) == 0)
{
lean_object* v_a_619_; 
v_a_619_ = lean_ctor_get(v___x_618_, 0);
lean_inc(v_a_619_);
lean_dec_ref_known(v___x_618_, 1);
v___y_606_ = v_ref_617_;
v_a_607_ = v_a_619_;
goto v___jp_605_;
}
else
{
lean_object* v___x_620_; 
lean_dec_ref_known(v___x_618_, 1);
v___x_620_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2);
v___y_606_ = v_ref_617_;
v_a_607_ = v___x_620_;
goto v___jp_605_;
}
}
v___jp_621_:
{
if (v_clsEnabled_578_ == 0)
{
if (v___y_622_ == 0)
{
lean_object* v___x_623_; lean_object* v_traceState_624_; lean_object* v_env_625_; lean_object* v_nextMacroScope_626_; lean_object* v_ngen_627_; lean_object* v_auxDeclNGen_628_; lean_object* v_cache_629_; lean_object* v_messages_630_; lean_object* v_infoState_631_; lean_object* v_snapshotTasks_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_651_; 
lean_dec(v_snd_602_);
lean_dec(v_fst_601_);
lean_dec_ref(v_msg_580_);
lean_dec_ref(v_tag_576_);
lean_dec(v_cls_574_);
v___x_623_ = lean_st_ref_take(v___y_583_);
v_traceState_624_ = lean_ctor_get(v___x_623_, 4);
v_env_625_ = lean_ctor_get(v___x_623_, 0);
v_nextMacroScope_626_ = lean_ctor_get(v___x_623_, 1);
v_ngen_627_ = lean_ctor_get(v___x_623_, 2);
v_auxDeclNGen_628_ = lean_ctor_get(v___x_623_, 3);
v_cache_629_ = lean_ctor_get(v___x_623_, 5);
v_messages_630_ = lean_ctor_get(v___x_623_, 6);
v_infoState_631_ = lean_ctor_get(v___x_623_, 7);
v_snapshotTasks_632_ = lean_ctor_get(v___x_623_, 8);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_651_ == 0)
{
v___x_634_ = v___x_623_;
v_isShared_635_ = v_isSharedCheck_651_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_snapshotTasks_632_);
lean_inc(v_infoState_631_);
lean_inc(v_messages_630_);
lean_inc(v_cache_629_);
lean_inc(v_traceState_624_);
lean_inc(v_auxDeclNGen_628_);
lean_inc(v_ngen_627_);
lean_inc(v_nextMacroScope_626_);
lean_inc(v_env_625_);
lean_dec(v___x_623_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_651_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
uint64_t v_tid_636_; lean_object* v_traces_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_650_; 
v_tid_636_ = lean_ctor_get_uint64(v_traceState_624_, sizeof(void*)*1);
v_traces_637_ = lean_ctor_get(v_traceState_624_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v_traceState_624_);
if (v_isSharedCheck_650_ == 0)
{
v___x_639_ = v_traceState_624_;
v_isShared_640_ = v_isSharedCheck_650_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_traces_637_);
lean_dec(v_traceState_624_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_650_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_641_; lean_object* v___x_643_; 
v___x_641_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_579_, v_traces_637_);
lean_dec_ref(v_traces_637_);
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 0, v___x_641_);
v___x_643_ = v___x_639_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v___x_641_);
lean_ctor_set_uint64(v_reuseFailAlloc_649_, sizeof(void*)*1, v_tid_636_);
v___x_643_ = v_reuseFailAlloc_649_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
lean_object* v___x_645_; 
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 4, v___x_643_);
v___x_645_ = v___x_634_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_env_625_);
lean_ctor_set(v_reuseFailAlloc_648_, 1, v_nextMacroScope_626_);
lean_ctor_set(v_reuseFailAlloc_648_, 2, v_ngen_627_);
lean_ctor_set(v_reuseFailAlloc_648_, 3, v_auxDeclNGen_628_);
lean_ctor_set(v_reuseFailAlloc_648_, 4, v___x_643_);
lean_ctor_set(v_reuseFailAlloc_648_, 5, v_cache_629_);
lean_ctor_set(v_reuseFailAlloc_648_, 6, v_messages_630_);
lean_ctor_set(v_reuseFailAlloc_648_, 7, v_infoState_631_);
lean_ctor_set(v_reuseFailAlloc_648_, 8, v_snapshotTasks_632_);
v___x_645_ = v_reuseFailAlloc_648_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = lean_st_ref_put(v___y_583_, v___x_645_);
v___x_647_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5___redArg(v_fst_585_);
return v___x_647_;
}
}
}
}
}
else
{
goto v___jp_616_;
}
}
else
{
goto v___jp_616_;
}
}
v___jp_652_:
{
double v___x_654_; double v___x_655_; double v___x_656_; uint8_t v___x_657_; 
v___x_654_ = lean_unbox_float(v_snd_602_);
v___x_655_ = lean_unbox_float(v_fst_601_);
v___x_656_ = lean_float_sub(v___x_654_, v___x_655_);
v___x_657_ = lean_float_decLt(v___y_653_, v___x_656_);
v___y_622_ = v___x_657_;
goto v___jp_621_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___boxed(lean_object* v_cls_668_, lean_object* v_collapsed_669_, lean_object* v_tag_670_, lean_object* v_opts_671_, lean_object* v_clsEnabled_672_, lean_object* v_oldTraces_673_, lean_object* v_msg_674_, lean_object* v_resStartStop_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_){
_start:
{
uint8_t v_collapsed_boxed_679_; uint8_t v_clsEnabled_boxed_680_; lean_object* v_res_681_; 
v_collapsed_boxed_679_ = lean_unbox(v_collapsed_669_);
v_clsEnabled_boxed_680_ = lean_unbox(v_clsEnabled_672_);
v_res_681_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3(v_cls_668_, v_collapsed_boxed_679_, v_tag_670_, v_opts_671_, v_clsEnabled_boxed_680_, v_oldTraces_673_, v_msg_674_, v_resStartStop_675_, v___y_676_, v___y_677_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec_ref(v_opts_671_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5___redArg(lean_object* v_msg_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
lean_object* v_ref_686_; lean_object* v___x_687_; lean_object* v_a_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_696_; 
v_ref_686_ = lean_ctor_get(v___y_683_, 2);
v___x_687_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0(v_msg_682_, v___y_683_, v___y_684_);
v_a_688_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_696_ == 0)
{
v___x_690_ = v___x_687_;
v_isShared_691_ = v_isSharedCheck_696_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_a_688_);
lean_dec(v___x_687_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_696_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_692_; lean_object* v___x_694_; 
lean_inc(v_ref_686_);
v___x_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_692_, 0, v_ref_686_);
lean_ctor_set(v___x_692_, 1, v_a_688_);
if (v_isShared_691_ == 0)
{
lean_ctor_set_tag(v___x_690_, 1);
lean_ctor_set(v___x_690_, 0, v___x_692_);
v___x_694_ = v___x_690_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_692_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5___redArg___boxed(lean_object* v_msg_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5___redArg(v_msg_697_, v___y_698_, v___y_699_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0(lean_object* v_cls_705_, lean_object* v_msg_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v_ref_710_; lean_object* v___x_711_; lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_756_; 
v_ref_710_ = lean_ctor_get(v___y_707_, 2);
v___x_711_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0(v_msg_706_, v___y_707_, v___y_708_);
v_a_712_ = lean_ctor_get(v___x_711_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_711_);
if (v_isSharedCheck_756_ == 0)
{
v___x_714_ = v___x_711_;
v_isShared_715_ = v_isSharedCheck_756_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_dec(v___x_711_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_756_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_716_; lean_object* v_traceState_717_; lean_object* v_env_718_; lean_object* v_nextMacroScope_719_; lean_object* v_ngen_720_; lean_object* v_auxDeclNGen_721_; lean_object* v_cache_722_; lean_object* v_messages_723_; lean_object* v_infoState_724_; lean_object* v_snapshotTasks_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_755_; 
v___x_716_ = lean_st_ref_take(v___y_708_);
v_traceState_717_ = lean_ctor_get(v___x_716_, 4);
v_env_718_ = lean_ctor_get(v___x_716_, 0);
v_nextMacroScope_719_ = lean_ctor_get(v___x_716_, 1);
v_ngen_720_ = lean_ctor_get(v___x_716_, 2);
v_auxDeclNGen_721_ = lean_ctor_get(v___x_716_, 3);
v_cache_722_ = lean_ctor_get(v___x_716_, 5);
v_messages_723_ = lean_ctor_get(v___x_716_, 6);
v_infoState_724_ = lean_ctor_get(v___x_716_, 7);
v_snapshotTasks_725_ = lean_ctor_get(v___x_716_, 8);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_755_ == 0)
{
v___x_727_ = v___x_716_;
v_isShared_728_ = v_isSharedCheck_755_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_snapshotTasks_725_);
lean_inc(v_infoState_724_);
lean_inc(v_messages_723_);
lean_inc(v_cache_722_);
lean_inc(v_traceState_717_);
lean_inc(v_auxDeclNGen_721_);
lean_inc(v_ngen_720_);
lean_inc(v_nextMacroScope_719_);
lean_inc(v_env_718_);
lean_dec(v___x_716_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_755_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
uint64_t v_tid_729_; lean_object* v_traces_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_754_; 
v_tid_729_ = lean_ctor_get_uint64(v_traceState_717_, sizeof(void*)*1);
v_traces_730_ = lean_ctor_get(v_traceState_717_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v_traceState_717_);
if (v_isSharedCheck_754_ == 0)
{
v___x_732_ = v_traceState_717_;
v_isShared_733_ = v_isSharedCheck_754_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_traces_730_);
lean_dec(v_traceState_717_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_754_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_734_; double v___x_735_; uint8_t v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_744_; 
v___x_734_ = lean_box(0);
v___x_735_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0);
v___x_736_ = 0;
v___x_737_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0___closed__0));
v___x_738_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_738_, 0, v_cls_705_);
lean_ctor_set(v___x_738_, 1, v___x_734_);
lean_ctor_set(v___x_738_, 2, v___x_737_);
lean_ctor_set_float(v___x_738_, sizeof(void*)*3, v___x_735_);
lean_ctor_set_float(v___x_738_, sizeof(void*)*3 + 8, v___x_735_);
lean_ctor_set_uint8(v___x_738_, sizeof(void*)*3 + 16, v___x_736_);
v___x_739_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0___closed__1));
v___x_740_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_740_, 0, v___x_738_);
lean_ctor_set(v___x_740_, 1, v_a_712_);
lean_ctor_set(v___x_740_, 2, v___x_739_);
lean_inc(v_ref_710_);
v___x_741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_741_, 0, v_ref_710_);
lean_ctor_set(v___x_741_, 1, v___x_740_);
v___x_742_ = l_Lean_PersistentArray_push___redArg(v_traces_730_, v___x_741_);
if (v_isShared_733_ == 0)
{
lean_ctor_set(v___x_732_, 0, v___x_742_);
v___x_744_ = v___x_732_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v___x_742_);
lean_ctor_set_uint64(v_reuseFailAlloc_753_, sizeof(void*)*1, v_tid_729_);
v___x_744_ = v_reuseFailAlloc_753_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
lean_object* v___x_746_; 
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 4, v___x_744_);
v___x_746_ = v___x_727_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_env_718_);
lean_ctor_set(v_reuseFailAlloc_752_, 1, v_nextMacroScope_719_);
lean_ctor_set(v_reuseFailAlloc_752_, 2, v_ngen_720_);
lean_ctor_set(v_reuseFailAlloc_752_, 3, v_auxDeclNGen_721_);
lean_ctor_set(v_reuseFailAlloc_752_, 4, v___x_744_);
lean_ctor_set(v_reuseFailAlloc_752_, 5, v_cache_722_);
lean_ctor_set(v_reuseFailAlloc_752_, 6, v_messages_723_);
lean_ctor_set(v_reuseFailAlloc_752_, 7, v_infoState_724_);
lean_ctor_set(v_reuseFailAlloc_752_, 8, v_snapshotTasks_725_);
v___x_746_ = v_reuseFailAlloc_752_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_750_; 
v___x_747_ = lean_st_ref_put(v___y_708_, v___x_746_);
v___x_748_ = lean_box(0);
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 0, v___x_748_);
v___x_750_ = v___x_714_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v___x_748_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0___boxed(lean_object* v_cls_757_, lean_object* v_msg_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0(v_cls_757_, v_msg_758_, v___y_759_, v___y_760_);
lean_dec(v___y_760_);
lean_dec_ref(v___y_759_);
return v_res_762_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6(void){
_start:
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_773_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__3));
v___x_774_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__5));
v___x_775_ = l_Lean_Name_append(v___x_774_, v___x_773_);
return v___x_775_;
}
}
static double _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9(void){
_start:
{
lean_object* v___x_778_; double v___x_779_; 
v___x_778_ = lean_unsigned_to_nat(1000000000u);
v___x_779_ = lean_float_of_nat(v___x_778_);
return v___x_779_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12(void){
_start:
{
lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_782_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__11));
v___x_783_ = l_Lean_stringToMessageData(v___x_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load(lean_object* v_lratPath_785_, uint8_t v_trimProofs_786_, lean_object* v_a_787_, lean_object* v_a_788_){
_start:
{
lean_object* v___x_790_; 
v___x_790_ = l_IO_FS_readBinFile(v_lratPath_785_);
if (lean_obj_tag(v___x_790_) == 0)
{
lean_object* v_toCold_791_; lean_object* v_options_792_; lean_object* v_a_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_1229_; 
v_toCold_791_ = lean_ctor_get(v_a_787_, 0);
v_options_792_ = lean_ctor_get(v_toCold_791_, 2);
v_a_793_ = lean_ctor_get(v___x_790_, 0);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_790_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_795_ = v___x_790_;
v_isShared_796_ = v_isSharedCheck_1229_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_a_793_);
lean_dec(v___x_790_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_1229_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v_ref_797_; lean_object* v_inheritedTraceOptions_798_; uint8_t v_hasTrace_799_; lean_object* v___f_800_; lean_object* v___f_801_; lean_object* v___x_802_; lean_object* v_proof_804_; lean_object* v___y_805_; lean_object* v_options_806_; lean_object* v_inheritedTraceOptions_807_; lean_object* v___y_808_; lean_object* v_proof_840_; lean_object* v___y_841_; lean_object* v___y_842_; lean_object* v___y_849_; lean_object* v___y_850_; lean_object* v___y_851_; uint8_t v___x_853_; lean_object* v___x_854_; lean_object* v___y_856_; uint8_t v___y_857_; lean_object* v___y_858_; lean_object* v___y_859_; lean_object* v___y_860_; lean_object* v___y_861_; lean_object* v_a_862_; lean_object* v___y_872_; uint8_t v___y_873_; lean_object* v___y_874_; lean_object* v___y_875_; lean_object* v___y_876_; lean_object* v___y_877_; lean_object* v_a_878_; lean_object* v___y_881_; uint8_t v___y_882_; lean_object* v___y_883_; lean_object* v___y_884_; lean_object* v___y_885_; lean_object* v___y_886_; lean_object* v_a_887_; lean_object* v___y_900_; lean_object* v___y_901_; uint8_t v___y_902_; lean_object* v___y_903_; lean_object* v___y_904_; lean_object* v___y_905_; lean_object* v_a_906_; lean_object* v___y_909_; lean_object* v___y_910_; uint8_t v___y_911_; lean_object* v___y_912_; lean_object* v___y_913_; lean_object* v___y_914_; lean_object* v___y_988_; lean_object* v___y_989_; lean_object* v___y_990_; lean_object* v___y_991_; lean_object* v_a_1066_; lean_object* v___y_1088_; 
v_ref_797_ = lean_ctor_get(v_a_787_, 2);
v_inheritedTraceOptions_798_ = lean_ctor_get(v_toCold_791_, 11);
v_hasTrace_799_ = lean_ctor_get_uint8(v_options_792_, sizeof(void*)*1);
v___f_800_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__0));
v___f_801_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__1), 2, 1);
lean_closure_set(v___f_801_, 0, v_a_793_);
v___x_802_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__3));
v___x_853_ = 1;
v___x_854_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0___closed__0));
if (v_hasTrace_799_ == 0)
{
lean_object* v___x_1090_; 
v___x_1090_ = l_IO_lazyPure___redArg(v___f_801_);
if (lean_obj_tag(v___x_1090_) == 0)
{
lean_object* v_a_1091_; 
v_a_1091_ = lean_ctor_get(v___x_1090_, 0);
lean_inc(v_a_1091_);
lean_dec_ref_known(v___x_1090_, 1);
if (lean_obj_tag(v_a_1091_) == 0)
{
lean_object* v_a_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
v_a_1092_ = lean_ctor_get(v_a_1091_, 0);
lean_inc(v_a_1092_);
lean_dec_ref_known(v_a_1091_, 1);
v___x_1093_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12);
v___x_1094_ = l_Lean_stringToMessageData(v_a_1092_);
v___x_1095_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1093_);
lean_ctor_set(v___x_1095_, 1, v___x_1094_);
v___x_1096_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5___redArg(v___x_1095_, v_a_787_, v_a_788_);
v___y_1088_ = v___x_1096_;
goto v___jp_1087_;
}
else
{
lean_object* v_a_1097_; 
v_a_1097_ = lean_ctor_get(v_a_1091_, 0);
lean_inc(v_a_1097_);
lean_dec_ref_known(v_a_1091_, 1);
v_a_1066_ = v_a_1097_;
goto v___jp_1065_;
}
}
else
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1109_; 
lean_del_object(v___x_795_);
v_a_1098_ = lean_ctor_get(v___x_1090_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1100_ = v___x_1090_;
v_isShared_1101_ = v_isSharedCheck_1109_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1090_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1109_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1107_; 
v___x_1102_ = lean_io_error_to_string(v_a_1098_);
v___x_1103_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1102_);
v___x_1104_ = l_Lean_MessageData_ofFormat(v___x_1103_);
lean_inc(v_ref_797_);
v___x_1105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1105_, 0, v_ref_797_);
lean_ctor_set(v___x_1105_, 1, v___x_1104_);
if (v_isShared_1101_ == 0)
{
lean_ctor_set(v___x_1100_, 0, v___x_1105_);
v___x_1107_ = v___x_1100_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v___x_1105_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
}
}
else
{
lean_object* v___f_1110_; lean_object* v___x_1111_; uint8_t v___x_1112_; lean_object* v___y_1114_; lean_object* v___y_1115_; lean_object* v_a_1116_; lean_object* v___y_1129_; lean_object* v___y_1130_; lean_object* v_a_1131_; lean_object* v___y_1134_; lean_object* v___y_1135_; lean_object* v_a_1136_; lean_object* v___y_1139_; lean_object* v___y_1140_; lean_object* v_a_1141_; lean_object* v___y_1151_; lean_object* v___y_1152_; lean_object* v_a_1153_; lean_object* v___y_1156_; lean_object* v___y_1157_; lean_object* v_a_1158_; 
v___f_1110_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__13));
v___x_1111_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6);
v___x_1112_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_798_, v_options_792_, v___x_1111_);
if (v___x_1112_ == 0)
{
lean_object* v___x_1207_; uint8_t v___x_1208_; 
v___x_1207_ = l_Lean_trace_profiler;
v___x_1208_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_options_792_, v___x_1207_);
if (v___x_1208_ == 0)
{
lean_object* v___x_1209_; 
v___x_1209_ = l_IO_lazyPure___redArg(v___f_801_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_object* v_a_1210_; 
v_a_1210_ = lean_ctor_get(v___x_1209_, 0);
lean_inc(v_a_1210_);
lean_dec_ref_known(v___x_1209_, 1);
if (lean_obj_tag(v_a_1210_) == 0)
{
lean_object* v_a_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
v_a_1211_ = lean_ctor_get(v_a_1210_, 0);
lean_inc(v_a_1211_);
lean_dec_ref_known(v_a_1210_, 1);
v___x_1212_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12);
v___x_1213_ = l_Lean_stringToMessageData(v_a_1211_);
v___x_1214_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1212_);
lean_ctor_set(v___x_1214_, 1, v___x_1213_);
v___x_1215_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5___redArg(v___x_1214_, v_a_787_, v_a_788_);
v___y_1088_ = v___x_1215_;
goto v___jp_1087_;
}
else
{
lean_object* v_a_1216_; 
v_a_1216_ = lean_ctor_get(v_a_1210_, 0);
lean_inc(v_a_1216_);
lean_dec_ref_known(v_a_1210_, 1);
v_a_1066_ = v_a_1216_;
goto v___jp_1065_;
}
}
else
{
lean_object* v_a_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1228_; 
lean_del_object(v___x_795_);
v_a_1217_ = lean_ctor_get(v___x_1209_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1219_ = v___x_1209_;
v_isShared_1220_ = v_isSharedCheck_1228_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_a_1217_);
lean_dec(v___x_1209_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1228_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1226_; 
v___x_1221_ = lean_io_error_to_string(v_a_1217_);
v___x_1222_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1221_);
v___x_1223_ = l_Lean_MessageData_ofFormat(v___x_1222_);
lean_inc(v_ref_797_);
v___x_1224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1224_, 0, v_ref_797_);
lean_ctor_set(v___x_1224_, 1, v___x_1223_);
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 0, v___x_1224_);
v___x_1226_ = v___x_1219_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v___x_1224_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
}
else
{
goto v___jp_1160_;
}
}
else
{
goto v___jp_1160_;
}
v___jp_1113_:
{
lean_object* v___x_1117_; double v___x_1118_; double v___x_1119_; double v___x_1120_; double v___x_1121_; double v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1117_ = lean_io_mono_nanos_now();
v___x_1118_ = lean_float_of_nat(v___y_1115_);
v___x_1119_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9);
v___x_1120_ = lean_float_div(v___x_1118_, v___x_1119_);
v___x_1121_ = lean_float_of_nat(v___x_1117_);
v___x_1122_ = lean_float_div(v___x_1121_, v___x_1119_);
v___x_1123_ = lean_box_float(v___x_1120_);
v___x_1124_ = lean_box_float(v___x_1122_);
v___x_1125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1123_);
lean_ctor_set(v___x_1125_, 1, v___x_1124_);
v___x_1126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1126_, 0, v_a_1116_);
lean_ctor_set(v___x_1126_, 1, v___x_1125_);
v___x_1127_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3(v___x_802_, v___x_853_, v___x_854_, v_options_792_, v___x_1112_, v___y_1114_, v___f_1110_, v___x_1126_, v_a_787_, v_a_788_);
v___y_1088_ = v___x_1127_;
goto v___jp_1087_;
}
v___jp_1128_:
{
lean_object* v___x_1132_; 
v___x_1132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1132_, 0, v_a_1131_);
v___y_1114_ = v___y_1129_;
v___y_1115_ = v___y_1130_;
v_a_1116_ = v___x_1132_;
goto v___jp_1113_;
}
v___jp_1133_:
{
lean_object* v___x_1137_; 
v___x_1137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1137_, 0, v_a_1136_);
v___y_1114_ = v___y_1134_;
v___y_1115_ = v___y_1135_;
v_a_1116_ = v___x_1137_;
goto v___jp_1113_;
}
v___jp_1138_:
{
lean_object* v___x_1142_; double v___x_1143_; double v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; 
v___x_1142_ = lean_io_get_num_heartbeats();
v___x_1143_ = lean_float_of_nat(v___y_1139_);
v___x_1144_ = lean_float_of_nat(v___x_1142_);
v___x_1145_ = lean_box_float(v___x_1143_);
v___x_1146_ = lean_box_float(v___x_1144_);
v___x_1147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1145_);
lean_ctor_set(v___x_1147_, 1, v___x_1146_);
v___x_1148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1148_, 0, v_a_1141_);
lean_ctor_set(v___x_1148_, 1, v___x_1147_);
v___x_1149_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3(v___x_802_, v___x_853_, v___x_854_, v_options_792_, v___x_1112_, v___y_1140_, v___f_1110_, v___x_1148_, v_a_787_, v_a_788_);
v___y_1088_ = v___x_1149_;
goto v___jp_1087_;
}
v___jp_1150_:
{
lean_object* v___x_1154_; 
v___x_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1154_, 0, v_a_1153_);
v___y_1139_ = v___y_1151_;
v___y_1140_ = v___y_1152_;
v_a_1141_ = v___x_1154_;
goto v___jp_1138_;
}
v___jp_1155_:
{
lean_object* v___x_1159_; 
v___x_1159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1159_, 0, v_a_1158_);
v___y_1139_ = v___y_1156_;
v___y_1140_ = v___y_1157_;
v_a_1141_ = v___x_1159_;
goto v___jp_1138_;
}
v___jp_1160_:
{
lean_object* v___x_1161_; lean_object* v_a_1162_; lean_object* v___x_1163_; uint8_t v___x_1164_; 
v___x_1161_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg(v_a_788_);
v_a_1162_ = lean_ctor_get(v___x_1161_, 0);
lean_inc(v_a_1162_);
lean_dec_ref(v___x_1161_);
v___x_1163_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1164_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_options_792_, v___x_1163_);
if (v___x_1164_ == 0)
{
lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1165_ = lean_io_mono_nanos_now();
v___x_1166_ = l_IO_lazyPure___redArg(v___f_801_);
if (lean_obj_tag(v___x_1166_) == 0)
{
lean_object* v_a_1167_; 
v_a_1167_ = lean_ctor_get(v___x_1166_, 0);
lean_inc(v_a_1167_);
lean_dec_ref_known(v___x_1166_, 1);
if (lean_obj_tag(v_a_1167_) == 0)
{
lean_object* v_a_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v_a_1173_; 
v_a_1168_ = lean_ctor_get(v_a_1167_, 0);
lean_inc(v_a_1168_);
lean_dec_ref_known(v_a_1167_, 1);
v___x_1169_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12);
v___x_1170_ = l_Lean_stringToMessageData(v_a_1168_);
v___x_1171_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1171_, 0, v___x_1169_);
lean_ctor_set(v___x_1171_, 1, v___x_1170_);
v___x_1172_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5___redArg(v___x_1171_, v_a_787_, v_a_788_);
v_a_1173_ = lean_ctor_get(v___x_1172_, 0);
lean_inc(v_a_1173_);
lean_dec_ref(v___x_1172_);
v___y_1129_ = v_a_1162_;
v___y_1130_ = v___x_1165_;
v_a_1131_ = v_a_1173_;
goto v___jp_1128_;
}
else
{
lean_object* v_a_1174_; 
v_a_1174_ = lean_ctor_get(v_a_1167_, 0);
lean_inc(v_a_1174_);
lean_dec_ref_known(v_a_1167_, 1);
v___y_1134_ = v_a_1162_;
v___y_1135_ = v___x_1165_;
v_a_1136_ = v_a_1174_;
goto v___jp_1133_;
}
}
else
{
lean_object* v_a_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1185_; 
v_a_1175_ = lean_ctor_get(v___x_1166_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1177_ = v___x_1166_;
v_isShared_1178_ = v_isSharedCheck_1185_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_a_1175_);
lean_dec(v___x_1166_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1185_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1179_; lean_object* v___x_1181_; 
v___x_1179_ = lean_io_error_to_string(v_a_1175_);
if (v_isShared_1178_ == 0)
{
lean_ctor_set_tag(v___x_1177_, 3);
lean_ctor_set(v___x_1177_, 0, v___x_1179_);
v___x_1181_ = v___x_1177_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v___x_1179_);
v___x_1181_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1182_ = l_Lean_MessageData_ofFormat(v___x_1181_);
lean_inc(v_ref_797_);
v___x_1183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1183_, 0, v_ref_797_);
lean_ctor_set(v___x_1183_, 1, v___x_1182_);
v___y_1129_ = v_a_1162_;
v___y_1130_ = v___x_1165_;
v_a_1131_ = v___x_1183_;
goto v___jp_1128_;
}
}
}
}
else
{
lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1186_ = lean_io_get_num_heartbeats();
v___x_1187_ = l_IO_lazyPure___redArg(v___f_801_);
if (lean_obj_tag(v___x_1187_) == 0)
{
lean_object* v_a_1188_; 
v_a_1188_ = lean_ctor_get(v___x_1187_, 0);
lean_inc(v_a_1188_);
lean_dec_ref_known(v___x_1187_, 1);
if (lean_obj_tag(v_a_1188_) == 0)
{
lean_object* v_a_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v_a_1194_; 
v_a_1189_ = lean_ctor_get(v_a_1188_, 0);
lean_inc(v_a_1189_);
lean_dec_ref_known(v_a_1188_, 1);
v___x_1190_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12);
v___x_1191_ = l_Lean_stringToMessageData(v_a_1189_);
v___x_1192_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1190_);
lean_ctor_set(v___x_1192_, 1, v___x_1191_);
v___x_1193_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5___redArg(v___x_1192_, v_a_787_, v_a_788_);
v_a_1194_ = lean_ctor_get(v___x_1193_, 0);
lean_inc(v_a_1194_);
lean_dec_ref(v___x_1193_);
v___y_1151_ = v___x_1186_;
v___y_1152_ = v_a_1162_;
v_a_1153_ = v_a_1194_;
goto v___jp_1150_;
}
else
{
lean_object* v_a_1195_; 
v_a_1195_ = lean_ctor_get(v_a_1188_, 0);
lean_inc(v_a_1195_);
lean_dec_ref_known(v_a_1188_, 1);
v___y_1156_ = v___x_1186_;
v___y_1157_ = v_a_1162_;
v_a_1158_ = v_a_1195_;
goto v___jp_1155_;
}
}
else
{
lean_object* v_a_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1206_; 
v_a_1196_ = lean_ctor_get(v___x_1187_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1198_ = v___x_1187_;
v_isShared_1199_ = v_isSharedCheck_1206_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_a_1196_);
lean_dec(v___x_1187_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1206_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1200_; lean_object* v___x_1202_; 
v___x_1200_ = lean_io_error_to_string(v_a_1196_);
if (v_isShared_1199_ == 0)
{
lean_ctor_set_tag(v___x_1198_, 3);
lean_ctor_set(v___x_1198_, 0, v___x_1200_);
v___x_1202_ = v___x_1198_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v___x_1200_);
v___x_1202_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1203_ = l_Lean_MessageData_ofFormat(v___x_1202_);
lean_inc(v_ref_797_);
v___x_1204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1204_, 0, v_ref_797_);
lean_ctor_set(v___x_1204_, 1, v___x_1203_);
v___y_1151_ = v___x_1186_;
v___y_1152_ = v_a_1162_;
v_a_1153_ = v___x_1204_;
goto v___jp_1150_;
}
}
}
}
}
}
v___jp_803_:
{
lean_object* v___x_809_; uint8_t v___x_810_; 
v___x_809_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6);
v___x_810_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_807_, v_options_806_, v___x_809_);
if (v___x_810_ == 0)
{
lean_object* v___x_812_; 
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 0, v_proof_804_);
v___x_812_ = v___x_795_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_proof_804_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
else
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
lean_del_object(v___x_795_);
v___x_814_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__7));
v___x_815_ = lean_array_get_size(v_proof_804_);
v___x_816_ = l_Nat_reprFast(v___x_815_);
v___x_817_ = lean_string_append(v___x_814_, v___x_816_);
lean_dec_ref(v___x_816_);
v___x_818_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__8));
v___x_819_ = lean_string_append(v___x_817_, v___x_818_);
v___x_820_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_820_, 0, v___x_819_);
v___x_821_ = l_Lean_MessageData_ofFormat(v___x_820_);
v___x_822_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0(v___x_802_, v___x_821_, v___y_805_, v___y_808_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_829_; 
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_829_ == 0)
{
lean_object* v_unused_830_; 
v_unused_830_ = lean_ctor_get(v___x_822_, 0);
lean_dec(v_unused_830_);
v___x_824_ = v___x_822_;
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
else
{
lean_dec(v___x_822_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_827_; 
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 0, v_proof_804_);
v___x_827_ = v___x_824_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_proof_804_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
else
{
lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_838_; 
lean_dec_ref(v_proof_804_);
v_a_831_ = lean_ctor_get(v___x_822_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_838_ == 0)
{
v___x_833_ = v___x_822_;
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_822_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_836_; 
if (v_isShared_834_ == 0)
{
v___x_836_ = v___x_833_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_a_831_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
}
}
v___jp_839_:
{
lean_object* v_toCold_843_; lean_object* v_options_844_; uint8_t v_hasTrace_845_; 
v_toCold_843_ = lean_ctor_get(v___y_841_, 0);
v_options_844_ = lean_ctor_get(v_toCold_843_, 2);
v_hasTrace_845_ = lean_ctor_get_uint8(v_options_844_, sizeof(void*)*1);
if (v_hasTrace_845_ == 0)
{
lean_object* v___x_846_; 
lean_del_object(v___x_795_);
v___x_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_846_, 0, v_proof_840_);
return v___x_846_;
}
else
{
lean_object* v_inheritedTraceOptions_847_; 
v_inheritedTraceOptions_847_ = lean_ctor_get(v_toCold_843_, 11);
v_proof_804_ = v_proof_840_;
v___y_805_ = v___y_841_;
v_options_806_ = v_options_844_;
v_inheritedTraceOptions_807_ = v_inheritedTraceOptions_847_;
v___y_808_ = v___y_842_;
goto v___jp_803_;
}
}
v___jp_848_:
{
if (lean_obj_tag(v___y_851_) == 0)
{
lean_object* v_a_852_; 
v_a_852_ = lean_ctor_get(v___y_851_, 0);
lean_inc(v_a_852_);
lean_dec_ref_known(v___y_851_, 1);
v_proof_840_ = v_a_852_;
v___y_841_ = v___y_850_;
v___y_842_ = v___y_849_;
goto v___jp_839_;
}
else
{
lean_del_object(v___x_795_);
return v___y_851_;
}
}
v___jp_855_:
{
lean_object* v___x_863_; double v___x_864_; double v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_863_ = lean_io_get_num_heartbeats();
v___x_864_ = lean_float_of_nat(v___y_858_);
v___x_865_ = lean_float_of_nat(v___x_863_);
v___x_866_ = lean_box_float(v___x_864_);
v___x_867_ = lean_box_float(v___x_865_);
v___x_868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_868_, 0, v___x_866_);
lean_ctor_set(v___x_868_, 1, v___x_867_);
v___x_869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_869_, 0, v_a_862_);
lean_ctor_set(v___x_869_, 1, v___x_868_);
v___x_870_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3(v___x_802_, v___x_853_, v___x_854_, v___y_860_, v___y_857_, v___y_861_, v___f_800_, v___x_869_, v___y_859_, v___y_856_);
v___y_849_ = v___y_856_;
v___y_850_ = v___y_859_;
v___y_851_ = v___x_870_;
goto v___jp_848_;
}
v___jp_871_:
{
lean_object* v___x_879_; 
v___x_879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_879_, 0, v_a_878_);
v___y_856_ = v___y_872_;
v___y_857_ = v___y_873_;
v___y_858_ = v___y_874_;
v___y_859_ = v___y_875_;
v___y_860_ = v___y_876_;
v___y_861_ = v___y_877_;
v_a_862_ = v___x_879_;
goto v___jp_855_;
}
v___jp_880_:
{
lean_object* v___x_888_; double v___x_889_; double v___x_890_; double v___x_891_; double v___x_892_; double v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_888_ = lean_io_mono_nanos_now();
v___x_889_ = lean_float_of_nat(v___y_883_);
v___x_890_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9);
v___x_891_ = lean_float_div(v___x_889_, v___x_890_);
v___x_892_ = lean_float_of_nat(v___x_888_);
v___x_893_ = lean_float_div(v___x_892_, v___x_890_);
v___x_894_ = lean_box_float(v___x_891_);
v___x_895_ = lean_box_float(v___x_893_);
v___x_896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_896_, 0, v___x_894_);
lean_ctor_set(v___x_896_, 1, v___x_895_);
v___x_897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_897_, 0, v_a_887_);
lean_ctor_set(v___x_897_, 1, v___x_896_);
v___x_898_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3(v___x_802_, v___x_853_, v___x_854_, v___y_885_, v___y_882_, v___y_886_, v___f_800_, v___x_897_, v___y_884_, v___y_881_);
v___y_849_ = v___y_881_;
v___y_850_ = v___y_884_;
v___y_851_ = v___x_898_;
goto v___jp_848_;
}
v___jp_899_:
{
lean_object* v___x_907_; 
v___x_907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_907_, 0, v_a_906_);
v___y_881_ = v___y_900_;
v___y_882_ = v___y_902_;
v___y_883_ = v___y_901_;
v___y_884_ = v___y_903_;
v___y_885_ = v___y_904_;
v___y_886_ = v___y_905_;
v_a_887_ = v___x_907_;
goto v___jp_880_;
}
v___jp_908_:
{
lean_object* v___x_915_; lean_object* v_a_916_; lean_object* v___x_917_; uint8_t v___x_918_; 
v___x_915_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg(v___y_909_);
v_a_916_ = lean_ctor_get(v___x_915_, 0);
lean_inc(v_a_916_);
lean_dec_ref(v___x_915_);
v___x_917_ = l_Lean_trace_profiler_useHeartbeats;
v___x_918_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v___y_914_, v___x_917_);
if (v___x_918_ == 0)
{
lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_919_ = lean_io_mono_nanos_now();
v___x_920_ = l_IO_lazyPure___redArg(v___y_910_);
if (lean_obj_tag(v___x_920_) == 0)
{
lean_object* v_a_921_; lean_object* v___x_922_; 
v_a_921_ = lean_ctor_get(v___x_920_, 0);
lean_inc(v_a_921_);
lean_dec_ref_known(v___x_920_, 1);
v___x_922_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__4___redArg(v_a_921_);
if (lean_obj_tag(v___x_922_) == 0)
{
lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_930_; 
v_a_923_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_930_ == 0)
{
v___x_925_ = v___x_922_;
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v___x_922_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_928_; 
if (v_isShared_926_ == 0)
{
lean_ctor_set_tag(v___x_925_, 1);
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
v___y_881_ = v___y_909_;
v___y_882_ = v___y_911_;
v___y_883_ = v___x_919_;
v___y_884_ = v___y_913_;
v___y_885_ = v___y_914_;
v___y_886_ = v_a_916_;
v_a_887_ = v___x_928_;
goto v___jp_880_;
}
}
}
else
{
lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_941_; 
v_a_931_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_941_ == 0)
{
v___x_933_ = v___x_922_;
v_isShared_934_ = v_isSharedCheck_941_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v___x_922_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_941_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_935_; lean_object* v___x_937_; 
v___x_935_ = lean_io_error_to_string(v_a_931_);
if (v_isShared_934_ == 0)
{
lean_ctor_set_tag(v___x_933_, 3);
lean_ctor_set(v___x_933_, 0, v___x_935_);
v___x_937_ = v___x_933_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v___x_935_);
v___x_937_ = v_reuseFailAlloc_940_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_938_ = l_Lean_MessageData_ofFormat(v___x_937_);
lean_inc(v___y_912_);
v___x_939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_939_, 0, v___y_912_);
lean_ctor_set(v___x_939_, 1, v___x_938_);
v___y_900_ = v___y_909_;
v___y_901_ = v___x_919_;
v___y_902_ = v___y_911_;
v___y_903_ = v___y_913_;
v___y_904_ = v___y_914_;
v___y_905_ = v_a_916_;
v_a_906_ = v___x_939_;
goto v___jp_899_;
}
}
}
}
else
{
lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_952_; 
v_a_942_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_952_ == 0)
{
v___x_944_ = v___x_920_;
v_isShared_945_ = v_isSharedCheck_952_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_920_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_952_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_946_; lean_object* v___x_948_; 
v___x_946_ = lean_io_error_to_string(v_a_942_);
if (v_isShared_945_ == 0)
{
lean_ctor_set_tag(v___x_944_, 3);
lean_ctor_set(v___x_944_, 0, v___x_946_);
v___x_948_ = v___x_944_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v___x_946_);
v___x_948_ = v_reuseFailAlloc_951_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_949_ = l_Lean_MessageData_ofFormat(v___x_948_);
lean_inc(v___y_912_);
v___x_950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_950_, 0, v___y_912_);
lean_ctor_set(v___x_950_, 1, v___x_949_);
v___y_900_ = v___y_909_;
v___y_901_ = v___x_919_;
v___y_902_ = v___y_911_;
v___y_903_ = v___y_913_;
v___y_904_ = v___y_914_;
v___y_905_ = v_a_916_;
v_a_906_ = v___x_950_;
goto v___jp_899_;
}
}
}
}
else
{
lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_953_ = lean_io_get_num_heartbeats();
v___x_954_ = l_IO_lazyPure___redArg(v___y_910_);
if (lean_obj_tag(v___x_954_) == 0)
{
lean_object* v_a_955_; lean_object* v___x_956_; 
v_a_955_ = lean_ctor_get(v___x_954_, 0);
lean_inc(v_a_955_);
lean_dec_ref_known(v___x_954_, 1);
v___x_956_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__4___redArg(v_a_955_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_964_; 
v_a_957_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_964_ == 0)
{
v___x_959_ = v___x_956_;
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v___x_956_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_962_; 
if (v_isShared_960_ == 0)
{
lean_ctor_set_tag(v___x_959_, 1);
v___x_962_ = v___x_959_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_a_957_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
v___y_856_ = v___y_909_;
v___y_857_ = v___y_911_;
v___y_858_ = v___x_953_;
v___y_859_ = v___y_913_;
v___y_860_ = v___y_914_;
v___y_861_ = v_a_916_;
v_a_862_ = v___x_962_;
goto v___jp_855_;
}
}
}
else
{
lean_object* v_a_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_975_; 
v_a_965_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_975_ == 0)
{
v___x_967_ = v___x_956_;
v_isShared_968_ = v_isSharedCheck_975_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_a_965_);
lean_dec(v___x_956_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_975_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_969_; lean_object* v___x_971_; 
v___x_969_ = lean_io_error_to_string(v_a_965_);
if (v_isShared_968_ == 0)
{
lean_ctor_set_tag(v___x_967_, 3);
lean_ctor_set(v___x_967_, 0, v___x_969_);
v___x_971_ = v___x_967_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v___x_969_);
v___x_971_ = v_reuseFailAlloc_974_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_972_ = l_Lean_MessageData_ofFormat(v___x_971_);
lean_inc(v___y_912_);
v___x_973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_973_, 0, v___y_912_);
lean_ctor_set(v___x_973_, 1, v___x_972_);
v___y_872_ = v___y_909_;
v___y_873_ = v___y_911_;
v___y_874_ = v___x_953_;
v___y_875_ = v___y_913_;
v___y_876_ = v___y_914_;
v___y_877_ = v_a_916_;
v_a_878_ = v___x_973_;
goto v___jp_871_;
}
}
}
}
else
{
lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_986_; 
v_a_976_ = lean_ctor_get(v___x_954_, 0);
v_isSharedCheck_986_ = !lean_is_exclusive(v___x_954_);
if (v_isSharedCheck_986_ == 0)
{
v___x_978_ = v___x_954_;
v_isShared_979_ = v_isSharedCheck_986_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_dec(v___x_954_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_986_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_980_; lean_object* v___x_982_; 
v___x_980_ = lean_io_error_to_string(v_a_976_);
if (v_isShared_979_ == 0)
{
lean_ctor_set_tag(v___x_978_, 3);
lean_ctor_set(v___x_978_, 0, v___x_980_);
v___x_982_ = v___x_978_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v___x_980_);
v___x_982_ = v_reuseFailAlloc_985_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_983_ = l_Lean_MessageData_ofFormat(v___x_982_);
lean_inc(v___y_912_);
v___x_984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_984_, 0, v___y_912_);
lean_ctor_set(v___x_984_, 1, v___x_983_);
v___y_872_ = v___y_909_;
v___y_873_ = v___y_911_;
v___y_874_ = v___x_953_;
v___y_875_ = v___y_913_;
v___y_876_ = v___y_914_;
v___y_877_ = v_a_916_;
v_a_878_ = v___x_984_;
goto v___jp_871_;
}
}
}
}
}
v___jp_987_:
{
if (v_trimProofs_786_ == 0)
{
lean_dec_ref(v___y_988_);
v_proof_840_ = v___y_989_;
v___y_841_ = v___y_990_;
v___y_842_ = v___y_991_;
goto v___jp_839_;
}
else
{
lean_object* v_toCold_992_; lean_object* v_options_993_; uint8_t v_hasTrace_994_; 
lean_dec_ref(v___y_989_);
v_toCold_992_ = lean_ctor_get(v___y_990_, 0);
v_options_993_ = lean_ctor_get(v_toCold_992_, 2);
v_hasTrace_994_ = lean_ctor_get_uint8(v_options_993_, sizeof(void*)*1);
if (v_hasTrace_994_ == 0)
{
lean_object* v_ref_995_; lean_object* v___x_996_; 
lean_del_object(v___x_795_);
v_ref_995_ = lean_ctor_get(v___y_990_, 2);
v___x_996_ = l_IO_lazyPure___redArg(v___y_988_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v_a_997_; lean_object* v___x_998_; 
v_a_997_ = lean_ctor_get(v___x_996_, 0);
lean_inc(v_a_997_);
lean_dec_ref_known(v___x_996_, 1);
v___x_998_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__4___redArg(v_a_997_);
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
v___x_1004_ = v___x_1001_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_a_999_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
}
}
}
else
{
lean_object* v_a_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1018_; 
v_a_1007_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1009_ = v___x_998_;
v_isShared_1010_ = v_isSharedCheck_1018_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_dec(v___x_998_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1018_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1016_; 
v___x_1011_ = lean_io_error_to_string(v_a_1007_);
v___x_1012_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
v___x_1013_ = l_Lean_MessageData_ofFormat(v___x_1012_);
lean_inc(v_ref_995_);
v___x_1014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1014_, 0, v_ref_995_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 0, v___x_1014_);
v___x_1016_ = v___x_1009_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v___x_1014_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
}
else
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1030_; 
v_a_1019_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1021_ = v___x_996_;
v_isShared_1022_ = v_isSharedCheck_1030_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_996_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1030_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1028_; 
v___x_1023_ = lean_io_error_to_string(v_a_1019_);
v___x_1024_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1023_);
v___x_1025_ = l_Lean_MessageData_ofFormat(v___x_1024_);
lean_inc(v_ref_995_);
v___x_1026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1026_, 0, v_ref_995_);
lean_ctor_set(v___x_1026_, 1, v___x_1025_);
if (v_isShared_1022_ == 0)
{
lean_ctor_set(v___x_1021_, 0, v___x_1026_);
v___x_1028_ = v___x_1021_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v___x_1026_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
else
{
lean_object* v_ref_1031_; lean_object* v_inheritedTraceOptions_1032_; lean_object* v___x_1033_; uint8_t v___x_1034_; 
v_ref_1031_ = lean_ctor_get(v___y_990_, 2);
v_inheritedTraceOptions_1032_ = lean_ctor_get(v_toCold_992_, 11);
v___x_1033_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6);
v___x_1034_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1032_, v_options_993_, v___x_1033_);
if (v___x_1034_ == 0)
{
lean_object* v___x_1035_; uint8_t v___x_1036_; 
v___x_1035_ = l_Lean_trace_profiler;
v___x_1036_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_options_993_, v___x_1035_);
if (v___x_1036_ == 0)
{
lean_object* v___x_1037_; 
v___x_1037_ = l_IO_lazyPure___redArg(v___y_988_);
if (lean_obj_tag(v___x_1037_) == 0)
{
lean_object* v_a_1038_; lean_object* v___x_1039_; 
v_a_1038_ = lean_ctor_get(v___x_1037_, 0);
lean_inc(v_a_1038_);
lean_dec_ref_known(v___x_1037_, 1);
v___x_1039_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__4___redArg(v_a_1038_);
if (lean_obj_tag(v___x_1039_) == 0)
{
lean_object* v_a_1040_; 
v_a_1040_ = lean_ctor_get(v___x_1039_, 0);
lean_inc(v_a_1040_);
lean_dec_ref_known(v___x_1039_, 1);
v_proof_804_ = v_a_1040_;
v___y_805_ = v___y_990_;
v_options_806_ = v_options_993_;
v_inheritedTraceOptions_807_ = v_inheritedTraceOptions_1032_;
v___y_808_ = v___y_991_;
goto v___jp_803_;
}
else
{
lean_object* v_a_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1052_; 
lean_del_object(v___x_795_);
v_a_1041_ = lean_ctor_get(v___x_1039_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1043_ = v___x_1039_;
v_isShared_1044_ = v_isSharedCheck_1052_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_a_1041_);
lean_dec(v___x_1039_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1052_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1050_; 
v___x_1045_ = lean_io_error_to_string(v_a_1041_);
v___x_1046_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1045_);
v___x_1047_ = l_Lean_MessageData_ofFormat(v___x_1046_);
lean_inc(v_ref_1031_);
v___x_1048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1048_, 0, v_ref_1031_);
lean_ctor_set(v___x_1048_, 1, v___x_1047_);
if (v_isShared_1044_ == 0)
{
lean_ctor_set(v___x_1043_, 0, v___x_1048_);
v___x_1050_ = v___x_1043_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v___x_1048_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
}
else
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1064_; 
lean_del_object(v___x_795_);
v_a_1053_ = lean_ctor_get(v___x_1037_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1055_ = v___x_1037_;
v_isShared_1056_ = v_isSharedCheck_1064_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_1037_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1064_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1062_; 
v___x_1057_ = lean_io_error_to_string(v_a_1053_);
v___x_1058_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1057_);
v___x_1059_ = l_Lean_MessageData_ofFormat(v___x_1058_);
lean_inc(v_ref_1031_);
v___x_1060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1060_, 0, v_ref_1031_);
lean_ctor_set(v___x_1060_, 1, v___x_1059_);
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 0, v___x_1060_);
v___x_1062_ = v___x_1055_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v___x_1060_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
}
else
{
v___y_909_ = v___y_991_;
v___y_910_ = v___y_988_;
v___y_911_ = v___x_1034_;
v___y_912_ = v_ref_1031_;
v___y_913_ = v___y_990_;
v___y_914_ = v_options_993_;
goto v___jp_908_;
}
}
else
{
v___y_909_ = v___y_991_;
v___y_910_ = v___y_988_;
v___y_911_ = v___x_1034_;
v___y_912_ = v_ref_1031_;
v___y_913_ = v___y_990_;
v___y_914_ = v_options_993_;
goto v___jp_908_;
}
}
}
}
v___jp_1065_:
{
lean_object* v___f_1067_; 
lean_inc_ref(v_a_1066_);
v___f_1067_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__2___boxed), 2, 1);
lean_closure_set(v___f_1067_, 0, v_a_1066_);
if (v_hasTrace_799_ == 0)
{
v___y_988_ = v___f_1067_;
v___y_989_ = v_a_1066_;
v___y_990_ = v_a_787_;
v___y_991_ = v_a_788_;
goto v___jp_987_;
}
else
{
lean_object* v___x_1068_; uint8_t v___x_1069_; 
v___x_1068_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6);
v___x_1069_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_798_, v_options_792_, v___x_1068_);
if (v___x_1069_ == 0)
{
v___y_988_ = v___f_1067_;
v___y_989_ = v_a_1066_;
v___y_990_ = v_a_787_;
v___y_991_ = v_a_788_;
goto v___jp_987_;
}
else
{
lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1070_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__7));
v___x_1071_ = lean_array_get_size(v_a_1066_);
v___x_1072_ = l_Nat_reprFast(v___x_1071_);
v___x_1073_ = lean_string_append(v___x_1070_, v___x_1072_);
lean_dec_ref(v___x_1072_);
v___x_1074_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__10));
v___x_1075_ = lean_string_append(v___x_1073_, v___x_1074_);
v___x_1076_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1075_);
v___x_1077_ = l_Lean_MessageData_ofFormat(v___x_1076_);
v___x_1078_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0(v___x_802_, v___x_1077_, v_a_787_, v_a_788_);
if (lean_obj_tag(v___x_1078_) == 0)
{
lean_dec_ref_known(v___x_1078_, 1);
v___y_988_ = v___f_1067_;
v___y_989_ = v_a_1066_;
v___y_990_ = v_a_787_;
v___y_991_ = v_a_788_;
goto v___jp_987_;
}
else
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1086_; 
lean_dec_ref(v___f_1067_);
lean_dec_ref(v_a_1066_);
lean_del_object(v___x_795_);
v_a_1079_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1081_ = v___x_1078_;
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1078_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1084_; 
if (v_isShared_1082_ == 0)
{
v___x_1084_ = v___x_1081_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_a_1079_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
}
}
}
v___jp_1087_:
{
if (lean_obj_tag(v___y_1088_) == 0)
{
lean_object* v_a_1089_; 
v_a_1089_ = lean_ctor_get(v___y_1088_, 0);
lean_inc(v_a_1089_);
lean_dec_ref_known(v___y_1088_, 1);
v_a_1066_ = v_a_1089_;
goto v___jp_1065_;
}
else
{
lean_del_object(v___x_795_);
return v___y_1088_;
}
}
}
}
else
{
lean_object* v_a_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1242_; 
v_a_1230_ = lean_ctor_get(v___x_790_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_790_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1232_ = v___x_790_;
v_isShared_1233_ = v_isSharedCheck_1242_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_a_1230_);
lean_dec(v___x_790_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1242_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v_ref_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1240_; 
v_ref_1234_ = lean_ctor_get(v_a_787_, 2);
v___x_1235_ = lean_io_error_to_string(v_a_1230_);
v___x_1236_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1236_, 0, v___x_1235_);
v___x_1237_ = l_Lean_MessageData_ofFormat(v___x_1236_);
lean_inc(v_ref_1234_);
v___x_1238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1238_, 0, v_ref_1234_);
lean_ctor_set(v___x_1238_, 1, v___x_1237_);
if (v_isShared_1233_ == 0)
{
lean_ctor_set(v___x_1232_, 0, v___x_1238_);
v___x_1240_ = v___x_1232_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v___x_1238_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___boxed(lean_object* v_lratPath_1243_, lean_object* v_trimProofs_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_){
_start:
{
uint8_t v_trimProofs_boxed_1248_; lean_object* v_res_1249_; 
v_trimProofs_boxed_1248_ = lean_unbox(v_trimProofs_1244_);
v_res_1249_ = l_Lean_Meta_Tactic_BVDecide_LratCert_load(v_lratPath_1243_, v_trimProofs_boxed_1248_, v_a_1245_, v_a_1246_);
lean_dec(v_a_1246_);
lean_dec_ref(v_a_1245_);
lean_dec_ref(v_lratPath_1243_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5(lean_object* v_00_u03b1_1250_, lean_object* v_x_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_){
_start:
{
lean_object* v___x_1255_; 
v___x_1255_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5___redArg(v_x_1251_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1256_, lean_object* v_x_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5(v_00_u03b1_1256_, v_x_1257_, v___y_1258_, v___y_1259_);
lean_dec(v___y_1259_);
lean_dec_ref(v___y_1258_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5(lean_object* v_00_u03b1_1262_, lean_object* v_msg_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_){
_start:
{
lean_object* v___x_1267_; 
v___x_1267_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5___redArg(v_msg_1263_, v___y_1264_, v___y_1265_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5___boxed(lean_object* v_00_u03b1_1268_, lean_object* v_msg_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5(v_00_u03b1_1268_, v_msg_1269_, v___y_1270_, v___y_1271_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(lean_object* v_lratPath_1274_, uint8_t v_trimProofs_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_){
_start:
{
lean_object* v___x_1279_; 
v___x_1279_ = l_Lean_Meta_Tactic_BVDecide_LratCert_load(v_lratPath_1274_, v_trimProofs_1275_, v_a_1276_, v_a_1277_);
if (lean_obj_tag(v___x_1279_) == 0)
{
lean_object* v_a_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1288_; 
v_a_1280_ = lean_ctor_get(v___x_1279_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1282_ = v___x_1279_;
v_isShared_1283_ = v_isSharedCheck_1288_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_a_1280_);
lean_dec(v___x_1279_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1288_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1284_; lean_object* v___x_1286_; 
v___x_1284_ = l_Std_Tactic_BVDecide_LRAT_lratProofToString(v_a_1280_);
lean_dec(v_a_1280_);
if (v_isShared_1283_ == 0)
{
lean_ctor_set(v___x_1282_, 0, v___x_1284_);
v___x_1286_ = v___x_1282_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v___x_1284_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
}
else
{
lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1296_; 
v_a_1289_ = lean_ctor_get(v___x_1279_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1291_ = v___x_1279_;
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_dec(v___x_1279_);
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
v_reuseFailAlloc_1295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_a_1289_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile___boxed(lean_object* v_lratPath_1297_, lean_object* v_trimProofs_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_){
_start:
{
uint8_t v_trimProofs_boxed_1302_; lean_object* v_res_1303_; 
v_trimProofs_boxed_1302_ = lean_unbox(v_trimProofs_1298_);
v_res_1303_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_1297_, v_trimProofs_boxed_1302_, v_a_1299_, v_a_1300_);
lean_dec(v_a_1300_);
lean_dec_ref(v_a_1299_);
lean_dec_ref(v_lratPath_1297_);
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg___lam__0(lean_object* v_snd_1304_, lean_object* v___y_1305_, lean_object* v_a_x3f_1306_){
_start:
{
lean_object* v___x_1308_; 
v___x_1308_ = lean_io_remove_file(v_snd_1304_);
if (lean_obj_tag(v___x_1308_) == 0)
{
lean_object* v_a_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1316_; 
v_a_1309_ = lean_ctor_get(v___x_1308_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1311_ = v___x_1308_;
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_a_1309_);
lean_dec(v___x_1308_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1314_; 
if (v_isShared_1312_ == 0)
{
v___x_1314_ = v___x_1311_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_a_1309_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
else
{
lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1329_; 
v_a_1317_ = lean_ctor_get(v___x_1308_, 0);
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1319_ = v___x_1308_;
v_isShared_1320_ = v_isSharedCheck_1329_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v___x_1308_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1329_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v_ref_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1327_; 
v_ref_1321_ = lean_ctor_get(v___y_1305_, 2);
v___x_1322_ = lean_io_error_to_string(v_a_1317_);
v___x_1323_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1322_);
v___x_1324_ = l_Lean_MessageData_ofFormat(v___x_1323_);
lean_inc(v_ref_1321_);
v___x_1325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1325_, 0, v_ref_1321_);
lean_ctor_set(v___x_1325_, 1, v___x_1324_);
if (v_isShared_1320_ == 0)
{
lean_ctor_set(v___x_1319_, 0, v___x_1325_);
v___x_1327_ = v___x_1319_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v___x_1325_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg___lam__0___boxed(lean_object* v_snd_1330_, lean_object* v___y_1331_, lean_object* v_a_x3f_1332_, lean_object* v___y_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg___lam__0(v_snd_1330_, v___y_1331_, v_a_x3f_1332_);
lean_dec(v_a_x3f_1332_);
lean_dec_ref(v___y_1331_);
lean_dec_ref(v_snd_1330_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg(lean_object* v_f_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_){
_start:
{
lean_object* v___x_1339_; 
v___x_1339_ = lean_io_create_tempfile();
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_object* v_a_1340_; lean_object* v_fst_1341_; lean_object* v_snd_1342_; lean_object* v_r_1343_; 
v_a_1340_ = lean_ctor_get(v___x_1339_, 0);
lean_inc(v_a_1340_);
lean_dec_ref_known(v___x_1339_, 1);
v_fst_1341_ = lean_ctor_get(v_a_1340_, 0);
lean_inc(v_fst_1341_);
v_snd_1342_ = lean_ctor_get(v_a_1340_, 1);
lean_inc_n(v_snd_1342_, 2);
lean_dec(v_a_1340_);
lean_inc(v___y_1337_);
lean_inc_ref(v___y_1336_);
v_r_1343_ = lean_apply_5(v_f_1335_, v_fst_1341_, v_snd_1342_, v___y_1336_, v___y_1337_, lean_box(0));
if (lean_obj_tag(v_r_1343_) == 0)
{
lean_object* v_a_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1368_; 
v_a_1344_ = lean_ctor_get(v_r_1343_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v_r_1343_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1346_ = v_r_1343_;
v_isShared_1347_ = v_isSharedCheck_1368_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_a_1344_);
lean_dec(v_r_1343_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1368_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1349_; 
lean_inc(v_a_1344_);
if (v_isShared_1347_ == 0)
{
lean_ctor_set_tag(v___x_1346_, 1);
v___x_1349_ = v___x_1346_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_a_1344_);
v___x_1349_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
lean_object* v___x_1350_; 
v___x_1350_ = l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg___lam__0(v_snd_1342_, v___y_1336_, v___x_1349_);
lean_dec_ref(v___x_1349_);
lean_dec(v_snd_1342_);
if (lean_obj_tag(v___x_1350_) == 0)
{
lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1357_; 
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1350_);
if (v_isSharedCheck_1357_ == 0)
{
lean_object* v_unused_1358_; 
v_unused_1358_ = lean_ctor_get(v___x_1350_, 0);
lean_dec(v_unused_1358_);
v___x_1352_ = v___x_1350_;
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
else
{
lean_dec(v___x_1350_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1355_; 
if (v_isShared_1353_ == 0)
{
lean_ctor_set(v___x_1352_, 0, v_a_1344_);
v___x_1355_ = v___x_1352_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_a_1344_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
}
else
{
lean_object* v_a_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1366_; 
lean_dec(v_a_1344_);
v_a_1359_ = lean_ctor_get(v___x_1350_, 0);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1350_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1361_ = v___x_1350_;
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_a_1359_);
lean_dec(v___x_1350_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1364_; 
if (v_isShared_1362_ == 0)
{
v___x_1364_ = v___x_1361_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_a_1359_);
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
else
{
lean_object* v_a_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; 
v_a_1369_ = lean_ctor_get(v_r_1343_, 0);
lean_inc(v_a_1369_);
lean_dec_ref_known(v_r_1343_, 1);
v___x_1370_ = lean_box(0);
v___x_1371_ = l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg___lam__0(v_snd_1342_, v___y_1336_, v___x_1370_);
lean_dec(v_snd_1342_);
if (lean_obj_tag(v___x_1371_) == 0)
{
lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1378_; 
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1371_);
if (v_isSharedCheck_1378_ == 0)
{
lean_object* v_unused_1379_; 
v_unused_1379_ = lean_ctor_get(v___x_1371_, 0);
lean_dec(v_unused_1379_);
v___x_1373_ = v___x_1371_;
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
else
{
lean_dec(v___x_1371_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1376_; 
if (v_isShared_1374_ == 0)
{
lean_ctor_set_tag(v___x_1373_, 1);
lean_ctor_set(v___x_1373_, 0, v_a_1369_);
v___x_1376_ = v___x_1373_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_a_1369_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
else
{
lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1387_; 
lean_dec(v_a_1369_);
v_a_1380_ = lean_ctor_get(v___x_1371_, 0);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1371_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1382_ = v___x_1371_;
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v___x_1371_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1385_; 
if (v_isShared_1383_ == 0)
{
v___x_1385_ = v___x_1382_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_a_1380_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
}
}
else
{
lean_object* v_a_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1400_; 
lean_dec_ref(v_f_1335_);
v_a_1388_ = lean_ctor_get(v___x_1339_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1390_ = v___x_1339_;
v_isShared_1391_ = v_isSharedCheck_1400_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_a_1388_);
lean_dec(v___x_1339_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1400_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v_ref_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1398_; 
v_ref_1392_ = lean_ctor_get(v___y_1336_, 2);
v___x_1393_ = lean_io_error_to_string(v_a_1388_);
v___x_1394_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1394_, 0, v___x_1393_);
v___x_1395_ = l_Lean_MessageData_ofFormat(v___x_1394_);
lean_inc(v_ref_1392_);
v___x_1396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1396_, 0, v_ref_1392_);
lean_ctor_set(v___x_1396_, 1, v___x_1395_);
if (v_isShared_1391_ == 0)
{
lean_ctor_set(v___x_1390_, 0, v___x_1396_);
v___x_1398_ = v___x_1390_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v___x_1396_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg___boxed(lean_object* v_f_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_){
_start:
{
lean_object* v_res_1405_; 
v_res_1405_ = l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg(v_f_1401_, v___y_1402_, v___y_1403_);
lean_dec(v___y_1403_);
lean_dec_ref(v___y_1402_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3(lean_object* v_00_u03b1_1406_, lean_object* v_f_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
lean_object* v___x_1411_; 
v___x_1411_ = l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg(v_f_1407_, v___y_1408_, v___y_1409_);
return v___x_1411_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___boxed(lean_object* v_00_u03b1_1412_, lean_object* v_f_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
lean_object* v_res_1417_; 
v_res_1417_ = l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3(v_00_u03b1_1412_, v_f_1413_, v___y_1414_, v___y_1415_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
return v_res_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__0(lean_object* v_cnf_1418_, lean_object* v_x_1419_){
_start:
{
lean_object* v___x_1420_; 
v___x_1420_ = l_Std_Sat_CNF_dimacs(v_cnf_1418_);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__0___boxed(lean_object* v_cnf_1421_, lean_object* v_x_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l_Lean_Meta_Tactic_BVDecide_runExternal___lam__0(v_cnf_1421_, v_x_1422_);
lean_dec_ref(v_cnf_1421_);
return v_res_1423_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; 
v___x_1427_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1___closed__1));
v___x_1428_ = l_Lean_MessageData_ofFormat(v___x_1427_);
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1(lean_object* v_x_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1433_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1___closed__2, &l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1___closed__2);
v___x_1434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1434_, 0, v___x_1433_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1___boxed(lean_object* v_x_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_){
_start:
{
lean_object* v_res_1439_; 
v_res_1439_ = l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1(v_x_1435_, v___y_1436_, v___y_1437_);
lean_dec(v___y_1437_);
lean_dec_ref(v___y_1436_);
lean_dec_ref(v_x_1435_);
return v_res_1439_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2___closed__2(void){
_start:
{
lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___x_1443_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2___closed__1));
v___x_1444_ = l_Lean_MessageData_ofFormat(v___x_1443_);
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2(lean_object* v_x_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___x_1449_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2___closed__2, &l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2___closed__2);
v___x_1450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1449_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2___boxed(lean_object* v_x_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_){
_start:
{
lean_object* v_res_1455_; 
v_res_1455_ = l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2(v_x_1451_, v___y_1452_, v___y_1453_);
lean_dec(v___y_1453_);
lean_dec_ref(v___y_1452_);
lean_dec_ref(v_x_1451_);
return v_res_1455_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3___closed__2(void){
_start:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1459_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3___closed__1));
v___x_1460_ = l_Lean_MessageData_ofFormat(v___x_1459_);
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3(lean_object* v_x_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1465_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3___closed__2, &l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3___closed__2);
v___x_1466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1466_, 0, v___x_1465_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3___boxed(lean_object* v_x_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_){
_start:
{
lean_object* v_res_1471_; 
v_res_1471_ = l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3(v_x_1467_, v___y_1468_, v___y_1469_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
lean_dec_ref(v_x_1467_);
return v_res_1471_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2_spec__4(lean_object* v_e_1472_){
_start:
{
if (lean_obj_tag(v_e_1472_) == 0)
{
uint8_t v___x_1473_; 
v___x_1473_ = 2;
return v___x_1473_;
}
else
{
uint8_t v___x_1474_; 
v___x_1474_ = 0;
return v___x_1474_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2_spec__4___boxed(lean_object* v_e_1475_){
_start:
{
uint8_t v_res_1476_; lean_object* v_r_1477_; 
v_res_1476_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2_spec__4(v_e_1475_);
lean_dec_ref(v_e_1475_);
v_r_1477_ = lean_box(v_res_1476_);
return v_r_1477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2(lean_object* v_cls_1478_, uint8_t v_collapsed_1479_, lean_object* v_tag_1480_, lean_object* v_opts_1481_, uint8_t v_clsEnabled_1482_, lean_object* v_oldTraces_1483_, lean_object* v_msg_1484_, lean_object* v_resStartStop_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_){
_start:
{
lean_object* v_fst_1489_; lean_object* v_snd_1490_; lean_object* v___y_1492_; lean_object* v___y_1493_; lean_object* v_data_1494_; lean_object* v_fst_1497_; lean_object* v_snd_1498_; lean_object* v___x_1499_; uint8_t v___x_1500_; lean_object* v___y_1502_; lean_object* v_a_1503_; uint8_t v___y_1518_; double v___y_1549_; 
v_fst_1489_ = lean_ctor_get(v_resStartStop_1485_, 0);
lean_inc(v_fst_1489_);
v_snd_1490_ = lean_ctor_get(v_resStartStop_1485_, 1);
lean_inc(v_snd_1490_);
lean_dec_ref(v_resStartStop_1485_);
v_fst_1497_ = lean_ctor_get(v_snd_1490_, 0);
lean_inc(v_fst_1497_);
v_snd_1498_ = lean_ctor_get(v_snd_1490_, 1);
lean_inc(v_snd_1498_);
lean_dec(v_snd_1490_);
v___x_1499_ = l_Lean_trace_profiler;
v___x_1500_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_opts_1481_, v___x_1499_);
if (v___x_1500_ == 0)
{
v___y_1518_ = v___x_1500_;
goto v___jp_1517_;
}
else
{
lean_object* v___x_1554_; uint8_t v___x_1555_; 
v___x_1554_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1555_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_opts_1481_, v___x_1554_);
if (v___x_1555_ == 0)
{
lean_object* v___x_1556_; lean_object* v___x_1557_; double v___x_1558_; double v___x_1559_; double v___x_1560_; 
v___x_1556_ = l_Lean_trace_profiler_threshold;
v___x_1557_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(v_opts_1481_, v___x_1556_);
v___x_1558_ = lean_float_of_nat(v___x_1557_);
v___x_1559_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3);
v___x_1560_ = lean_float_div(v___x_1558_, v___x_1559_);
v___y_1549_ = v___x_1560_;
goto v___jp_1548_;
}
else
{
lean_object* v___x_1561_; lean_object* v___x_1562_; double v___x_1563_; 
v___x_1561_ = l_Lean_trace_profiler_threshold;
v___x_1562_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(v_opts_1481_, v___x_1561_);
v___x_1563_ = lean_float_of_nat(v___x_1562_);
v___y_1549_ = v___x_1563_;
goto v___jp_1548_;
}
}
v___jp_1491_:
{
lean_object* v___x_1495_; 
lean_inc(v___y_1493_);
v___x_1495_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__4(v_oldTraces_1483_, v_data_1494_, v___y_1493_, v___y_1492_, v___y_1486_, v___y_1487_);
if (lean_obj_tag(v___x_1495_) == 0)
{
lean_object* v___x_1496_; 
lean_dec_ref_known(v___x_1495_, 1);
v___x_1496_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5___redArg(v_fst_1489_);
return v___x_1496_;
}
else
{
lean_dec(v_fst_1489_);
return v___x_1495_;
}
}
v___jp_1501_:
{
uint8_t v_result_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; double v___x_1507_; lean_object* v_data_1508_; 
v_result_1504_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2_spec__4(v_fst_1489_);
v___x_1505_ = lean_box(v_result_1504_);
v___x_1506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1505_);
v___x_1507_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0);
lean_inc_ref(v_tag_1480_);
lean_inc_ref(v___x_1506_);
lean_inc(v_cls_1478_);
v_data_1508_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1508_, 0, v_cls_1478_);
lean_ctor_set(v_data_1508_, 1, v___x_1506_);
lean_ctor_set(v_data_1508_, 2, v_tag_1480_);
lean_ctor_set_float(v_data_1508_, sizeof(void*)*3, v___x_1507_);
lean_ctor_set_float(v_data_1508_, sizeof(void*)*3 + 8, v___x_1507_);
lean_ctor_set_uint8(v_data_1508_, sizeof(void*)*3 + 16, v_collapsed_1479_);
if (v___x_1500_ == 0)
{
lean_dec_ref_known(v___x_1506_, 1);
lean_dec(v_snd_1498_);
lean_dec(v_fst_1497_);
lean_dec_ref(v_tag_1480_);
lean_dec(v_cls_1478_);
v___y_1492_ = v_a_1503_;
v___y_1493_ = v___y_1502_;
v_data_1494_ = v_data_1508_;
goto v___jp_1491_;
}
else
{
lean_object* v_data_1509_; double v___x_1510_; double v___x_1511_; 
lean_dec_ref_known(v_data_1508_, 3);
v_data_1509_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1509_, 0, v_cls_1478_);
lean_ctor_set(v_data_1509_, 1, v___x_1506_);
lean_ctor_set(v_data_1509_, 2, v_tag_1480_);
v___x_1510_ = lean_unbox_float(v_fst_1497_);
lean_dec(v_fst_1497_);
lean_ctor_set_float(v_data_1509_, sizeof(void*)*3, v___x_1510_);
v___x_1511_ = lean_unbox_float(v_snd_1498_);
lean_dec(v_snd_1498_);
lean_ctor_set_float(v_data_1509_, sizeof(void*)*3 + 8, v___x_1511_);
lean_ctor_set_uint8(v_data_1509_, sizeof(void*)*3 + 16, v_collapsed_1479_);
v___y_1492_ = v_a_1503_;
v___y_1493_ = v___y_1502_;
v_data_1494_ = v_data_1509_;
goto v___jp_1491_;
}
}
v___jp_1512_:
{
lean_object* v_ref_1513_; lean_object* v___x_1514_; 
v_ref_1513_ = lean_ctor_get(v___y_1486_, 2);
lean_inc(v___y_1487_);
lean_inc_ref(v___y_1486_);
lean_inc(v_fst_1489_);
v___x_1514_ = lean_apply_4(v_msg_1484_, v_fst_1489_, v___y_1486_, v___y_1487_, lean_box(0));
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v_a_1515_; 
v_a_1515_ = lean_ctor_get(v___x_1514_, 0);
lean_inc(v_a_1515_);
lean_dec_ref_known(v___x_1514_, 1);
v___y_1502_ = v_ref_1513_;
v_a_1503_ = v_a_1515_;
goto v___jp_1501_;
}
else
{
lean_object* v___x_1516_; 
lean_dec_ref_known(v___x_1514_, 1);
v___x_1516_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2);
v___y_1502_ = v_ref_1513_;
v_a_1503_ = v___x_1516_;
goto v___jp_1501_;
}
}
v___jp_1517_:
{
if (v_clsEnabled_1482_ == 0)
{
if (v___y_1518_ == 0)
{
lean_object* v___x_1519_; lean_object* v_traceState_1520_; lean_object* v_env_1521_; lean_object* v_nextMacroScope_1522_; lean_object* v_ngen_1523_; lean_object* v_auxDeclNGen_1524_; lean_object* v_cache_1525_; lean_object* v_messages_1526_; lean_object* v_infoState_1527_; lean_object* v_snapshotTasks_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1547_; 
lean_dec(v_snd_1498_);
lean_dec(v_fst_1497_);
lean_dec_ref(v_msg_1484_);
lean_dec_ref(v_tag_1480_);
lean_dec(v_cls_1478_);
v___x_1519_ = lean_st_ref_take(v___y_1487_);
v_traceState_1520_ = lean_ctor_get(v___x_1519_, 4);
v_env_1521_ = lean_ctor_get(v___x_1519_, 0);
v_nextMacroScope_1522_ = lean_ctor_get(v___x_1519_, 1);
v_ngen_1523_ = lean_ctor_get(v___x_1519_, 2);
v_auxDeclNGen_1524_ = lean_ctor_get(v___x_1519_, 3);
v_cache_1525_ = lean_ctor_get(v___x_1519_, 5);
v_messages_1526_ = lean_ctor_get(v___x_1519_, 6);
v_infoState_1527_ = lean_ctor_get(v___x_1519_, 7);
v_snapshotTasks_1528_ = lean_ctor_get(v___x_1519_, 8);
v_isSharedCheck_1547_ = !lean_is_exclusive(v___x_1519_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1530_ = v___x_1519_;
v_isShared_1531_ = v_isSharedCheck_1547_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_snapshotTasks_1528_);
lean_inc(v_infoState_1527_);
lean_inc(v_messages_1526_);
lean_inc(v_cache_1525_);
lean_inc(v_traceState_1520_);
lean_inc(v_auxDeclNGen_1524_);
lean_inc(v_ngen_1523_);
lean_inc(v_nextMacroScope_1522_);
lean_inc(v_env_1521_);
lean_dec(v___x_1519_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1547_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
uint64_t v_tid_1532_; lean_object* v_traces_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1546_; 
v_tid_1532_ = lean_ctor_get_uint64(v_traceState_1520_, sizeof(void*)*1);
v_traces_1533_ = lean_ctor_get(v_traceState_1520_, 0);
v_isSharedCheck_1546_ = !lean_is_exclusive(v_traceState_1520_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1535_ = v_traceState_1520_;
v_isShared_1536_ = v_isSharedCheck_1546_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_traces_1533_);
lean_dec(v_traceState_1520_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1546_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v___x_1537_; lean_object* v___x_1539_; 
v___x_1537_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1483_, v_traces_1533_);
lean_dec_ref(v_traces_1533_);
if (v_isShared_1536_ == 0)
{
lean_ctor_set(v___x_1535_, 0, v___x_1537_);
v___x_1539_ = v___x_1535_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___x_1537_);
lean_ctor_set_uint64(v_reuseFailAlloc_1545_, sizeof(void*)*1, v_tid_1532_);
v___x_1539_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
lean_object* v___x_1541_; 
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 4, v___x_1539_);
v___x_1541_ = v___x_1530_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_env_1521_);
lean_ctor_set(v_reuseFailAlloc_1544_, 1, v_nextMacroScope_1522_);
lean_ctor_set(v_reuseFailAlloc_1544_, 2, v_ngen_1523_);
lean_ctor_set(v_reuseFailAlloc_1544_, 3, v_auxDeclNGen_1524_);
lean_ctor_set(v_reuseFailAlloc_1544_, 4, v___x_1539_);
lean_ctor_set(v_reuseFailAlloc_1544_, 5, v_cache_1525_);
lean_ctor_set(v_reuseFailAlloc_1544_, 6, v_messages_1526_);
lean_ctor_set(v_reuseFailAlloc_1544_, 7, v_infoState_1527_);
lean_ctor_set(v_reuseFailAlloc_1544_, 8, v_snapshotTasks_1528_);
v___x_1541_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1542_ = lean_st_ref_put(v___y_1487_, v___x_1541_);
v___x_1543_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5___redArg(v_fst_1489_);
return v___x_1543_;
}
}
}
}
}
else
{
goto v___jp_1512_;
}
}
else
{
goto v___jp_1512_;
}
}
v___jp_1548_:
{
double v___x_1550_; double v___x_1551_; double v___x_1552_; uint8_t v___x_1553_; 
v___x_1550_ = lean_unbox_float(v_snd_1498_);
v___x_1551_ = lean_unbox_float(v_fst_1497_);
v___x_1552_ = lean_float_sub(v___x_1550_, v___x_1551_);
v___x_1553_ = lean_float_decLt(v___y_1549_, v___x_1552_);
v___y_1518_ = v___x_1553_;
goto v___jp_1517_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2___boxed(lean_object* v_cls_1564_, lean_object* v_collapsed_1565_, lean_object* v_tag_1566_, lean_object* v_opts_1567_, lean_object* v_clsEnabled_1568_, lean_object* v_oldTraces_1569_, lean_object* v_msg_1570_, lean_object* v_resStartStop_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
uint8_t v_collapsed_boxed_1575_; uint8_t v_clsEnabled_boxed_1576_; lean_object* v_res_1577_; 
v_collapsed_boxed_1575_ = lean_unbox(v_collapsed_1565_);
v_clsEnabled_boxed_1576_ = lean_unbox(v_clsEnabled_1568_);
v_res_1577_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2(v_cls_1564_, v_collapsed_boxed_1575_, v_tag_1566_, v_opts_1567_, v_clsEnabled_boxed_1576_, v_oldTraces_1569_, v_msg_1570_, v_resStartStop_1571_, v___y_1572_, v___y_1573_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec_ref(v_opts_1567_);
return v_res_1577_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0_spec__0(lean_object* v_e_1578_){
_start:
{
if (lean_obj_tag(v_e_1578_) == 0)
{
uint8_t v___x_1579_; 
v___x_1579_ = 2;
return v___x_1579_;
}
else
{
uint8_t v___x_1580_; 
v___x_1580_ = 0;
return v___x_1580_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0_spec__0___boxed(lean_object* v_e_1581_){
_start:
{
uint8_t v_res_1582_; lean_object* v_r_1583_; 
v_res_1582_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0_spec__0(v_e_1581_);
lean_dec_ref(v_e_1581_);
v_r_1583_ = lean_box(v_res_1582_);
return v_r_1583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0(lean_object* v_cls_1584_, uint8_t v_collapsed_1585_, lean_object* v_tag_1586_, lean_object* v_opts_1587_, uint8_t v_clsEnabled_1588_, lean_object* v_oldTraces_1589_, lean_object* v_msg_1590_, lean_object* v_resStartStop_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_){
_start:
{
lean_object* v_fst_1595_; lean_object* v_snd_1596_; lean_object* v___y_1598_; lean_object* v___y_1599_; lean_object* v_data_1600_; lean_object* v_fst_1611_; lean_object* v_snd_1612_; lean_object* v___x_1613_; uint8_t v___x_1614_; lean_object* v___y_1616_; lean_object* v_a_1617_; uint8_t v___y_1632_; double v___y_1663_; 
v_fst_1595_ = lean_ctor_get(v_resStartStop_1591_, 0);
lean_inc(v_fst_1595_);
v_snd_1596_ = lean_ctor_get(v_resStartStop_1591_, 1);
lean_inc(v_snd_1596_);
lean_dec_ref(v_resStartStop_1591_);
v_fst_1611_ = lean_ctor_get(v_snd_1596_, 0);
lean_inc(v_fst_1611_);
v_snd_1612_ = lean_ctor_get(v_snd_1596_, 1);
lean_inc(v_snd_1612_);
lean_dec(v_snd_1596_);
v___x_1613_ = l_Lean_trace_profiler;
v___x_1614_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_opts_1587_, v___x_1613_);
if (v___x_1614_ == 0)
{
v___y_1632_ = v___x_1614_;
goto v___jp_1631_;
}
else
{
lean_object* v___x_1668_; uint8_t v___x_1669_; 
v___x_1668_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1669_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_opts_1587_, v___x_1668_);
if (v___x_1669_ == 0)
{
lean_object* v___x_1670_; lean_object* v___x_1671_; double v___x_1672_; double v___x_1673_; double v___x_1674_; 
v___x_1670_ = l_Lean_trace_profiler_threshold;
v___x_1671_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(v_opts_1587_, v___x_1670_);
v___x_1672_ = lean_float_of_nat(v___x_1671_);
v___x_1673_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3);
v___x_1674_ = lean_float_div(v___x_1672_, v___x_1673_);
v___y_1663_ = v___x_1674_;
goto v___jp_1662_;
}
else
{
lean_object* v___x_1675_; lean_object* v___x_1676_; double v___x_1677_; 
v___x_1675_ = l_Lean_trace_profiler_threshold;
v___x_1676_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(v_opts_1587_, v___x_1675_);
v___x_1677_ = lean_float_of_nat(v___x_1676_);
v___y_1663_ = v___x_1677_;
goto v___jp_1662_;
}
}
v___jp_1597_:
{
lean_object* v___x_1601_; 
lean_inc(v___y_1598_);
v___x_1601_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__4(v_oldTraces_1589_, v_data_1600_, v___y_1598_, v___y_1599_, v___y_1592_, v___y_1593_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v___x_1602_; 
lean_dec_ref_known(v___x_1601_, 1);
v___x_1602_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5___redArg(v_fst_1595_);
return v___x_1602_;
}
else
{
lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1610_; 
lean_dec(v_fst_1595_);
v_a_1603_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1605_ = v___x_1601_;
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_dec(v___x_1601_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1608_; 
if (v_isShared_1606_ == 0)
{
v___x_1608_ = v___x_1605_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_a_1603_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
v___jp_1615_:
{
uint8_t v_result_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; double v___x_1621_; lean_object* v_data_1622_; 
v_result_1618_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0_spec__0(v_fst_1595_);
v___x_1619_ = lean_box(v_result_1618_);
v___x_1620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1619_);
v___x_1621_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0);
lean_inc_ref(v_tag_1586_);
lean_inc_ref(v___x_1620_);
lean_inc(v_cls_1584_);
v_data_1622_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1622_, 0, v_cls_1584_);
lean_ctor_set(v_data_1622_, 1, v___x_1620_);
lean_ctor_set(v_data_1622_, 2, v_tag_1586_);
lean_ctor_set_float(v_data_1622_, sizeof(void*)*3, v___x_1621_);
lean_ctor_set_float(v_data_1622_, sizeof(void*)*3 + 8, v___x_1621_);
lean_ctor_set_uint8(v_data_1622_, sizeof(void*)*3 + 16, v_collapsed_1585_);
if (v___x_1614_ == 0)
{
lean_dec_ref_known(v___x_1620_, 1);
lean_dec(v_snd_1612_);
lean_dec(v_fst_1611_);
lean_dec_ref(v_tag_1586_);
lean_dec(v_cls_1584_);
v___y_1598_ = v___y_1616_;
v___y_1599_ = v_a_1617_;
v_data_1600_ = v_data_1622_;
goto v___jp_1597_;
}
else
{
lean_object* v_data_1623_; double v___x_1624_; double v___x_1625_; 
lean_dec_ref_known(v_data_1622_, 3);
v_data_1623_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1623_, 0, v_cls_1584_);
lean_ctor_set(v_data_1623_, 1, v___x_1620_);
lean_ctor_set(v_data_1623_, 2, v_tag_1586_);
v___x_1624_ = lean_unbox_float(v_fst_1611_);
lean_dec(v_fst_1611_);
lean_ctor_set_float(v_data_1623_, sizeof(void*)*3, v___x_1624_);
v___x_1625_ = lean_unbox_float(v_snd_1612_);
lean_dec(v_snd_1612_);
lean_ctor_set_float(v_data_1623_, sizeof(void*)*3 + 8, v___x_1625_);
lean_ctor_set_uint8(v_data_1623_, sizeof(void*)*3 + 16, v_collapsed_1585_);
v___y_1598_ = v___y_1616_;
v___y_1599_ = v_a_1617_;
v_data_1600_ = v_data_1623_;
goto v___jp_1597_;
}
}
v___jp_1626_:
{
lean_object* v_ref_1627_; lean_object* v___x_1628_; 
v_ref_1627_ = lean_ctor_get(v___y_1592_, 2);
lean_inc(v___y_1593_);
lean_inc_ref(v___y_1592_);
lean_inc(v_fst_1595_);
v___x_1628_ = lean_apply_4(v_msg_1590_, v_fst_1595_, v___y_1592_, v___y_1593_, lean_box(0));
if (lean_obj_tag(v___x_1628_) == 0)
{
lean_object* v_a_1629_; 
v_a_1629_ = lean_ctor_get(v___x_1628_, 0);
lean_inc(v_a_1629_);
lean_dec_ref_known(v___x_1628_, 1);
v___y_1616_ = v_ref_1627_;
v_a_1617_ = v_a_1629_;
goto v___jp_1615_;
}
else
{
lean_object* v___x_1630_; 
lean_dec_ref_known(v___x_1628_, 1);
v___x_1630_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2);
v___y_1616_ = v_ref_1627_;
v_a_1617_ = v___x_1630_;
goto v___jp_1615_;
}
}
v___jp_1631_:
{
if (v_clsEnabled_1588_ == 0)
{
if (v___y_1632_ == 0)
{
lean_object* v___x_1633_; lean_object* v_traceState_1634_; lean_object* v_env_1635_; lean_object* v_nextMacroScope_1636_; lean_object* v_ngen_1637_; lean_object* v_auxDeclNGen_1638_; lean_object* v_cache_1639_; lean_object* v_messages_1640_; lean_object* v_infoState_1641_; lean_object* v_snapshotTasks_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1661_; 
lean_dec(v_snd_1612_);
lean_dec(v_fst_1611_);
lean_dec_ref(v_msg_1590_);
lean_dec_ref(v_tag_1586_);
lean_dec(v_cls_1584_);
v___x_1633_ = lean_st_ref_take(v___y_1593_);
v_traceState_1634_ = lean_ctor_get(v___x_1633_, 4);
v_env_1635_ = lean_ctor_get(v___x_1633_, 0);
v_nextMacroScope_1636_ = lean_ctor_get(v___x_1633_, 1);
v_ngen_1637_ = lean_ctor_get(v___x_1633_, 2);
v_auxDeclNGen_1638_ = lean_ctor_get(v___x_1633_, 3);
v_cache_1639_ = lean_ctor_get(v___x_1633_, 5);
v_messages_1640_ = lean_ctor_get(v___x_1633_, 6);
v_infoState_1641_ = lean_ctor_get(v___x_1633_, 7);
v_snapshotTasks_1642_ = lean_ctor_get(v___x_1633_, 8);
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1644_ = v___x_1633_;
v_isShared_1645_ = v_isSharedCheck_1661_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_snapshotTasks_1642_);
lean_inc(v_infoState_1641_);
lean_inc(v_messages_1640_);
lean_inc(v_cache_1639_);
lean_inc(v_traceState_1634_);
lean_inc(v_auxDeclNGen_1638_);
lean_inc(v_ngen_1637_);
lean_inc(v_nextMacroScope_1636_);
lean_inc(v_env_1635_);
lean_dec(v___x_1633_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1661_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
uint64_t v_tid_1646_; lean_object* v_traces_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1660_; 
v_tid_1646_ = lean_ctor_get_uint64(v_traceState_1634_, sizeof(void*)*1);
v_traces_1647_ = lean_ctor_get(v_traceState_1634_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v_traceState_1634_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1649_ = v_traceState_1634_;
v_isShared_1650_ = v_isSharedCheck_1660_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_traces_1647_);
lean_dec(v_traceState_1634_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1660_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___x_1651_; lean_object* v___x_1653_; 
v___x_1651_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1589_, v_traces_1647_);
lean_dec_ref(v_traces_1647_);
if (v_isShared_1650_ == 0)
{
lean_ctor_set(v___x_1649_, 0, v___x_1651_);
v___x_1653_ = v___x_1649_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v___x_1651_);
lean_ctor_set_uint64(v_reuseFailAlloc_1659_, sizeof(void*)*1, v_tid_1646_);
v___x_1653_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
lean_object* v___x_1655_; 
if (v_isShared_1645_ == 0)
{
lean_ctor_set(v___x_1644_, 4, v___x_1653_);
v___x_1655_ = v___x_1644_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_env_1635_);
lean_ctor_set(v_reuseFailAlloc_1658_, 1, v_nextMacroScope_1636_);
lean_ctor_set(v_reuseFailAlloc_1658_, 2, v_ngen_1637_);
lean_ctor_set(v_reuseFailAlloc_1658_, 3, v_auxDeclNGen_1638_);
lean_ctor_set(v_reuseFailAlloc_1658_, 4, v___x_1653_);
lean_ctor_set(v_reuseFailAlloc_1658_, 5, v_cache_1639_);
lean_ctor_set(v_reuseFailAlloc_1658_, 6, v_messages_1640_);
lean_ctor_set(v_reuseFailAlloc_1658_, 7, v_infoState_1641_);
lean_ctor_set(v_reuseFailAlloc_1658_, 8, v_snapshotTasks_1642_);
v___x_1655_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
lean_object* v___x_1656_; lean_object* v___x_1657_; 
v___x_1656_ = lean_st_ref_put(v___y_1593_, v___x_1655_);
v___x_1657_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5___redArg(v_fst_1595_);
return v___x_1657_;
}
}
}
}
}
else
{
goto v___jp_1626_;
}
}
else
{
goto v___jp_1626_;
}
}
v___jp_1662_:
{
double v___x_1664_; double v___x_1665_; double v___x_1666_; uint8_t v___x_1667_; 
v___x_1664_ = lean_unbox_float(v_snd_1612_);
v___x_1665_ = lean_unbox_float(v_fst_1611_);
v___x_1666_ = lean_float_sub(v___x_1664_, v___x_1665_);
v___x_1667_ = lean_float_decLt(v___y_1663_, v___x_1666_);
v___y_1632_ = v___x_1667_;
goto v___jp_1631_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0___boxed(lean_object* v_cls_1678_, lean_object* v_collapsed_1679_, lean_object* v_tag_1680_, lean_object* v_opts_1681_, lean_object* v_clsEnabled_1682_, lean_object* v_oldTraces_1683_, lean_object* v_msg_1684_, lean_object* v_resStartStop_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_){
_start:
{
uint8_t v_collapsed_boxed_1689_; uint8_t v_clsEnabled_boxed_1690_; lean_object* v_res_1691_; 
v_collapsed_boxed_1689_ = lean_unbox(v_collapsed_1679_);
v_clsEnabled_boxed_1690_ = lean_unbox(v_clsEnabled_1682_);
v_res_1691_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0(v_cls_1678_, v_collapsed_boxed_1689_, v_tag_1680_, v_opts_1681_, v_clsEnabled_boxed_1690_, v_oldTraces_1683_, v_msg_1684_, v_resStartStop_1685_, v___y_1686_, v___y_1687_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
lean_dec_ref(v_opts_1681_);
return v_res_1691_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1_spec__2(lean_object* v_e_1692_){
_start:
{
if (lean_obj_tag(v_e_1692_) == 0)
{
uint8_t v___x_1693_; 
v___x_1693_ = 2;
return v___x_1693_;
}
else
{
uint8_t v___x_1694_; 
v___x_1694_ = 0;
return v___x_1694_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1_spec__2___boxed(lean_object* v_e_1695_){
_start:
{
uint8_t v_res_1696_; lean_object* v_r_1697_; 
v_res_1696_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1_spec__2(v_e_1695_);
lean_dec_ref(v_e_1695_);
v_r_1697_ = lean_box(v_res_1696_);
return v_r_1697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1(lean_object* v_cls_1698_, uint8_t v_collapsed_1699_, lean_object* v_tag_1700_, lean_object* v_opts_1701_, uint8_t v_clsEnabled_1702_, lean_object* v_oldTraces_1703_, lean_object* v_msg_1704_, lean_object* v_resStartStop_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_){
_start:
{
lean_object* v_fst_1709_; lean_object* v_snd_1710_; lean_object* v___y_1712_; lean_object* v___y_1713_; lean_object* v_data_1714_; lean_object* v_fst_1725_; lean_object* v_snd_1726_; lean_object* v___x_1727_; uint8_t v___x_1728_; lean_object* v___y_1730_; lean_object* v_a_1731_; uint8_t v___y_1746_; double v___y_1777_; 
v_fst_1709_ = lean_ctor_get(v_resStartStop_1705_, 0);
lean_inc(v_fst_1709_);
v_snd_1710_ = lean_ctor_get(v_resStartStop_1705_, 1);
lean_inc(v_snd_1710_);
lean_dec_ref(v_resStartStop_1705_);
v_fst_1725_ = lean_ctor_get(v_snd_1710_, 0);
lean_inc(v_fst_1725_);
v_snd_1726_ = lean_ctor_get(v_snd_1710_, 1);
lean_inc(v_snd_1726_);
lean_dec(v_snd_1710_);
v___x_1727_ = l_Lean_trace_profiler;
v___x_1728_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_opts_1701_, v___x_1727_);
if (v___x_1728_ == 0)
{
v___y_1746_ = v___x_1728_;
goto v___jp_1745_;
}
else
{
lean_object* v___x_1782_; uint8_t v___x_1783_; 
v___x_1782_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1783_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_opts_1701_, v___x_1782_);
if (v___x_1783_ == 0)
{
lean_object* v___x_1784_; lean_object* v___x_1785_; double v___x_1786_; double v___x_1787_; double v___x_1788_; 
v___x_1784_ = l_Lean_trace_profiler_threshold;
v___x_1785_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(v_opts_1701_, v___x_1784_);
v___x_1786_ = lean_float_of_nat(v___x_1785_);
v___x_1787_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3);
v___x_1788_ = lean_float_div(v___x_1786_, v___x_1787_);
v___y_1777_ = v___x_1788_;
goto v___jp_1776_;
}
else
{
lean_object* v___x_1789_; lean_object* v___x_1790_; double v___x_1791_; 
v___x_1789_ = l_Lean_trace_profiler_threshold;
v___x_1790_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(v_opts_1701_, v___x_1789_);
v___x_1791_ = lean_float_of_nat(v___x_1790_);
v___y_1777_ = v___x_1791_;
goto v___jp_1776_;
}
}
v___jp_1711_:
{
lean_object* v___x_1715_; 
lean_inc(v___y_1713_);
v___x_1715_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__4(v_oldTraces_1703_, v_data_1714_, v___y_1713_, v___y_1712_, v___y_1706_, v___y_1707_);
if (lean_obj_tag(v___x_1715_) == 0)
{
lean_object* v___x_1716_; 
lean_dec_ref_known(v___x_1715_, 1);
v___x_1716_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5___redArg(v_fst_1709_);
return v___x_1716_;
}
else
{
lean_object* v_a_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1724_; 
lean_dec(v_fst_1709_);
v_a_1717_ = lean_ctor_get(v___x_1715_, 0);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1715_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1719_ = v___x_1715_;
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_a_1717_);
lean_dec(v___x_1715_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1722_; 
if (v_isShared_1720_ == 0)
{
v___x_1722_ = v___x_1719_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_a_1717_);
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
v___jp_1729_:
{
uint8_t v_result_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; double v___x_1735_; lean_object* v_data_1736_; 
v_result_1732_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1_spec__2(v_fst_1709_);
v___x_1733_ = lean_box(v_result_1732_);
v___x_1734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1734_, 0, v___x_1733_);
v___x_1735_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0);
lean_inc_ref(v_tag_1700_);
lean_inc_ref(v___x_1734_);
lean_inc(v_cls_1698_);
v_data_1736_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1736_, 0, v_cls_1698_);
lean_ctor_set(v_data_1736_, 1, v___x_1734_);
lean_ctor_set(v_data_1736_, 2, v_tag_1700_);
lean_ctor_set_float(v_data_1736_, sizeof(void*)*3, v___x_1735_);
lean_ctor_set_float(v_data_1736_, sizeof(void*)*3 + 8, v___x_1735_);
lean_ctor_set_uint8(v_data_1736_, sizeof(void*)*3 + 16, v_collapsed_1699_);
if (v___x_1728_ == 0)
{
lean_dec_ref_known(v___x_1734_, 1);
lean_dec(v_snd_1726_);
lean_dec(v_fst_1725_);
lean_dec_ref(v_tag_1700_);
lean_dec(v_cls_1698_);
v___y_1712_ = v_a_1731_;
v___y_1713_ = v___y_1730_;
v_data_1714_ = v_data_1736_;
goto v___jp_1711_;
}
else
{
lean_object* v_data_1737_; double v___x_1738_; double v___x_1739_; 
lean_dec_ref_known(v_data_1736_, 3);
v_data_1737_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1737_, 0, v_cls_1698_);
lean_ctor_set(v_data_1737_, 1, v___x_1734_);
lean_ctor_set(v_data_1737_, 2, v_tag_1700_);
v___x_1738_ = lean_unbox_float(v_fst_1725_);
lean_dec(v_fst_1725_);
lean_ctor_set_float(v_data_1737_, sizeof(void*)*3, v___x_1738_);
v___x_1739_ = lean_unbox_float(v_snd_1726_);
lean_dec(v_snd_1726_);
lean_ctor_set_float(v_data_1737_, sizeof(void*)*3 + 8, v___x_1739_);
lean_ctor_set_uint8(v_data_1737_, sizeof(void*)*3 + 16, v_collapsed_1699_);
v___y_1712_ = v_a_1731_;
v___y_1713_ = v___y_1730_;
v_data_1714_ = v_data_1737_;
goto v___jp_1711_;
}
}
v___jp_1740_:
{
lean_object* v_ref_1741_; lean_object* v___x_1742_; 
v_ref_1741_ = lean_ctor_get(v___y_1706_, 2);
lean_inc(v___y_1707_);
lean_inc_ref(v___y_1706_);
lean_inc(v_fst_1709_);
v___x_1742_ = lean_apply_4(v_msg_1704_, v_fst_1709_, v___y_1706_, v___y_1707_, lean_box(0));
if (lean_obj_tag(v___x_1742_) == 0)
{
lean_object* v_a_1743_; 
v_a_1743_ = lean_ctor_get(v___x_1742_, 0);
lean_inc(v_a_1743_);
lean_dec_ref_known(v___x_1742_, 1);
v___y_1730_ = v_ref_1741_;
v_a_1731_ = v_a_1743_;
goto v___jp_1729_;
}
else
{
lean_object* v___x_1744_; 
lean_dec_ref_known(v___x_1742_, 1);
v___x_1744_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2);
v___y_1730_ = v_ref_1741_;
v_a_1731_ = v___x_1744_;
goto v___jp_1729_;
}
}
v___jp_1745_:
{
if (v_clsEnabled_1702_ == 0)
{
if (v___y_1746_ == 0)
{
lean_object* v___x_1747_; lean_object* v_traceState_1748_; lean_object* v_env_1749_; lean_object* v_nextMacroScope_1750_; lean_object* v_ngen_1751_; lean_object* v_auxDeclNGen_1752_; lean_object* v_cache_1753_; lean_object* v_messages_1754_; lean_object* v_infoState_1755_; lean_object* v_snapshotTasks_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1775_; 
lean_dec(v_snd_1726_);
lean_dec(v_fst_1725_);
lean_dec_ref(v_msg_1704_);
lean_dec_ref(v_tag_1700_);
lean_dec(v_cls_1698_);
v___x_1747_ = lean_st_ref_take(v___y_1707_);
v_traceState_1748_ = lean_ctor_get(v___x_1747_, 4);
v_env_1749_ = lean_ctor_get(v___x_1747_, 0);
v_nextMacroScope_1750_ = lean_ctor_get(v___x_1747_, 1);
v_ngen_1751_ = lean_ctor_get(v___x_1747_, 2);
v_auxDeclNGen_1752_ = lean_ctor_get(v___x_1747_, 3);
v_cache_1753_ = lean_ctor_get(v___x_1747_, 5);
v_messages_1754_ = lean_ctor_get(v___x_1747_, 6);
v_infoState_1755_ = lean_ctor_get(v___x_1747_, 7);
v_snapshotTasks_1756_ = lean_ctor_get(v___x_1747_, 8);
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1747_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1758_ = v___x_1747_;
v_isShared_1759_ = v_isSharedCheck_1775_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_snapshotTasks_1756_);
lean_inc(v_infoState_1755_);
lean_inc(v_messages_1754_);
lean_inc(v_cache_1753_);
lean_inc(v_traceState_1748_);
lean_inc(v_auxDeclNGen_1752_);
lean_inc(v_ngen_1751_);
lean_inc(v_nextMacroScope_1750_);
lean_inc(v_env_1749_);
lean_dec(v___x_1747_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1775_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
uint64_t v_tid_1760_; lean_object* v_traces_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1774_; 
v_tid_1760_ = lean_ctor_get_uint64(v_traceState_1748_, sizeof(void*)*1);
v_traces_1761_ = lean_ctor_get(v_traceState_1748_, 0);
v_isSharedCheck_1774_ = !lean_is_exclusive(v_traceState_1748_);
if (v_isSharedCheck_1774_ == 0)
{
v___x_1763_ = v_traceState_1748_;
v_isShared_1764_ = v_isSharedCheck_1774_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_traces_1761_);
lean_dec(v_traceState_1748_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1774_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1765_; lean_object* v___x_1767_; 
v___x_1765_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1703_, v_traces_1761_);
lean_dec_ref(v_traces_1761_);
if (v_isShared_1764_ == 0)
{
lean_ctor_set(v___x_1763_, 0, v___x_1765_);
v___x_1767_ = v___x_1763_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v___x_1765_);
lean_ctor_set_uint64(v_reuseFailAlloc_1773_, sizeof(void*)*1, v_tid_1760_);
v___x_1767_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
lean_object* v___x_1769_; 
if (v_isShared_1759_ == 0)
{
lean_ctor_set(v___x_1758_, 4, v___x_1767_);
v___x_1769_ = v___x_1758_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v_env_1749_);
lean_ctor_set(v_reuseFailAlloc_1772_, 1, v_nextMacroScope_1750_);
lean_ctor_set(v_reuseFailAlloc_1772_, 2, v_ngen_1751_);
lean_ctor_set(v_reuseFailAlloc_1772_, 3, v_auxDeclNGen_1752_);
lean_ctor_set(v_reuseFailAlloc_1772_, 4, v___x_1767_);
lean_ctor_set(v_reuseFailAlloc_1772_, 5, v_cache_1753_);
lean_ctor_set(v_reuseFailAlloc_1772_, 6, v_messages_1754_);
lean_ctor_set(v_reuseFailAlloc_1772_, 7, v_infoState_1755_);
lean_ctor_set(v_reuseFailAlloc_1772_, 8, v_snapshotTasks_1756_);
v___x_1769_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1770_ = lean_st_ref_put(v___y_1707_, v___x_1769_);
v___x_1771_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5___redArg(v_fst_1709_);
return v___x_1771_;
}
}
}
}
}
else
{
goto v___jp_1740_;
}
}
else
{
goto v___jp_1740_;
}
}
v___jp_1776_:
{
double v___x_1778_; double v___x_1779_; double v___x_1780_; uint8_t v___x_1781_; 
v___x_1778_ = lean_unbox_float(v_snd_1726_);
v___x_1779_ = lean_unbox_float(v_fst_1725_);
v___x_1780_ = lean_float_sub(v___x_1778_, v___x_1779_);
v___x_1781_ = lean_float_decLt(v___y_1777_, v___x_1780_);
v___y_1746_ = v___x_1781_;
goto v___jp_1745_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1___boxed(lean_object* v_cls_1792_, lean_object* v_collapsed_1793_, lean_object* v_tag_1794_, lean_object* v_opts_1795_, lean_object* v_clsEnabled_1796_, lean_object* v_oldTraces_1797_, lean_object* v_msg_1798_, lean_object* v_resStartStop_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_){
_start:
{
uint8_t v_collapsed_boxed_1803_; uint8_t v_clsEnabled_boxed_1804_; lean_object* v_res_1805_; 
v_collapsed_boxed_1803_ = lean_unbox(v_collapsed_1793_);
v_clsEnabled_boxed_1804_ = lean_unbox(v_clsEnabled_1796_);
v_res_1805_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1(v_cls_1792_, v_collapsed_boxed_1803_, v_tag_1794_, v_opts_1795_, v_clsEnabled_boxed_1804_, v_oldTraces_1797_, v_msg_1798_, v_resStartStop_1799_, v___y_1800_, v___y_1801_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
lean_dec_ref(v_opts_1795_);
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__4(lean_object* v___f_1806_, lean_object* v_lratPath_1807_, uint8_t v_trimProofs_1808_, lean_object* v___f_1809_, lean_object* v_solver_1810_, lean_object* v_timeout_1811_, uint8_t v_binaryProofs_1812_, uint8_t v_solverMode_1813_, lean_object* v___f_1814_, lean_object* v___f_1815_, lean_object* v_cnfHandle_1816_, lean_object* v_cnfPath_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_){
_start:
{
lean_object* v___y_1822_; lean_object* v_toCold_1840_; lean_object* v_options_1841_; lean_object* v_ref_1842_; lean_object* v_inheritedTraceOptions_1843_; uint8_t v_hasTrace_1844_; lean_object* v___x_1845_; uint8_t v___x_1846_; lean_object* v___x_1847_; lean_object* v___y_1849_; lean_object* v___y_1850_; lean_object* v___y_1851_; uint8_t v___y_1852_; lean_object* v_a_1853_; lean_object* v___y_1866_; lean_object* v___y_1867_; lean_object* v___y_1868_; uint8_t v___y_1869_; lean_object* v_a_1870_; lean_object* v___y_1880_; uint8_t v___y_1881_; lean_object* v___y_1923_; lean_object* v___y_1955_; lean_object* v___y_1956_; lean_object* v___y_1957_; uint8_t v___y_1958_; lean_object* v_a_1959_; lean_object* v___y_1972_; lean_object* v___y_1973_; uint8_t v___y_1974_; lean_object* v___y_1975_; lean_object* v_a_1976_; lean_object* v___y_1986_; uint8_t v___y_1987_; lean_object* v___y_2036_; 
v_toCold_1840_ = lean_ctor_get(v___y_1818_, 0);
v_options_1841_ = lean_ctor_get(v_toCold_1840_, 2);
v_ref_1842_ = lean_ctor_get(v___y_1818_, 2);
v_inheritedTraceOptions_1843_ = lean_ctor_get(v_toCold_1840_, 11);
v_hasTrace_1844_ = lean_ctor_get_uint8(v_options_1841_, sizeof(void*)*1);
v___x_1845_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__3));
v___x_1846_ = 1;
v___x_1847_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0___closed__0));
if (v_hasTrace_1844_ == 0)
{
lean_object* v___x_2045_; 
lean_dec_ref(v___f_1815_);
v___x_2045_ = l_IO_lazyPure___redArg(v___f_1814_);
if (lean_obj_tag(v___x_2045_) == 0)
{
lean_object* v_a_2046_; lean_object* v___x_2047_; 
v_a_2046_ = lean_ctor_get(v___x_2045_, 0);
lean_inc(v_a_2046_);
lean_dec_ref_known(v___x_2045_, 1);
v___x_2047_ = lean_io_prim_handle_put_str(v_cnfHandle_1816_, v_a_2046_);
lean_dec(v_a_2046_);
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_object* v___x_2048_; 
lean_dec_ref_known(v___x_2047_, 1);
v___x_2048_ = lean_io_prim_handle_flush(v_cnfHandle_1816_);
if (lean_obj_tag(v___x_2048_) == 0)
{
lean_dec_ref_known(v___x_2048_, 1);
goto v___jp_2028_;
}
else
{
lean_object* v_a_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2060_; 
lean_dec_ref(v_cnfPath_1817_);
lean_dec_ref(v_solver_1810_);
lean_dec_ref(v___f_1809_);
lean_dec_ref(v_lratPath_1807_);
lean_dec_ref(v___f_1806_);
v_a_2049_ = lean_ctor_get(v___x_2048_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2048_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2051_ = v___x_2048_;
v_isShared_2052_ = v_isSharedCheck_2060_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_a_2049_);
lean_dec(v___x_2048_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2060_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2058_; 
v___x_2053_ = lean_io_error_to_string(v_a_2049_);
v___x_2054_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2054_, 0, v___x_2053_);
v___x_2055_ = l_Lean_MessageData_ofFormat(v___x_2054_);
lean_inc(v_ref_1842_);
v___x_2056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2056_, 0, v_ref_1842_);
lean_ctor_set(v___x_2056_, 1, v___x_2055_);
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 0, v___x_2056_);
v___x_2058_ = v___x_2051_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v___x_2056_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
return v___x_2058_;
}
}
}
}
else
{
lean_object* v_a_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2072_; 
lean_dec_ref(v_cnfPath_1817_);
lean_dec_ref(v_solver_1810_);
lean_dec_ref(v___f_1809_);
lean_dec_ref(v_lratPath_1807_);
lean_dec_ref(v___f_1806_);
v_a_2061_ = lean_ctor_get(v___x_2047_, 0);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_2047_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2063_ = v___x_2047_;
v_isShared_2064_ = v_isSharedCheck_2072_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_a_2061_);
lean_dec(v___x_2047_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2072_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2070_; 
v___x_2065_ = lean_io_error_to_string(v_a_2061_);
v___x_2066_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2065_);
v___x_2067_ = l_Lean_MessageData_ofFormat(v___x_2066_);
lean_inc(v_ref_1842_);
v___x_2068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2068_, 0, v_ref_1842_);
lean_ctor_set(v___x_2068_, 1, v___x_2067_);
if (v_isShared_2064_ == 0)
{
lean_ctor_set(v___x_2063_, 0, v___x_2068_);
v___x_2070_ = v___x_2063_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v___x_2068_);
v___x_2070_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
return v___x_2070_;
}
}
}
}
else
{
lean_object* v_a_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2084_; 
lean_dec_ref(v_cnfPath_1817_);
lean_dec_ref(v_solver_1810_);
lean_dec_ref(v___f_1809_);
lean_dec_ref(v_lratPath_1807_);
lean_dec_ref(v___f_1806_);
v_a_2073_ = lean_ctor_get(v___x_2045_, 0);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2075_ = v___x_2045_;
v_isShared_2076_ = v_isSharedCheck_2084_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_a_2073_);
lean_dec(v___x_2045_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2084_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2082_; 
v___x_2077_ = lean_io_error_to_string(v_a_2073_);
v___x_2078_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2077_);
v___x_2079_ = l_Lean_MessageData_ofFormat(v___x_2078_);
lean_inc(v_ref_1842_);
v___x_2080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2080_, 0, v_ref_1842_);
lean_ctor_set(v___x_2080_, 1, v___x_2079_);
if (v_isShared_2076_ == 0)
{
lean_ctor_set(v___x_2075_, 0, v___x_2080_);
v___x_2082_ = v___x_2075_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v___x_2080_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
}
}
}
}
else
{
lean_object* v___x_2085_; uint8_t v___x_2086_; lean_object* v___y_2088_; lean_object* v___y_2089_; lean_object* v_a_2090_; lean_object* v___y_2103_; lean_object* v___y_2104_; lean_object* v_a_2105_; lean_object* v___y_2108_; lean_object* v___y_2109_; lean_object* v_a_2110_; lean_object* v___y_2120_; lean_object* v___y_2121_; lean_object* v_a_2122_; 
v___x_2085_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6);
v___x_2086_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1843_, v_options_1841_, v___x_2085_);
if (v___x_2086_ == 0)
{
lean_object* v___x_2221_; uint8_t v___x_2222_; 
v___x_2221_ = l_Lean_trace_profiler;
v___x_2222_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_options_1841_, v___x_2221_);
if (v___x_2222_ == 0)
{
lean_object* v___x_2223_; 
lean_dec_ref(v___f_1815_);
v___x_2223_ = l_IO_lazyPure___redArg(v___f_1814_);
if (lean_obj_tag(v___x_2223_) == 0)
{
lean_object* v_a_2224_; lean_object* v___x_2225_; 
v_a_2224_ = lean_ctor_get(v___x_2223_, 0);
lean_inc(v_a_2224_);
lean_dec_ref_known(v___x_2223_, 1);
v___x_2225_ = lean_io_prim_handle_put_str(v_cnfHandle_1816_, v_a_2224_);
lean_dec(v_a_2224_);
if (lean_obj_tag(v___x_2225_) == 0)
{
lean_object* v___x_2226_; 
lean_dec_ref_known(v___x_2225_, 1);
v___x_2226_ = lean_io_prim_handle_flush(v_cnfHandle_1816_);
if (lean_obj_tag(v___x_2226_) == 0)
{
lean_dec_ref_known(v___x_2226_, 1);
goto v___jp_2028_;
}
else
{
lean_object* v_a_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2238_; 
lean_dec_ref(v_cnfPath_1817_);
lean_dec_ref(v_solver_1810_);
lean_dec_ref(v___f_1809_);
lean_dec_ref(v_lratPath_1807_);
lean_dec_ref(v___f_1806_);
v_a_2227_ = lean_ctor_get(v___x_2226_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2226_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2229_ = v___x_2226_;
v_isShared_2230_ = v_isSharedCheck_2238_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_a_2227_);
lean_dec(v___x_2226_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2238_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2236_; 
v___x_2231_ = lean_io_error_to_string(v_a_2227_);
v___x_2232_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2232_, 0, v___x_2231_);
v___x_2233_ = l_Lean_MessageData_ofFormat(v___x_2232_);
lean_inc(v_ref_1842_);
v___x_2234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2234_, 0, v_ref_1842_);
lean_ctor_set(v___x_2234_, 1, v___x_2233_);
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 0, v___x_2234_);
v___x_2236_ = v___x_2229_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v___x_2234_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
}
}
else
{
lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2250_; 
lean_dec_ref(v_cnfPath_1817_);
lean_dec_ref(v_solver_1810_);
lean_dec_ref(v___f_1809_);
lean_dec_ref(v_lratPath_1807_);
lean_dec_ref(v___f_1806_);
v_a_2239_ = lean_ctor_get(v___x_2225_, 0);
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2225_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2241_ = v___x_2225_;
v_isShared_2242_ = v_isSharedCheck_2250_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___x_2225_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2250_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2248_; 
v___x_2243_ = lean_io_error_to_string(v_a_2239_);
v___x_2244_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2243_);
v___x_2245_ = l_Lean_MessageData_ofFormat(v___x_2244_);
lean_inc(v_ref_1842_);
v___x_2246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2246_, 0, v_ref_1842_);
lean_ctor_set(v___x_2246_, 1, v___x_2245_);
if (v_isShared_2242_ == 0)
{
lean_ctor_set(v___x_2241_, 0, v___x_2246_);
v___x_2248_ = v___x_2241_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v___x_2246_);
v___x_2248_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
return v___x_2248_;
}
}
}
}
else
{
lean_object* v_a_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2262_; 
lean_dec_ref(v_cnfPath_1817_);
lean_dec_ref(v_solver_1810_);
lean_dec_ref(v___f_1809_);
lean_dec_ref(v_lratPath_1807_);
lean_dec_ref(v___f_1806_);
v_a_2251_ = lean_ctor_get(v___x_2223_, 0);
v_isSharedCheck_2262_ = !lean_is_exclusive(v___x_2223_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2253_ = v___x_2223_;
v_isShared_2254_ = v_isSharedCheck_2262_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_a_2251_);
lean_dec(v___x_2223_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2262_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2260_; 
v___x_2255_ = lean_io_error_to_string(v_a_2251_);
v___x_2256_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2256_, 0, v___x_2255_);
v___x_2257_ = l_Lean_MessageData_ofFormat(v___x_2256_);
lean_inc(v_ref_1842_);
v___x_2258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2258_, 0, v_ref_1842_);
lean_ctor_set(v___x_2258_, 1, v___x_2257_);
if (v_isShared_2254_ == 0)
{
lean_ctor_set(v___x_2253_, 0, v___x_2258_);
v___x_2260_ = v___x_2253_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v___x_2258_);
v___x_2260_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
return v___x_2260_;
}
}
}
}
else
{
goto v___jp_2124_;
}
}
else
{
goto v___jp_2124_;
}
v___jp_2087_:
{
lean_object* v___x_2091_; double v___x_2092_; double v___x_2093_; double v___x_2094_; double v___x_2095_; double v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2091_ = lean_io_mono_nanos_now();
v___x_2092_ = lean_float_of_nat(v___y_2089_);
v___x_2093_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9);
v___x_2094_ = lean_float_div(v___x_2092_, v___x_2093_);
v___x_2095_ = lean_float_of_nat(v___x_2091_);
v___x_2096_ = lean_float_div(v___x_2095_, v___x_2093_);
v___x_2097_ = lean_box_float(v___x_2094_);
v___x_2098_ = lean_box_float(v___x_2096_);
v___x_2099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2099_, 0, v___x_2097_);
lean_ctor_set(v___x_2099_, 1, v___x_2098_);
v___x_2100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2100_, 0, v_a_2090_);
lean_ctor_set(v___x_2100_, 1, v___x_2099_);
v___x_2101_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2(v___x_1845_, v___x_1846_, v___x_1847_, v_options_1841_, v___x_2086_, v___y_2088_, v___f_1815_, v___x_2100_, v___y_1818_, v___y_1819_);
v___y_2036_ = v___x_2101_;
goto v___jp_2035_;
}
v___jp_2102_:
{
lean_object* v___x_2106_; 
v___x_2106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2106_, 0, v_a_2105_);
v___y_2088_ = v___y_2103_;
v___y_2089_ = v___y_2104_;
v_a_2090_ = v___x_2106_;
goto v___jp_2087_;
}
v___jp_2107_:
{
lean_object* v___x_2111_; double v___x_2112_; double v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2111_ = lean_io_get_num_heartbeats();
v___x_2112_ = lean_float_of_nat(v___y_2108_);
v___x_2113_ = lean_float_of_nat(v___x_2111_);
v___x_2114_ = lean_box_float(v___x_2112_);
v___x_2115_ = lean_box_float(v___x_2113_);
v___x_2116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2114_);
lean_ctor_set(v___x_2116_, 1, v___x_2115_);
v___x_2117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2117_, 0, v_a_2110_);
lean_ctor_set(v___x_2117_, 1, v___x_2116_);
v___x_2118_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2(v___x_1845_, v___x_1846_, v___x_1847_, v_options_1841_, v___x_2086_, v___y_2109_, v___f_1815_, v___x_2117_, v___y_1818_, v___y_1819_);
v___y_2036_ = v___x_2118_;
goto v___jp_2035_;
}
v___jp_2119_:
{
lean_object* v___x_2123_; 
v___x_2123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2123_, 0, v_a_2122_);
v___y_2108_ = v___y_2120_;
v___y_2109_ = v___y_2121_;
v_a_2110_ = v___x_2123_;
goto v___jp_2107_;
}
v___jp_2124_:
{
lean_object* v___x_2125_; lean_object* v_a_2126_; lean_object* v___x_2127_; uint8_t v___x_2128_; 
v___x_2125_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg(v___y_1819_);
v_a_2126_ = lean_ctor_get(v___x_2125_, 0);
lean_inc(v_a_2126_);
lean_dec_ref(v___x_2125_);
v___x_2127_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2128_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_options_1841_, v___x_2127_);
if (v___x_2128_ == 0)
{
lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___x_2129_ = lean_io_mono_nanos_now();
v___x_2130_ = l_IO_lazyPure___redArg(v___f_1814_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v_a_2131_; lean_object* v___x_2132_; 
v_a_2131_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_a_2131_);
lean_dec_ref_known(v___x_2130_, 1);
v___x_2132_ = lean_io_prim_handle_put_str(v_cnfHandle_1816_, v_a_2131_);
lean_dec(v_a_2131_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v___x_2133_; 
lean_dec_ref_known(v___x_2132_, 1);
v___x_2133_ = lean_io_prim_handle_flush(v_cnfHandle_1816_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2141_; 
v_a_2134_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2136_ = v___x_2133_;
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___x_2133_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2139_; 
if (v_isShared_2137_ == 0)
{
lean_ctor_set_tag(v___x_2136_, 1);
v___x_2139_ = v___x_2136_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_a_2134_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
v___y_2088_ = v_a_2126_;
v___y_2089_ = v___x_2129_;
v_a_2090_ = v___x_2139_;
goto v___jp_2087_;
}
}
}
else
{
lean_object* v_a_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2152_; 
v_a_2142_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2152_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2144_ = v___x_2133_;
v_isShared_2145_ = v_isSharedCheck_2152_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_a_2142_);
lean_dec(v___x_2133_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2152_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2146_; lean_object* v___x_2148_; 
v___x_2146_ = lean_io_error_to_string(v_a_2142_);
if (v_isShared_2145_ == 0)
{
lean_ctor_set_tag(v___x_2144_, 3);
lean_ctor_set(v___x_2144_, 0, v___x_2146_);
v___x_2148_ = v___x_2144_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v___x_2146_);
v___x_2148_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
lean_object* v___x_2149_; lean_object* v___x_2150_; 
v___x_2149_ = l_Lean_MessageData_ofFormat(v___x_2148_);
lean_inc(v_ref_1842_);
v___x_2150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2150_, 0, v_ref_1842_);
lean_ctor_set(v___x_2150_, 1, v___x_2149_);
v___y_2103_ = v_a_2126_;
v___y_2104_ = v___x_2129_;
v_a_2105_ = v___x_2150_;
goto v___jp_2102_;
}
}
}
}
else
{
lean_object* v_a_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2163_; 
v_a_2153_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2155_ = v___x_2132_;
v_isShared_2156_ = v_isSharedCheck_2163_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_a_2153_);
lean_dec(v___x_2132_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2163_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2157_; lean_object* v___x_2159_; 
v___x_2157_ = lean_io_error_to_string(v_a_2153_);
if (v_isShared_2156_ == 0)
{
lean_ctor_set_tag(v___x_2155_, 3);
lean_ctor_set(v___x_2155_, 0, v___x_2157_);
v___x_2159_ = v___x_2155_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v___x_2157_);
v___x_2159_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
lean_object* v___x_2160_; lean_object* v___x_2161_; 
v___x_2160_ = l_Lean_MessageData_ofFormat(v___x_2159_);
lean_inc(v_ref_1842_);
v___x_2161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2161_, 0, v_ref_1842_);
lean_ctor_set(v___x_2161_, 1, v___x_2160_);
v___y_2103_ = v_a_2126_;
v___y_2104_ = v___x_2129_;
v_a_2105_ = v___x_2161_;
goto v___jp_2102_;
}
}
}
}
else
{
lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2174_; 
v_a_2164_ = lean_ctor_get(v___x_2130_, 0);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2166_ = v___x_2130_;
v_isShared_2167_ = v_isSharedCheck_2174_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_dec(v___x_2130_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2174_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2168_; lean_object* v___x_2170_; 
v___x_2168_ = lean_io_error_to_string(v_a_2164_);
if (v_isShared_2167_ == 0)
{
lean_ctor_set_tag(v___x_2166_, 3);
lean_ctor_set(v___x_2166_, 0, v___x_2168_);
v___x_2170_ = v___x_2166_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v___x_2168_);
v___x_2170_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2171_ = l_Lean_MessageData_ofFormat(v___x_2170_);
lean_inc(v_ref_1842_);
v___x_2172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2172_, 0, v_ref_1842_);
lean_ctor_set(v___x_2172_, 1, v___x_2171_);
v___y_2103_ = v_a_2126_;
v___y_2104_ = v___x_2129_;
v_a_2105_ = v___x_2172_;
goto v___jp_2102_;
}
}
}
}
else
{
lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2175_ = lean_io_get_num_heartbeats();
v___x_2176_ = l_IO_lazyPure___redArg(v___f_1814_);
if (lean_obj_tag(v___x_2176_) == 0)
{
lean_object* v_a_2177_; lean_object* v___x_2178_; 
v_a_2177_ = lean_ctor_get(v___x_2176_, 0);
lean_inc(v_a_2177_);
lean_dec_ref_known(v___x_2176_, 1);
v___x_2178_ = lean_io_prim_handle_put_str(v_cnfHandle_1816_, v_a_2177_);
lean_dec(v_a_2177_);
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_object* v___x_2179_; 
lean_dec_ref_known(v___x_2178_, 1);
v___x_2179_ = lean_io_prim_handle_flush(v_cnfHandle_1816_);
if (lean_obj_tag(v___x_2179_) == 0)
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2187_; 
v_a_2180_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2182_ = v___x_2179_;
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___x_2179_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2185_; 
if (v_isShared_2183_ == 0)
{
lean_ctor_set_tag(v___x_2182_, 1);
v___x_2185_ = v___x_2182_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_a_2180_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
v___y_2108_ = v___x_2175_;
v___y_2109_ = v_a_2126_;
v_a_2110_ = v___x_2185_;
goto v___jp_2107_;
}
}
}
else
{
lean_object* v_a_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2198_; 
v_a_2188_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2198_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2190_ = v___x_2179_;
v_isShared_2191_ = v_isSharedCheck_2198_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_a_2188_);
lean_dec(v___x_2179_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2198_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v___x_2192_; lean_object* v___x_2194_; 
v___x_2192_ = lean_io_error_to_string(v_a_2188_);
if (v_isShared_2191_ == 0)
{
lean_ctor_set_tag(v___x_2190_, 3);
lean_ctor_set(v___x_2190_, 0, v___x_2192_);
v___x_2194_ = v___x_2190_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v___x_2192_);
v___x_2194_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; 
v___x_2195_ = l_Lean_MessageData_ofFormat(v___x_2194_);
lean_inc(v_ref_1842_);
v___x_2196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2196_, 0, v_ref_1842_);
lean_ctor_set(v___x_2196_, 1, v___x_2195_);
v___y_2120_ = v___x_2175_;
v___y_2121_ = v_a_2126_;
v_a_2122_ = v___x_2196_;
goto v___jp_2119_;
}
}
}
}
else
{
lean_object* v_a_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2209_; 
v_a_2199_ = lean_ctor_get(v___x_2178_, 0);
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_2178_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2201_ = v___x_2178_;
v_isShared_2202_ = v_isSharedCheck_2209_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_a_2199_);
lean_dec(v___x_2178_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2209_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v___x_2203_; lean_object* v___x_2205_; 
v___x_2203_ = lean_io_error_to_string(v_a_2199_);
if (v_isShared_2202_ == 0)
{
lean_ctor_set_tag(v___x_2201_, 3);
lean_ctor_set(v___x_2201_, 0, v___x_2203_);
v___x_2205_ = v___x_2201_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v___x_2203_);
v___x_2205_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; 
v___x_2206_ = l_Lean_MessageData_ofFormat(v___x_2205_);
lean_inc(v_ref_1842_);
v___x_2207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2207_, 0, v_ref_1842_);
lean_ctor_set(v___x_2207_, 1, v___x_2206_);
v___y_2120_ = v___x_2175_;
v___y_2121_ = v_a_2126_;
v_a_2122_ = v___x_2207_;
goto v___jp_2119_;
}
}
}
}
else
{
lean_object* v_a_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2220_; 
v_a_2210_ = lean_ctor_get(v___x_2176_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2176_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2212_ = v___x_2176_;
v_isShared_2213_ = v_isSharedCheck_2220_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_a_2210_);
lean_dec(v___x_2176_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2220_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
lean_object* v___x_2214_; lean_object* v___x_2216_; 
v___x_2214_ = lean_io_error_to_string(v_a_2210_);
if (v_isShared_2213_ == 0)
{
lean_ctor_set_tag(v___x_2212_, 3);
lean_ctor_set(v___x_2212_, 0, v___x_2214_);
v___x_2216_ = v___x_2212_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v___x_2214_);
v___x_2216_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
lean_object* v___x_2217_; lean_object* v___x_2218_; 
v___x_2217_ = l_Lean_MessageData_ofFormat(v___x_2216_);
lean_inc(v_ref_1842_);
v___x_2218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2218_, 0, v_ref_1842_);
lean_ctor_set(v___x_2218_, 1, v___x_2217_);
v___y_2120_ = v___x_2175_;
v___y_2121_ = v_a_2126_;
v_a_2122_ = v___x_2218_;
goto v___jp_2119_;
}
}
}
}
}
}
v___jp_1821_:
{
if (lean_obj_tag(v___y_1822_) == 0)
{
lean_object* v_a_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1831_; 
v_a_1823_ = lean_ctor_get(v___y_1822_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___y_1822_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1825_ = v___y_1822_;
v_isShared_1826_ = v_isSharedCheck_1831_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_a_1823_);
lean_dec(v___y_1822_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1831_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v___x_1827_; lean_object* v___x_1829_; 
v___x_1827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1827_, 0, v_a_1823_);
if (v_isShared_1826_ == 0)
{
lean_ctor_set(v___x_1825_, 0, v___x_1827_);
v___x_1829_ = v___x_1825_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v___x_1827_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
}
else
{
lean_object* v_a_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1839_; 
v_a_1832_ = lean_ctor_get(v___y_1822_, 0);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___y_1822_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1834_ = v___y_1822_;
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_a_1832_);
lean_dec(v___y_1822_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1837_; 
if (v_isShared_1835_ == 0)
{
v___x_1837_ = v___x_1834_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_a_1832_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
}
}
v___jp_1848_:
{
lean_object* v___x_1854_; double v___x_1855_; double v___x_1856_; double v___x_1857_; double v___x_1858_; double v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; 
v___x_1854_ = lean_io_mono_nanos_now();
v___x_1855_ = lean_float_of_nat(v___y_1850_);
v___x_1856_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9);
v___x_1857_ = lean_float_div(v___x_1855_, v___x_1856_);
v___x_1858_ = lean_float_of_nat(v___x_1854_);
v___x_1859_ = lean_float_div(v___x_1858_, v___x_1856_);
v___x_1860_ = lean_box_float(v___x_1857_);
v___x_1861_ = lean_box_float(v___x_1859_);
v___x_1862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1860_);
lean_ctor_set(v___x_1862_, 1, v___x_1861_);
v___x_1863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1863_, 0, v_a_1853_);
lean_ctor_set(v___x_1863_, 1, v___x_1862_);
v___x_1864_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0(v___x_1845_, v___x_1846_, v___x_1847_, v___y_1851_, v___y_1852_, v___y_1849_, v___f_1806_, v___x_1863_, v___y_1818_, v___y_1819_);
v___y_1822_ = v___x_1864_;
goto v___jp_1821_;
}
v___jp_1865_:
{
lean_object* v___x_1871_; double v___x_1872_; double v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1871_ = lean_io_get_num_heartbeats();
v___x_1872_ = lean_float_of_nat(v___y_1867_);
v___x_1873_ = lean_float_of_nat(v___x_1871_);
v___x_1874_ = lean_box_float(v___x_1872_);
v___x_1875_ = lean_box_float(v___x_1873_);
v___x_1876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1874_);
lean_ctor_set(v___x_1876_, 1, v___x_1875_);
v___x_1877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1877_, 0, v_a_1870_);
lean_ctor_set(v___x_1877_, 1, v___x_1876_);
v___x_1878_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0(v___x_1845_, v___x_1846_, v___x_1847_, v___y_1868_, v___y_1869_, v___y_1866_, v___f_1806_, v___x_1877_, v___y_1818_, v___y_1819_);
v___y_1822_ = v___x_1878_;
goto v___jp_1821_;
}
v___jp_1879_:
{
lean_object* v___x_1882_; lean_object* v_a_1883_; lean_object* v___x_1884_; uint8_t v___x_1885_; 
v___x_1882_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg(v___y_1819_);
v_a_1883_ = lean_ctor_get(v___x_1882_, 0);
lean_inc(v_a_1883_);
lean_dec_ref(v___x_1882_);
v___x_1884_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1885_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v___y_1880_, v___x_1884_);
if (v___x_1885_ == 0)
{
lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1886_ = lean_io_mono_nanos_now();
v___x_1887_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_1807_, v_trimProofs_1808_, v___y_1818_, v___y_1819_);
lean_dec_ref(v_lratPath_1807_);
if (lean_obj_tag(v___x_1887_) == 0)
{
lean_object* v_a_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1895_; 
v_a_1888_ = lean_ctor_get(v___x_1887_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1887_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1890_ = v___x_1887_;
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_a_1888_);
lean_dec(v___x_1887_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1893_; 
if (v_isShared_1891_ == 0)
{
lean_ctor_set_tag(v___x_1890_, 1);
v___x_1893_ = v___x_1890_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_a_1888_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
v___y_1849_ = v_a_1883_;
v___y_1850_ = v___x_1886_;
v___y_1851_ = v___y_1880_;
v___y_1852_ = v___y_1881_;
v_a_1853_ = v___x_1893_;
goto v___jp_1848_;
}
}
}
else
{
lean_object* v_a_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1903_; 
v_a_1896_ = lean_ctor_get(v___x_1887_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v___x_1887_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1898_ = v___x_1887_;
v_isShared_1899_ = v_isSharedCheck_1903_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_a_1896_);
lean_dec(v___x_1887_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1903_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v___x_1901_; 
if (v_isShared_1899_ == 0)
{
lean_ctor_set_tag(v___x_1898_, 0);
v___x_1901_ = v___x_1898_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_a_1896_);
v___x_1901_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
v___y_1849_ = v_a_1883_;
v___y_1850_ = v___x_1886_;
v___y_1851_ = v___y_1880_;
v___y_1852_ = v___y_1881_;
v_a_1853_ = v___x_1901_;
goto v___jp_1848_;
}
}
}
}
else
{
lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1904_ = lean_io_get_num_heartbeats();
v___x_1905_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_1807_, v_trimProofs_1808_, v___y_1818_, v___y_1819_);
lean_dec_ref(v_lratPath_1807_);
if (lean_obj_tag(v___x_1905_) == 0)
{
lean_object* v_a_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1913_; 
v_a_1906_ = lean_ctor_get(v___x_1905_, 0);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1908_ = v___x_1905_;
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_a_1906_);
lean_dec(v___x_1905_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___x_1911_; 
if (v_isShared_1909_ == 0)
{
lean_ctor_set_tag(v___x_1908_, 1);
v___x_1911_ = v___x_1908_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_a_1906_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
v___y_1866_ = v_a_1883_;
v___y_1867_ = v___x_1904_;
v___y_1868_ = v___y_1880_;
v___y_1869_ = v___y_1881_;
v_a_1870_ = v___x_1911_;
goto v___jp_1865_;
}
}
}
else
{
lean_object* v_a_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1921_; 
v_a_1914_ = lean_ctor_get(v___x_1905_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1916_ = v___x_1905_;
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_a_1914_);
lean_dec(v___x_1905_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1919_; 
if (v_isShared_1917_ == 0)
{
lean_ctor_set_tag(v___x_1916_, 0);
v___x_1919_ = v___x_1916_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_a_1914_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
v___y_1866_ = v_a_1883_;
v___y_1867_ = v___x_1904_;
v___y_1868_ = v___y_1880_;
v___y_1869_ = v___y_1881_;
v_a_1870_ = v___x_1919_;
goto v___jp_1865_;
}
}
}
}
}
v___jp_1922_:
{
if (lean_obj_tag(v___y_1923_) == 0)
{
lean_object* v_a_1924_; lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1945_; 
v_a_1924_ = lean_ctor_get(v___y_1923_, 0);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___y_1923_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1926_ = v___y_1923_;
v_isShared_1927_ = v_isSharedCheck_1945_;
goto v_resetjp_1925_;
}
else
{
lean_inc(v_a_1924_);
lean_dec(v___y_1923_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1945_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
if (lean_obj_tag(v_a_1924_) == 0)
{
lean_object* v_assignment_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1938_; 
lean_dec_ref(v_lratPath_1807_);
lean_dec_ref(v___f_1806_);
v_assignment_1928_ = lean_ctor_get(v_a_1924_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v_a_1924_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1930_ = v_a_1924_;
v_isShared_1931_ = v_isSharedCheck_1938_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_assignment_1928_);
lean_dec(v_a_1924_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1938_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1933_; 
if (v_isShared_1931_ == 0)
{
v___x_1933_ = v___x_1930_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_assignment_1928_);
v___x_1933_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
lean_object* v___x_1935_; 
if (v_isShared_1927_ == 0)
{
lean_ctor_set(v___x_1926_, 0, v___x_1933_);
v___x_1935_ = v___x_1926_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v___x_1933_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
}
else
{
lean_del_object(v___x_1926_);
lean_dec(v_a_1924_);
if (v_hasTrace_1844_ == 0)
{
lean_object* v___x_1939_; 
lean_dec_ref(v___f_1806_);
v___x_1939_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_1807_, v_trimProofs_1808_, v___y_1818_, v___y_1819_);
lean_dec_ref(v_lratPath_1807_);
v___y_1822_ = v___x_1939_;
goto v___jp_1821_;
}
else
{
lean_object* v___x_1940_; uint8_t v___x_1941_; 
v___x_1940_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6);
v___x_1941_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1843_, v_options_1841_, v___x_1940_);
if (v___x_1941_ == 0)
{
lean_object* v___x_1942_; uint8_t v___x_1943_; 
v___x_1942_ = l_Lean_trace_profiler;
v___x_1943_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_options_1841_, v___x_1942_);
if (v___x_1943_ == 0)
{
lean_object* v___x_1944_; 
lean_dec_ref(v___f_1806_);
v___x_1944_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_1807_, v_trimProofs_1808_, v___y_1818_, v___y_1819_);
lean_dec_ref(v_lratPath_1807_);
v___y_1822_ = v___x_1944_;
goto v___jp_1821_;
}
else
{
v___y_1880_ = v_options_1841_;
v___y_1881_ = v___x_1941_;
goto v___jp_1879_;
}
}
else
{
v___y_1880_ = v_options_1841_;
v___y_1881_ = v___x_1941_;
goto v___jp_1879_;
}
}
}
}
}
else
{
lean_object* v_a_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1953_; 
lean_dec_ref(v_lratPath_1807_);
lean_dec_ref(v___f_1806_);
v_a_1946_ = lean_ctor_get(v___y_1923_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___y_1923_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1948_ = v___y_1923_;
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_a_1946_);
lean_dec(v___y_1923_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1951_; 
if (v_isShared_1949_ == 0)
{
v___x_1951_ = v___x_1948_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_a_1946_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
return v___x_1951_;
}
}
}
}
v___jp_1954_:
{
lean_object* v___x_1960_; double v___x_1961_; double v___x_1962_; double v___x_1963_; double v___x_1964_; double v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; 
v___x_1960_ = lean_io_mono_nanos_now();
v___x_1961_ = lean_float_of_nat(v___y_1956_);
v___x_1962_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9);
v___x_1963_ = lean_float_div(v___x_1961_, v___x_1962_);
v___x_1964_ = lean_float_of_nat(v___x_1960_);
v___x_1965_ = lean_float_div(v___x_1964_, v___x_1962_);
v___x_1966_ = lean_box_float(v___x_1963_);
v___x_1967_ = lean_box_float(v___x_1965_);
v___x_1968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1968_, 0, v___x_1966_);
lean_ctor_set(v___x_1968_, 1, v___x_1967_);
v___x_1969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1969_, 0, v_a_1959_);
lean_ctor_set(v___x_1969_, 1, v___x_1968_);
v___x_1970_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1(v___x_1845_, v___x_1846_, v___x_1847_, v___y_1957_, v___y_1958_, v___y_1955_, v___f_1809_, v___x_1969_, v___y_1818_, v___y_1819_);
v___y_1923_ = v___x_1970_;
goto v___jp_1922_;
}
v___jp_1971_:
{
lean_object* v___x_1977_; double v___x_1978_; double v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; 
v___x_1977_ = lean_io_get_num_heartbeats();
v___x_1978_ = lean_float_of_nat(v___y_1975_);
v___x_1979_ = lean_float_of_nat(v___x_1977_);
v___x_1980_ = lean_box_float(v___x_1978_);
v___x_1981_ = lean_box_float(v___x_1979_);
v___x_1982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1980_);
lean_ctor_set(v___x_1982_, 1, v___x_1981_);
v___x_1983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1983_, 0, v_a_1976_);
lean_ctor_set(v___x_1983_, 1, v___x_1982_);
v___x_1984_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1(v___x_1845_, v___x_1846_, v___x_1847_, v___y_1973_, v___y_1974_, v___y_1972_, v___f_1809_, v___x_1983_, v___y_1818_, v___y_1819_);
v___y_1923_ = v___x_1984_;
goto v___jp_1922_;
}
v___jp_1985_:
{
lean_object* v___x_1988_; lean_object* v_a_1989_; lean_object* v___x_1990_; uint8_t v___x_1991_; 
v___x_1988_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg(v___y_1819_);
v_a_1989_ = lean_ctor_get(v___x_1988_, 0);
lean_inc(v_a_1989_);
lean_dec_ref(v___x_1988_);
v___x_1990_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1991_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v___y_1986_, v___x_1990_);
if (v___x_1991_ == 0)
{
lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___x_1992_ = lean_io_mono_nanos_now();
lean_inc_ref(v_lratPath_1807_);
v___x_1993_ = l_Lean_Meta_Tactic_BVDecide_External_satQuery(v_solver_1810_, v_cnfPath_1817_, v_lratPath_1807_, v_timeout_1811_, v_binaryProofs_1812_, v_solverMode_1813_, v___y_1818_, v___y_1819_);
if (lean_obj_tag(v___x_1993_) == 0)
{
lean_object* v_a_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2001_; 
v_a_1994_ = lean_ctor_get(v___x_1993_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1996_ = v___x_1993_;
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_a_1994_);
lean_dec(v___x_1993_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1999_; 
if (v_isShared_1997_ == 0)
{
lean_ctor_set_tag(v___x_1996_, 1);
v___x_1999_ = v___x_1996_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_a_1994_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
v___y_1955_ = v_a_1989_;
v___y_1956_ = v___x_1992_;
v___y_1957_ = v___y_1986_;
v___y_1958_ = v___y_1987_;
v_a_1959_ = v___x_1999_;
goto v___jp_1954_;
}
}
}
else
{
lean_object* v_a_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2009_; 
v_a_2002_ = lean_ctor_get(v___x_1993_, 0);
v_isSharedCheck_2009_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_2004_ = v___x_1993_;
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_a_2002_);
lean_dec(v___x_1993_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v___x_2007_; 
if (v_isShared_2005_ == 0)
{
lean_ctor_set_tag(v___x_2004_, 0);
v___x_2007_ = v___x_2004_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_a_2002_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
v___y_1955_ = v_a_1989_;
v___y_1956_ = v___x_1992_;
v___y_1957_ = v___y_1986_;
v___y_1958_ = v___y_1987_;
v_a_1959_ = v___x_2007_;
goto v___jp_1954_;
}
}
}
}
else
{
lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_2010_ = lean_io_get_num_heartbeats();
lean_inc_ref(v_lratPath_1807_);
v___x_2011_ = l_Lean_Meta_Tactic_BVDecide_External_satQuery(v_solver_1810_, v_cnfPath_1817_, v_lratPath_1807_, v_timeout_1811_, v_binaryProofs_1812_, v_solverMode_1813_, v___y_1818_, v___y_1819_);
if (lean_obj_tag(v___x_2011_) == 0)
{
lean_object* v_a_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2019_; 
v_a_2012_ = lean_ctor_get(v___x_2011_, 0);
v_isSharedCheck_2019_ = !lean_is_exclusive(v___x_2011_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_2014_ = v___x_2011_;
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_a_2012_);
lean_dec(v___x_2011_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2017_; 
if (v_isShared_2015_ == 0)
{
lean_ctor_set_tag(v___x_2014_, 1);
v___x_2017_ = v___x_2014_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_a_2012_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
v___y_1972_ = v_a_1989_;
v___y_1973_ = v___y_1986_;
v___y_1974_ = v___y_1987_;
v___y_1975_ = v___x_2010_;
v_a_1976_ = v___x_2017_;
goto v___jp_1971_;
}
}
}
else
{
lean_object* v_a_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2027_; 
v_a_2020_ = lean_ctor_get(v___x_2011_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_2011_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2022_ = v___x_2011_;
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_a_2020_);
lean_dec(v___x_2011_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2025_; 
if (v_isShared_2023_ == 0)
{
lean_ctor_set_tag(v___x_2022_, 0);
v___x_2025_ = v___x_2022_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_a_2020_);
v___x_2025_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
v___y_1972_ = v_a_1989_;
v___y_1973_ = v___y_1986_;
v___y_1974_ = v___y_1987_;
v___y_1975_ = v___x_2010_;
v_a_1976_ = v___x_2025_;
goto v___jp_1971_;
}
}
}
}
}
v___jp_2028_:
{
if (v_hasTrace_1844_ == 0)
{
lean_object* v___x_2029_; 
lean_dec_ref(v___f_1809_);
lean_inc_ref(v_lratPath_1807_);
v___x_2029_ = l_Lean_Meta_Tactic_BVDecide_External_satQuery(v_solver_1810_, v_cnfPath_1817_, v_lratPath_1807_, v_timeout_1811_, v_binaryProofs_1812_, v_solverMode_1813_, v___y_1818_, v___y_1819_);
v___y_1923_ = v___x_2029_;
goto v___jp_1922_;
}
else
{
lean_object* v___x_2030_; uint8_t v___x_2031_; 
v___x_2030_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6);
v___x_2031_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1843_, v_options_1841_, v___x_2030_);
if (v___x_2031_ == 0)
{
lean_object* v___x_2032_; uint8_t v___x_2033_; 
v___x_2032_ = l_Lean_trace_profiler;
v___x_2033_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_options_1841_, v___x_2032_);
if (v___x_2033_ == 0)
{
lean_object* v___x_2034_; 
lean_dec_ref(v___f_1809_);
lean_inc_ref(v_lratPath_1807_);
v___x_2034_ = l_Lean_Meta_Tactic_BVDecide_External_satQuery(v_solver_1810_, v_cnfPath_1817_, v_lratPath_1807_, v_timeout_1811_, v_binaryProofs_1812_, v_solverMode_1813_, v___y_1818_, v___y_1819_);
v___y_1923_ = v___x_2034_;
goto v___jp_1922_;
}
else
{
v___y_1986_ = v_options_1841_;
v___y_1987_ = v___x_2031_;
goto v___jp_1985_;
}
}
else
{
v___y_1986_ = v_options_1841_;
v___y_1987_ = v___x_2031_;
goto v___jp_1985_;
}
}
}
v___jp_2035_:
{
if (lean_obj_tag(v___y_2036_) == 0)
{
lean_dec_ref_known(v___y_2036_, 1);
goto v___jp_2028_;
}
else
{
lean_object* v_a_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2044_; 
lean_dec_ref(v_cnfPath_1817_);
lean_dec_ref(v_solver_1810_);
lean_dec_ref(v___f_1809_);
lean_dec_ref(v_lratPath_1807_);
lean_dec_ref(v___f_1806_);
v_a_2037_ = lean_ctor_get(v___y_2036_, 0);
v_isSharedCheck_2044_ = !lean_is_exclusive(v___y_2036_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2039_ = v___y_2036_;
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_a_2037_);
lean_dec(v___y_2036_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2042_; 
if (v_isShared_2040_ == 0)
{
v___x_2042_ = v___x_2039_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v_a_2037_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__4___boxed(lean_object* v___f_2263_, lean_object* v_lratPath_2264_, lean_object* v_trimProofs_2265_, lean_object* v___f_2266_, lean_object* v_solver_2267_, lean_object* v_timeout_2268_, lean_object* v_binaryProofs_2269_, lean_object* v_solverMode_2270_, lean_object* v___f_2271_, lean_object* v___f_2272_, lean_object* v_cnfHandle_2273_, lean_object* v_cnfPath_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_){
_start:
{
uint8_t v_trimProofs_boxed_2278_; uint8_t v_binaryProofs_boxed_2279_; uint8_t v_solverMode_boxed_2280_; lean_object* v_res_2281_; 
v_trimProofs_boxed_2278_ = lean_unbox(v_trimProofs_2265_);
v_binaryProofs_boxed_2279_ = lean_unbox(v_binaryProofs_2269_);
v_solverMode_boxed_2280_ = lean_unbox(v_solverMode_2270_);
v_res_2281_ = l_Lean_Meta_Tactic_BVDecide_runExternal___lam__4(v___f_2263_, v_lratPath_2264_, v_trimProofs_boxed_2278_, v___f_2266_, v_solver_2267_, v_timeout_2268_, v_binaryProofs_boxed_2279_, v_solverMode_boxed_2280_, v___f_2271_, v___f_2272_, v_cnfHandle_2273_, v_cnfPath_2274_, v___y_2275_, v___y_2276_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v_cnfHandle_2273_);
lean_dec(v_timeout_2268_);
return v_res_2281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal(lean_object* v_cnf_2285_, lean_object* v_solver_2286_, lean_object* v_lratPath_2287_, uint8_t v_trimProofs_2288_, lean_object* v_timeout_2289_, uint8_t v_binaryProofs_2290_, uint8_t v_solverMode_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_){
_start:
{
lean_object* v___f_2295_; lean_object* v___f_2296_; lean_object* v___f_2297_; lean_object* v___f_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___f_2302_; lean_object* v___x_2303_; 
v___f_2295_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_runExternal___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2295_, 0, v_cnf_2285_);
v___f_2296_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_runExternal___closed__0));
v___f_2297_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_runExternal___closed__1));
v___f_2298_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_runExternal___closed__2));
v___x_2299_ = lean_box(v_trimProofs_2288_);
v___x_2300_ = lean_box(v_binaryProofs_2290_);
v___x_2301_ = lean_box(v_solverMode_2291_);
v___f_2302_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_runExternal___lam__4___boxed), 15, 10);
lean_closure_set(v___f_2302_, 0, v___f_2297_);
lean_closure_set(v___f_2302_, 1, v_lratPath_2287_);
lean_closure_set(v___f_2302_, 2, v___x_2299_);
lean_closure_set(v___f_2302_, 3, v___f_2296_);
lean_closure_set(v___f_2302_, 4, v_solver_2286_);
lean_closure_set(v___f_2302_, 5, v_timeout_2289_);
lean_closure_set(v___f_2302_, 6, v___x_2300_);
lean_closure_set(v___f_2302_, 7, v___x_2301_);
lean_closure_set(v___f_2302_, 8, v___f_2295_);
lean_closure_set(v___f_2302_, 9, v___f_2298_);
v___x_2303_ = l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg(v___f_2302_, v_a_2292_, v_a_2293_);
return v___x_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___boxed(lean_object* v_cnf_2304_, lean_object* v_solver_2305_, lean_object* v_lratPath_2306_, lean_object* v_trimProofs_2307_, lean_object* v_timeout_2308_, lean_object* v_binaryProofs_2309_, lean_object* v_solverMode_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_){
_start:
{
uint8_t v_trimProofs_boxed_2314_; uint8_t v_binaryProofs_boxed_2315_; uint8_t v_solverMode_boxed_2316_; lean_object* v_res_2317_; 
v_trimProofs_boxed_2314_ = lean_unbox(v_trimProofs_2307_);
v_binaryProofs_boxed_2315_ = lean_unbox(v_binaryProofs_2309_);
v_solverMode_boxed_2316_ = lean_unbox(v_solverMode_2310_);
v_res_2317_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_cnf_2304_, v_solver_2305_, v_lratPath_2306_, v_trimProofs_boxed_2314_, v_timeout_2308_, v_binaryProofs_boxed_2315_, v_solverMode_boxed_2316_, v_a_2311_, v_a_2312_);
lean_dec(v_a_2312_);
lean_dec_ref(v_a_2311_);
return v_res_2317_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Checker(uint8_t builtin);
lean_object* runtime_initialize_Lean_CoreM(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_LRAT_Trim(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Parser(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_External(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_LRAT_Cert(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
