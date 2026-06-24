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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__6(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__6___boxed(lean_object*);
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
v___x_449_ = lean_alloc_ctor(0, 10, 0);
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
lean_object* v___x_467_; lean_object* v_env_468_; lean_object* v_options_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_467_ = lean_st_ref_get(v___y_465_);
v_env_468_ = lean_ctor_get(v___x_467_, 0);
lean_inc_ref(v_env_468_);
lean_dec(v___x_467_);
v_options_469_ = lean_ctor_get(v___y_464_, 2);
v___x_470_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__2);
v___x_471_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_469_);
v___x_472_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_472_, 0, v_env_468_);
lean_ctor_set(v___x_472_, 1, v___x_470_);
lean_ctor_set(v___x_472_, 2, v___x_471_);
lean_ctor_set(v___x_472_, 3, v_options_469_);
v___x_473_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_473_, 0, v___x_472_);
lean_ctor_set(v___x_473_, 1, v_msgData_463_);
v___x_474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___boxed(lean_object* v_msgData_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0(v_msgData_475_, v___y_476_, v___y_477_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__4(lean_object* v_oldTraces_480_, lean_object* v_data_481_, lean_object* v_ref_482_, lean_object* v_msg_483_, lean_object* v___y_484_, lean_object* v___y_485_){
_start:
{
lean_object* v_fileName_487_; lean_object* v_fileMap_488_; lean_object* v_options_489_; lean_object* v_currRecDepth_490_; lean_object* v_maxRecDepth_491_; lean_object* v_ref_492_; lean_object* v_currNamespace_493_; lean_object* v_openDecls_494_; lean_object* v_initHeartbeats_495_; lean_object* v_maxHeartbeats_496_; lean_object* v_quotContext_497_; lean_object* v_currMacroScope_498_; uint8_t v_diag_499_; lean_object* v_cancelTk_x3f_500_; uint8_t v_suppressElabErrors_501_; lean_object* v_inheritedTraceOptions_502_; lean_object* v___x_503_; lean_object* v_traceState_504_; lean_object* v_traces_505_; lean_object* v_ref_506_; lean_object* v___x_507_; lean_object* v___x_508_; size_t v_sz_509_; size_t v___x_510_; lean_object* v___x_511_; lean_object* v_msg_512_; lean_object* v___x_513_; lean_object* v_a_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_551_; 
v_fileName_487_ = lean_ctor_get(v___y_484_, 0);
v_fileMap_488_ = lean_ctor_get(v___y_484_, 1);
v_options_489_ = lean_ctor_get(v___y_484_, 2);
v_currRecDepth_490_ = lean_ctor_get(v___y_484_, 3);
v_maxRecDepth_491_ = lean_ctor_get(v___y_484_, 4);
v_ref_492_ = lean_ctor_get(v___y_484_, 5);
v_currNamespace_493_ = lean_ctor_get(v___y_484_, 6);
v_openDecls_494_ = lean_ctor_get(v___y_484_, 7);
v_initHeartbeats_495_ = lean_ctor_get(v___y_484_, 8);
v_maxHeartbeats_496_ = lean_ctor_get(v___y_484_, 9);
v_quotContext_497_ = lean_ctor_get(v___y_484_, 10);
v_currMacroScope_498_ = lean_ctor_get(v___y_484_, 11);
v_diag_499_ = lean_ctor_get_uint8(v___y_484_, sizeof(void*)*14);
v_cancelTk_x3f_500_ = lean_ctor_get(v___y_484_, 12);
v_suppressElabErrors_501_ = lean_ctor_get_uint8(v___y_484_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_502_ = lean_ctor_get(v___y_484_, 13);
v___x_503_ = lean_st_ref_get(v___y_485_);
v_traceState_504_ = lean_ctor_get(v___x_503_, 4);
lean_inc_ref(v_traceState_504_);
lean_dec(v___x_503_);
v_traces_505_ = lean_ctor_get(v_traceState_504_, 0);
lean_inc_ref(v_traces_505_);
lean_dec_ref(v_traceState_504_);
v_ref_506_ = l_Lean_replaceRef(v_ref_482_, v_ref_492_);
lean_inc_ref(v_inheritedTraceOptions_502_);
lean_inc(v_cancelTk_x3f_500_);
lean_inc(v_currMacroScope_498_);
lean_inc(v_quotContext_497_);
lean_inc(v_maxHeartbeats_496_);
lean_inc(v_initHeartbeats_495_);
lean_inc(v_openDecls_494_);
lean_inc(v_currNamespace_493_);
lean_inc(v_maxRecDepth_491_);
lean_inc(v_currRecDepth_490_);
lean_inc_ref(v_options_489_);
lean_inc_ref(v_fileMap_488_);
lean_inc_ref(v_fileName_487_);
v___x_507_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_507_, 0, v_fileName_487_);
lean_ctor_set(v___x_507_, 1, v_fileMap_488_);
lean_ctor_set(v___x_507_, 2, v_options_489_);
lean_ctor_set(v___x_507_, 3, v_currRecDepth_490_);
lean_ctor_set(v___x_507_, 4, v_maxRecDepth_491_);
lean_ctor_set(v___x_507_, 5, v_ref_506_);
lean_ctor_set(v___x_507_, 6, v_currNamespace_493_);
lean_ctor_set(v___x_507_, 7, v_openDecls_494_);
lean_ctor_set(v___x_507_, 8, v_initHeartbeats_495_);
lean_ctor_set(v___x_507_, 9, v_maxHeartbeats_496_);
lean_ctor_set(v___x_507_, 10, v_quotContext_497_);
lean_ctor_set(v___x_507_, 11, v_currMacroScope_498_);
lean_ctor_set(v___x_507_, 12, v_cancelTk_x3f_500_);
lean_ctor_set(v___x_507_, 13, v_inheritedTraceOptions_502_);
lean_ctor_set_uint8(v___x_507_, sizeof(void*)*14, v_diag_499_);
lean_ctor_set_uint8(v___x_507_, sizeof(void*)*14 + 1, v_suppressElabErrors_501_);
v___x_508_ = l_Lean_PersistentArray_toArray___redArg(v_traces_505_);
lean_dec_ref(v_traces_505_);
v_sz_509_ = lean_array_size(v___x_508_);
v___x_510_ = ((size_t)0ULL);
v___x_511_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__4_spec__6(v_sz_509_, v___x_510_, v___x_508_);
v_msg_512_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_512_, 0, v_data_481_);
lean_ctor_set(v_msg_512_, 1, v_msg_483_);
lean_ctor_set(v_msg_512_, 2, v___x_511_);
v___x_513_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0(v_msg_512_, v___x_507_, v___y_485_);
lean_dec_ref_known(v___x_507_, 14);
v_a_514_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_551_ == 0)
{
v___x_516_ = v___x_513_;
v_isShared_517_ = v_isSharedCheck_551_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_a_514_);
lean_dec(v___x_513_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_551_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_518_; lean_object* v_traceState_519_; lean_object* v_env_520_; lean_object* v_nextMacroScope_521_; lean_object* v_ngen_522_; lean_object* v_auxDeclNGen_523_; lean_object* v_cache_524_; lean_object* v_messages_525_; lean_object* v_infoState_526_; lean_object* v_snapshotTasks_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_550_; 
v___x_518_ = lean_st_ref_take(v___y_485_);
v_traceState_519_ = lean_ctor_get(v___x_518_, 4);
v_env_520_ = lean_ctor_get(v___x_518_, 0);
v_nextMacroScope_521_ = lean_ctor_get(v___x_518_, 1);
v_ngen_522_ = lean_ctor_get(v___x_518_, 2);
v_auxDeclNGen_523_ = lean_ctor_get(v___x_518_, 3);
v_cache_524_ = lean_ctor_get(v___x_518_, 5);
v_messages_525_ = lean_ctor_get(v___x_518_, 6);
v_infoState_526_ = lean_ctor_get(v___x_518_, 7);
v_snapshotTasks_527_ = lean_ctor_get(v___x_518_, 8);
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_550_ == 0)
{
v___x_529_ = v___x_518_;
v_isShared_530_ = v_isSharedCheck_550_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_snapshotTasks_527_);
lean_inc(v_infoState_526_);
lean_inc(v_messages_525_);
lean_inc(v_cache_524_);
lean_inc(v_traceState_519_);
lean_inc(v_auxDeclNGen_523_);
lean_inc(v_ngen_522_);
lean_inc(v_nextMacroScope_521_);
lean_inc(v_env_520_);
lean_dec(v___x_518_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_550_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
uint64_t v_tid_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_548_; 
v_tid_531_ = lean_ctor_get_uint64(v_traceState_519_, sizeof(void*)*1);
v_isSharedCheck_548_ = !lean_is_exclusive(v_traceState_519_);
if (v_isSharedCheck_548_ == 0)
{
lean_object* v_unused_549_; 
v_unused_549_ = lean_ctor_get(v_traceState_519_, 0);
lean_dec(v_unused_549_);
v___x_533_ = v_traceState_519_;
v_isShared_534_ = v_isSharedCheck_548_;
goto v_resetjp_532_;
}
else
{
lean_dec(v_traceState_519_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_548_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_538_; 
v___x_535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_535_, 0, v_ref_482_);
lean_ctor_set(v___x_535_, 1, v_a_514_);
v___x_536_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_480_, v___x_535_);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 0, v___x_536_);
v___x_538_ = v___x_533_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v___x_536_);
lean_ctor_set_uint64(v_reuseFailAlloc_547_, sizeof(void*)*1, v_tid_531_);
v___x_538_ = v_reuseFailAlloc_547_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
lean_object* v___x_540_; 
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 4, v___x_538_);
v___x_540_ = v___x_529_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_env_520_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v_nextMacroScope_521_);
lean_ctor_set(v_reuseFailAlloc_546_, 2, v_ngen_522_);
lean_ctor_set(v_reuseFailAlloc_546_, 3, v_auxDeclNGen_523_);
lean_ctor_set(v_reuseFailAlloc_546_, 4, v___x_538_);
lean_ctor_set(v_reuseFailAlloc_546_, 5, v_cache_524_);
lean_ctor_set(v_reuseFailAlloc_546_, 6, v_messages_525_);
lean_ctor_set(v_reuseFailAlloc_546_, 7, v_infoState_526_);
lean_ctor_set(v_reuseFailAlloc_546_, 8, v_snapshotTasks_527_);
v___x_540_ = v_reuseFailAlloc_546_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_544_; 
v___x_541_ = lean_st_ref_set(v___y_485_, v___x_540_);
v___x_542_ = lean_box(0);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 0, v___x_542_);
v___x_544_ = v___x_516_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 1, 0);
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__4___boxed(lean_object* v_oldTraces_552_, lean_object* v_data_553_, lean_object* v_ref_554_, lean_object* v_msg_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__4(v_oldTraces_552_, v_data_553_, v_ref_554_, v_msg_555_, v___y_556_, v___y_557_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(lean_object* v_opts_560_, lean_object* v_opt_561_){
_start:
{
lean_object* v_name_562_; lean_object* v_defValue_563_; lean_object* v_map_564_; lean_object* v___x_565_; 
v_name_562_ = lean_ctor_get(v_opt_561_, 0);
v_defValue_563_ = lean_ctor_get(v_opt_561_, 1);
v_map_564_ = lean_ctor_get(v_opts_560_, 0);
v___x_565_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_564_, v_name_562_);
if (lean_obj_tag(v___x_565_) == 0)
{
lean_inc(v_defValue_563_);
return v_defValue_563_;
}
else
{
lean_object* v_val_566_; 
v_val_566_ = lean_ctor_get(v___x_565_, 0);
lean_inc(v_val_566_);
lean_dec_ref_known(v___x_565_, 1);
if (lean_obj_tag(v_val_566_) == 3)
{
lean_object* v_v_567_; 
v_v_567_ = lean_ctor_get(v_val_566_, 0);
lean_inc(v_v_567_);
lean_dec_ref_known(v_val_566_, 1);
return v_v_567_;
}
else
{
lean_dec(v_val_566_);
lean_inc(v_defValue_563_);
return v_defValue_563_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7___boxed(lean_object* v_opts_568_, lean_object* v_opt_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(v_opts_568_, v_opt_569_);
lean_dec_ref(v_opt_569_);
lean_dec_ref(v_opts_568_);
return v_res_570_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__6(lean_object* v_e_571_){
_start:
{
if (lean_obj_tag(v_e_571_) == 0)
{
uint8_t v___x_572_; 
v___x_572_ = 2;
return v___x_572_;
}
else
{
uint8_t v___x_573_; 
v___x_573_ = 0;
return v___x_573_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__6___boxed(lean_object* v_e_574_){
_start:
{
uint8_t v_res_575_; lean_object* v_r_576_; 
v_res_575_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__6(v_e_574_);
lean_dec_ref(v_e_574_);
v_r_576_ = lean_box(v_res_575_);
return v_r_576_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0(void){
_start:
{
lean_object* v___x_577_; double v___x_578_; 
v___x_577_ = lean_unsigned_to_nat(0u);
v___x_578_ = lean_float_of_nat(v___x_577_);
return v___x_578_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2(void){
_start:
{
lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_580_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__1));
v___x_581_ = l_Lean_stringToMessageData(v___x_580_);
return v___x_581_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3(void){
_start:
{
lean_object* v___x_582_; double v___x_583_; 
v___x_582_ = lean_unsigned_to_nat(1000u);
v___x_583_ = lean_float_of_nat(v___x_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3(lean_object* v_cls_584_, uint8_t v_collapsed_585_, lean_object* v_tag_586_, lean_object* v_opts_587_, uint8_t v_clsEnabled_588_, lean_object* v_oldTraces_589_, lean_object* v_msg_590_, lean_object* v_resStartStop_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
lean_object* v_fst_595_; lean_object* v_snd_596_; lean_object* v___y_598_; lean_object* v___y_599_; lean_object* v_data_600_; lean_object* v_fst_611_; lean_object* v_snd_612_; lean_object* v___x_613_; uint8_t v___x_614_; lean_object* v___y_616_; lean_object* v_a_617_; uint8_t v___y_632_; double v___y_663_; 
v_fst_595_ = lean_ctor_get(v_resStartStop_591_, 0);
lean_inc(v_fst_595_);
v_snd_596_ = lean_ctor_get(v_resStartStop_591_, 1);
lean_inc(v_snd_596_);
lean_dec_ref(v_resStartStop_591_);
v_fst_611_ = lean_ctor_get(v_snd_596_, 0);
lean_inc(v_fst_611_);
v_snd_612_ = lean_ctor_get(v_snd_596_, 1);
lean_inc(v_snd_612_);
lean_dec(v_snd_596_);
v___x_613_ = l_Lean_trace_profiler;
v___x_614_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_opts_587_, v___x_613_);
if (v___x_614_ == 0)
{
v___y_632_ = v___x_614_;
goto v___jp_631_;
}
else
{
lean_object* v___x_668_; uint8_t v___x_669_; 
v___x_668_ = l_Lean_trace_profiler_useHeartbeats;
v___x_669_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_opts_587_, v___x_668_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; lean_object* v___x_671_; double v___x_672_; double v___x_673_; double v___x_674_; 
v___x_670_ = l_Lean_trace_profiler_threshold;
v___x_671_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(v_opts_587_, v___x_670_);
v___x_672_ = lean_float_of_nat(v___x_671_);
v___x_673_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3);
v___x_674_ = lean_float_div(v___x_672_, v___x_673_);
v___y_663_ = v___x_674_;
goto v___jp_662_;
}
else
{
lean_object* v___x_675_; lean_object* v___x_676_; double v___x_677_; 
v___x_675_ = l_Lean_trace_profiler_threshold;
v___x_676_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(v_opts_587_, v___x_675_);
v___x_677_ = lean_float_of_nat(v___x_676_);
v___y_663_ = v___x_677_;
goto v___jp_662_;
}
}
v___jp_597_:
{
lean_object* v___x_601_; 
lean_inc(v___y_598_);
v___x_601_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__4(v_oldTraces_589_, v_data_600_, v___y_598_, v___y_599_, v___y_592_, v___y_593_);
if (lean_obj_tag(v___x_601_) == 0)
{
lean_object* v___x_602_; 
lean_dec_ref_known(v___x_601_, 1);
v___x_602_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5___redArg(v_fst_595_);
return v___x_602_;
}
else
{
lean_object* v_a_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_610_; 
lean_dec(v_fst_595_);
v_a_603_ = lean_ctor_get(v___x_601_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_610_ == 0)
{
v___x_605_ = v___x_601_;
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_a_603_);
lean_dec(v___x_601_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_608_; 
if (v_isShared_606_ == 0)
{
v___x_608_ = v___x_605_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_a_603_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
}
v___jp_615_:
{
uint8_t v_result_618_; lean_object* v___x_619_; lean_object* v___x_620_; double v___x_621_; lean_object* v_data_622_; 
v_result_618_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__6(v_fst_595_);
v___x_619_ = lean_box(v_result_618_);
v___x_620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_620_, 0, v___x_619_);
v___x_621_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0);
lean_inc_ref(v_tag_586_);
lean_inc_ref(v___x_620_);
lean_inc(v_cls_584_);
v_data_622_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_622_, 0, v_cls_584_);
lean_ctor_set(v_data_622_, 1, v___x_620_);
lean_ctor_set(v_data_622_, 2, v_tag_586_);
lean_ctor_set_float(v_data_622_, sizeof(void*)*3, v___x_621_);
lean_ctor_set_float(v_data_622_, sizeof(void*)*3 + 8, v___x_621_);
lean_ctor_set_uint8(v_data_622_, sizeof(void*)*3 + 16, v_collapsed_585_);
if (v___x_614_ == 0)
{
lean_dec_ref_known(v___x_620_, 1);
lean_dec(v_snd_612_);
lean_dec(v_fst_611_);
lean_dec_ref(v_tag_586_);
lean_dec(v_cls_584_);
v___y_598_ = v___y_616_;
v___y_599_ = v_a_617_;
v_data_600_ = v_data_622_;
goto v___jp_597_;
}
else
{
lean_object* v_data_623_; double v___x_624_; double v___x_625_; 
lean_dec_ref_known(v_data_622_, 3);
v_data_623_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_623_, 0, v_cls_584_);
lean_ctor_set(v_data_623_, 1, v___x_620_);
lean_ctor_set(v_data_623_, 2, v_tag_586_);
v___x_624_ = lean_unbox_float(v_fst_611_);
lean_dec(v_fst_611_);
lean_ctor_set_float(v_data_623_, sizeof(void*)*3, v___x_624_);
v___x_625_ = lean_unbox_float(v_snd_612_);
lean_dec(v_snd_612_);
lean_ctor_set_float(v_data_623_, sizeof(void*)*3 + 8, v___x_625_);
lean_ctor_set_uint8(v_data_623_, sizeof(void*)*3 + 16, v_collapsed_585_);
v___y_598_ = v___y_616_;
v___y_599_ = v_a_617_;
v_data_600_ = v_data_623_;
goto v___jp_597_;
}
}
v___jp_626_:
{
lean_object* v_ref_627_; lean_object* v___x_628_; 
v_ref_627_ = lean_ctor_get(v___y_592_, 5);
lean_inc(v___y_593_);
lean_inc_ref(v___y_592_);
lean_inc(v_fst_595_);
v___x_628_ = lean_apply_4(v_msg_590_, v_fst_595_, v___y_592_, v___y_593_, lean_box(0));
if (lean_obj_tag(v___x_628_) == 0)
{
lean_object* v_a_629_; 
v_a_629_ = lean_ctor_get(v___x_628_, 0);
lean_inc(v_a_629_);
lean_dec_ref_known(v___x_628_, 1);
v___y_616_ = v_ref_627_;
v_a_617_ = v_a_629_;
goto v___jp_615_;
}
else
{
lean_object* v___x_630_; 
lean_dec_ref_known(v___x_628_, 1);
v___x_630_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2);
v___y_616_ = v_ref_627_;
v_a_617_ = v___x_630_;
goto v___jp_615_;
}
}
v___jp_631_:
{
if (v_clsEnabled_588_ == 0)
{
if (v___y_632_ == 0)
{
lean_object* v___x_633_; lean_object* v_traceState_634_; lean_object* v_env_635_; lean_object* v_nextMacroScope_636_; lean_object* v_ngen_637_; lean_object* v_auxDeclNGen_638_; lean_object* v_cache_639_; lean_object* v_messages_640_; lean_object* v_infoState_641_; lean_object* v_snapshotTasks_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_661_; 
lean_dec(v_snd_612_);
lean_dec(v_fst_611_);
lean_dec_ref(v_msg_590_);
lean_dec_ref(v_tag_586_);
lean_dec(v_cls_584_);
v___x_633_ = lean_st_ref_take(v___y_593_);
v_traceState_634_ = lean_ctor_get(v___x_633_, 4);
v_env_635_ = lean_ctor_get(v___x_633_, 0);
v_nextMacroScope_636_ = lean_ctor_get(v___x_633_, 1);
v_ngen_637_ = lean_ctor_get(v___x_633_, 2);
v_auxDeclNGen_638_ = lean_ctor_get(v___x_633_, 3);
v_cache_639_ = lean_ctor_get(v___x_633_, 5);
v_messages_640_ = lean_ctor_get(v___x_633_, 6);
v_infoState_641_ = lean_ctor_get(v___x_633_, 7);
v_snapshotTasks_642_ = lean_ctor_get(v___x_633_, 8);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_661_ == 0)
{
v___x_644_ = v___x_633_;
v_isShared_645_ = v_isSharedCheck_661_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_snapshotTasks_642_);
lean_inc(v_infoState_641_);
lean_inc(v_messages_640_);
lean_inc(v_cache_639_);
lean_inc(v_traceState_634_);
lean_inc(v_auxDeclNGen_638_);
lean_inc(v_ngen_637_);
lean_inc(v_nextMacroScope_636_);
lean_inc(v_env_635_);
lean_dec(v___x_633_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_661_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
uint64_t v_tid_646_; lean_object* v_traces_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_660_; 
v_tid_646_ = lean_ctor_get_uint64(v_traceState_634_, sizeof(void*)*1);
v_traces_647_ = lean_ctor_get(v_traceState_634_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v_traceState_634_);
if (v_isSharedCheck_660_ == 0)
{
v___x_649_ = v_traceState_634_;
v_isShared_650_ = v_isSharedCheck_660_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_traces_647_);
lean_dec(v_traceState_634_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_660_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_651_; lean_object* v___x_653_; 
v___x_651_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_589_, v_traces_647_);
lean_dec_ref(v_traces_647_);
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 0, v___x_651_);
v___x_653_ = v___x_649_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v___x_651_);
lean_ctor_set_uint64(v_reuseFailAlloc_659_, sizeof(void*)*1, v_tid_646_);
v___x_653_ = v_reuseFailAlloc_659_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
lean_object* v___x_655_; 
if (v_isShared_645_ == 0)
{
lean_ctor_set(v___x_644_, 4, v___x_653_);
v___x_655_ = v___x_644_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_env_635_);
lean_ctor_set(v_reuseFailAlloc_658_, 1, v_nextMacroScope_636_);
lean_ctor_set(v_reuseFailAlloc_658_, 2, v_ngen_637_);
lean_ctor_set(v_reuseFailAlloc_658_, 3, v_auxDeclNGen_638_);
lean_ctor_set(v_reuseFailAlloc_658_, 4, v___x_653_);
lean_ctor_set(v_reuseFailAlloc_658_, 5, v_cache_639_);
lean_ctor_set(v_reuseFailAlloc_658_, 6, v_messages_640_);
lean_ctor_set(v_reuseFailAlloc_658_, 7, v_infoState_641_);
lean_ctor_set(v_reuseFailAlloc_658_, 8, v_snapshotTasks_642_);
v___x_655_ = v_reuseFailAlloc_658_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_656_ = lean_st_ref_set(v___y_593_, v___x_655_);
v___x_657_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5___redArg(v_fst_595_);
return v___x_657_;
}
}
}
}
}
else
{
goto v___jp_626_;
}
}
else
{
goto v___jp_626_;
}
}
v___jp_662_:
{
double v___x_664_; double v___x_665_; double v___x_666_; uint8_t v___x_667_; 
v___x_664_ = lean_unbox_float(v_snd_612_);
v___x_665_ = lean_unbox_float(v_fst_611_);
v___x_666_ = lean_float_sub(v___x_664_, v___x_665_);
v___x_667_ = lean_float_decLt(v___y_663_, v___x_666_);
v___y_632_ = v___x_667_;
goto v___jp_631_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___boxed(lean_object* v_cls_678_, lean_object* v_collapsed_679_, lean_object* v_tag_680_, lean_object* v_opts_681_, lean_object* v_clsEnabled_682_, lean_object* v_oldTraces_683_, lean_object* v_msg_684_, lean_object* v_resStartStop_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_){
_start:
{
uint8_t v_collapsed_boxed_689_; uint8_t v_clsEnabled_boxed_690_; lean_object* v_res_691_; 
v_collapsed_boxed_689_ = lean_unbox(v_collapsed_679_);
v_clsEnabled_boxed_690_ = lean_unbox(v_clsEnabled_682_);
v_res_691_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3(v_cls_678_, v_collapsed_boxed_689_, v_tag_680_, v_opts_681_, v_clsEnabled_boxed_690_, v_oldTraces_683_, v_msg_684_, v_resStartStop_685_, v___y_686_, v___y_687_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec_ref(v_opts_681_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5___redArg(lean_object* v_msg_692_, lean_object* v___y_693_, lean_object* v___y_694_){
_start:
{
lean_object* v_ref_696_; lean_object* v___x_697_; lean_object* v_a_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_706_; 
v_ref_696_ = lean_ctor_get(v___y_693_, 5);
v___x_697_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0(v_msg_692_, v___y_693_, v___y_694_);
v_a_698_ = lean_ctor_get(v___x_697_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_706_ == 0)
{
v___x_700_ = v___x_697_;
v_isShared_701_ = v_isSharedCheck_706_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_a_698_);
lean_dec(v___x_697_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_706_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_702_; lean_object* v___x_704_; 
lean_inc(v_ref_696_);
v___x_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_702_, 0, v_ref_696_);
lean_ctor_set(v___x_702_, 1, v_a_698_);
if (v_isShared_701_ == 0)
{
lean_ctor_set_tag(v___x_700_, 1);
lean_ctor_set(v___x_700_, 0, v___x_702_);
v___x_704_ = v___x_700_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_702_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5___redArg___boxed(lean_object* v_msg_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5___redArg(v_msg_707_, v___y_708_, v___y_709_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0(lean_object* v_cls_715_, lean_object* v_msg_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
lean_object* v_ref_720_; lean_object* v___x_721_; lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_766_; 
v_ref_720_ = lean_ctor_get(v___y_717_, 5);
v___x_721_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0(v_msg_716_, v___y_717_, v___y_718_);
v_a_722_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_766_ == 0)
{
v___x_724_ = v___x_721_;
v_isShared_725_ = v_isSharedCheck_766_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_721_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_766_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_726_; lean_object* v_traceState_727_; lean_object* v_env_728_; lean_object* v_nextMacroScope_729_; lean_object* v_ngen_730_; lean_object* v_auxDeclNGen_731_; lean_object* v_cache_732_; lean_object* v_messages_733_; lean_object* v_infoState_734_; lean_object* v_snapshotTasks_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_765_; 
v___x_726_ = lean_st_ref_take(v___y_718_);
v_traceState_727_ = lean_ctor_get(v___x_726_, 4);
v_env_728_ = lean_ctor_get(v___x_726_, 0);
v_nextMacroScope_729_ = lean_ctor_get(v___x_726_, 1);
v_ngen_730_ = lean_ctor_get(v___x_726_, 2);
v_auxDeclNGen_731_ = lean_ctor_get(v___x_726_, 3);
v_cache_732_ = lean_ctor_get(v___x_726_, 5);
v_messages_733_ = lean_ctor_get(v___x_726_, 6);
v_infoState_734_ = lean_ctor_get(v___x_726_, 7);
v_snapshotTasks_735_ = lean_ctor_get(v___x_726_, 8);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_765_ == 0)
{
v___x_737_ = v___x_726_;
v_isShared_738_ = v_isSharedCheck_765_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_snapshotTasks_735_);
lean_inc(v_infoState_734_);
lean_inc(v_messages_733_);
lean_inc(v_cache_732_);
lean_inc(v_traceState_727_);
lean_inc(v_auxDeclNGen_731_);
lean_inc(v_ngen_730_);
lean_inc(v_nextMacroScope_729_);
lean_inc(v_env_728_);
lean_dec(v___x_726_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_765_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
uint64_t v_tid_739_; lean_object* v_traces_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_764_; 
v_tid_739_ = lean_ctor_get_uint64(v_traceState_727_, sizeof(void*)*1);
v_traces_740_ = lean_ctor_get(v_traceState_727_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v_traceState_727_);
if (v_isSharedCheck_764_ == 0)
{
v___x_742_ = v_traceState_727_;
v_isShared_743_ = v_isSharedCheck_764_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_traces_740_);
lean_dec(v_traceState_727_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_764_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_744_; double v___x_745_; uint8_t v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_754_; 
v___x_744_ = lean_box(0);
v___x_745_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0);
v___x_746_ = 0;
v___x_747_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0___closed__0));
v___x_748_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_748_, 0, v_cls_715_);
lean_ctor_set(v___x_748_, 1, v___x_744_);
lean_ctor_set(v___x_748_, 2, v___x_747_);
lean_ctor_set_float(v___x_748_, sizeof(void*)*3, v___x_745_);
lean_ctor_set_float(v___x_748_, sizeof(void*)*3 + 8, v___x_745_);
lean_ctor_set_uint8(v___x_748_, sizeof(void*)*3 + 16, v___x_746_);
v___x_749_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0___closed__1));
v___x_750_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_750_, 0, v___x_748_);
lean_ctor_set(v___x_750_, 1, v_a_722_);
lean_ctor_set(v___x_750_, 2, v___x_749_);
lean_inc(v_ref_720_);
v___x_751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_751_, 0, v_ref_720_);
lean_ctor_set(v___x_751_, 1, v___x_750_);
v___x_752_ = l_Lean_PersistentArray_push___redArg(v_traces_740_, v___x_751_);
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 0, v___x_752_);
v___x_754_ = v___x_742_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_752_);
lean_ctor_set_uint64(v_reuseFailAlloc_763_, sizeof(void*)*1, v_tid_739_);
v___x_754_ = v_reuseFailAlloc_763_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
lean_object* v___x_756_; 
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 4, v___x_754_);
v___x_756_ = v___x_737_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_env_728_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v_nextMacroScope_729_);
lean_ctor_set(v_reuseFailAlloc_762_, 2, v_ngen_730_);
lean_ctor_set(v_reuseFailAlloc_762_, 3, v_auxDeclNGen_731_);
lean_ctor_set(v_reuseFailAlloc_762_, 4, v___x_754_);
lean_ctor_set(v_reuseFailAlloc_762_, 5, v_cache_732_);
lean_ctor_set(v_reuseFailAlloc_762_, 6, v_messages_733_);
lean_ctor_set(v_reuseFailAlloc_762_, 7, v_infoState_734_);
lean_ctor_set(v_reuseFailAlloc_762_, 8, v_snapshotTasks_735_);
v___x_756_ = v_reuseFailAlloc_762_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_760_; 
v___x_757_ = lean_st_ref_set(v___y_718_, v___x_756_);
v___x_758_ = lean_box(0);
if (v_isShared_725_ == 0)
{
lean_ctor_set(v___x_724_, 0, v___x_758_);
v___x_760_ = v___x_724_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_758_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0___boxed(lean_object* v_cls_767_, lean_object* v_msg_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0(v_cls_767_, v_msg_768_, v___y_769_, v___y_770_);
lean_dec(v___y_770_);
lean_dec_ref(v___y_769_);
return v_res_772_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6(void){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_783_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__3));
v___x_784_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__5));
v___x_785_ = l_Lean_Name_append(v___x_784_, v___x_783_);
return v___x_785_;
}
}
static double _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9(void){
_start:
{
lean_object* v___x_788_; double v___x_789_; 
v___x_788_ = lean_unsigned_to_nat(1000000000u);
v___x_789_ = lean_float_of_nat(v___x_788_);
return v___x_789_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12(void){
_start:
{
lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_792_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__11));
v___x_793_ = l_Lean_stringToMessageData(v___x_792_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load(lean_object* v_lratPath_795_, uint8_t v_trimProofs_796_, lean_object* v_a_797_, lean_object* v_a_798_){
_start:
{
lean_object* v___x_800_; 
v___x_800_ = l_IO_FS_readBinFile(v_lratPath_795_);
if (lean_obj_tag(v___x_800_) == 0)
{
lean_object* v_options_801_; lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_1236_; 
v_options_801_ = lean_ctor_get(v_a_797_, 2);
v_a_802_ = lean_ctor_get(v___x_800_, 0);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_804_ = v___x_800_;
v_isShared_805_ = v_isSharedCheck_1236_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_dec(v___x_800_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_1236_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v_ref_806_; lean_object* v_inheritedTraceOptions_807_; uint8_t v_hasTrace_808_; lean_object* v___f_809_; lean_object* v___f_810_; lean_object* v___x_811_; lean_object* v_proof_813_; lean_object* v___y_814_; lean_object* v_options_815_; lean_object* v_inheritedTraceOptions_816_; lean_object* v___y_817_; lean_object* v_proof_849_; lean_object* v___y_850_; lean_object* v___y_851_; lean_object* v___y_857_; lean_object* v___y_858_; lean_object* v___y_859_; uint8_t v___x_861_; lean_object* v___x_862_; uint8_t v___y_864_; lean_object* v___y_865_; lean_object* v___y_866_; lean_object* v___y_867_; lean_object* v___y_868_; lean_object* v___y_869_; lean_object* v_a_870_; uint8_t v___y_880_; lean_object* v___y_881_; lean_object* v___y_882_; lean_object* v___y_883_; lean_object* v___y_884_; lean_object* v___y_885_; lean_object* v_a_886_; uint8_t v___y_889_; lean_object* v___y_890_; lean_object* v___y_891_; lean_object* v___y_892_; lean_object* v___y_893_; lean_object* v___y_894_; lean_object* v_a_895_; uint8_t v___y_908_; lean_object* v___y_909_; lean_object* v___y_910_; lean_object* v___y_911_; lean_object* v___y_912_; lean_object* v___y_913_; lean_object* v_a_914_; uint8_t v___y_917_; lean_object* v___y_918_; lean_object* v___y_919_; lean_object* v___y_920_; lean_object* v___y_921_; lean_object* v___y_922_; lean_object* v___y_996_; lean_object* v___y_997_; lean_object* v___y_998_; lean_object* v___y_999_; lean_object* v_a_1073_; lean_object* v___y_1095_; 
v_ref_806_ = lean_ctor_get(v_a_797_, 5);
v_inheritedTraceOptions_807_ = lean_ctor_get(v_a_797_, 13);
v_hasTrace_808_ = lean_ctor_get_uint8(v_options_801_, sizeof(void*)*1);
v___f_809_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__0));
v___f_810_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__1), 2, 1);
lean_closure_set(v___f_810_, 0, v_a_802_);
v___x_811_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__3));
v___x_861_ = 1;
v___x_862_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0___closed__0));
if (v_hasTrace_808_ == 0)
{
lean_object* v___x_1097_; 
v___x_1097_ = l_IO_lazyPure___redArg(v___f_810_);
if (lean_obj_tag(v___x_1097_) == 0)
{
lean_object* v_a_1098_; 
v_a_1098_ = lean_ctor_get(v___x_1097_, 0);
lean_inc(v_a_1098_);
lean_dec_ref_known(v___x_1097_, 1);
if (lean_obj_tag(v_a_1098_) == 0)
{
lean_object* v_a_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v_a_1099_ = lean_ctor_get(v_a_1098_, 0);
lean_inc(v_a_1099_);
lean_dec_ref_known(v_a_1098_, 1);
v___x_1100_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12);
v___x_1101_ = l_Lean_stringToMessageData(v_a_1099_);
v___x_1102_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1100_);
lean_ctor_set(v___x_1102_, 1, v___x_1101_);
v___x_1103_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5___redArg(v___x_1102_, v_a_797_, v_a_798_);
v___y_1095_ = v___x_1103_;
goto v___jp_1094_;
}
else
{
lean_object* v_a_1104_; 
v_a_1104_ = lean_ctor_get(v_a_1098_, 0);
lean_inc(v_a_1104_);
lean_dec_ref_known(v_a_1098_, 1);
v_a_1073_ = v_a_1104_;
goto v___jp_1072_;
}
}
else
{
lean_object* v_a_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1116_; 
lean_del_object(v___x_804_);
v_a_1105_ = lean_ctor_get(v___x_1097_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1107_ = v___x_1097_;
v_isShared_1108_ = v_isSharedCheck_1116_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_a_1105_);
lean_dec(v___x_1097_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1116_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1114_; 
v___x_1109_ = lean_io_error_to_string(v_a_1105_);
v___x_1110_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1109_);
v___x_1111_ = l_Lean_MessageData_ofFormat(v___x_1110_);
lean_inc(v_ref_806_);
v___x_1112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1112_, 0, v_ref_806_);
lean_ctor_set(v___x_1112_, 1, v___x_1111_);
if (v_isShared_1108_ == 0)
{
lean_ctor_set(v___x_1107_, 0, v___x_1112_);
v___x_1114_ = v___x_1107_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v___x_1112_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
}
}
else
{
lean_object* v___f_1117_; lean_object* v___x_1118_; uint8_t v___x_1119_; lean_object* v___y_1121_; lean_object* v___y_1122_; lean_object* v_a_1123_; lean_object* v___y_1136_; lean_object* v___y_1137_; lean_object* v_a_1138_; lean_object* v___y_1141_; lean_object* v___y_1142_; lean_object* v_a_1143_; lean_object* v___y_1146_; lean_object* v___y_1147_; lean_object* v_a_1148_; lean_object* v___y_1158_; lean_object* v___y_1159_; lean_object* v_a_1160_; lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v_a_1165_; 
v___f_1117_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__13));
v___x_1118_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6);
v___x_1119_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_807_, v_options_801_, v___x_1118_);
if (v___x_1119_ == 0)
{
lean_object* v___x_1214_; uint8_t v___x_1215_; 
v___x_1214_ = l_Lean_trace_profiler;
v___x_1215_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_options_801_, v___x_1214_);
if (v___x_1215_ == 0)
{
lean_object* v___x_1216_; 
v___x_1216_ = l_IO_lazyPure___redArg(v___f_810_);
if (lean_obj_tag(v___x_1216_) == 0)
{
lean_object* v_a_1217_; 
v_a_1217_ = lean_ctor_get(v___x_1216_, 0);
lean_inc(v_a_1217_);
lean_dec_ref_known(v___x_1216_, 1);
if (lean_obj_tag(v_a_1217_) == 0)
{
lean_object* v_a_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
v_a_1218_ = lean_ctor_get(v_a_1217_, 0);
lean_inc(v_a_1218_);
lean_dec_ref_known(v_a_1217_, 1);
v___x_1219_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12);
v___x_1220_ = l_Lean_stringToMessageData(v_a_1218_);
v___x_1221_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1219_);
lean_ctor_set(v___x_1221_, 1, v___x_1220_);
v___x_1222_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5___redArg(v___x_1221_, v_a_797_, v_a_798_);
v___y_1095_ = v___x_1222_;
goto v___jp_1094_;
}
else
{
lean_object* v_a_1223_; 
v_a_1223_ = lean_ctor_get(v_a_1217_, 0);
lean_inc(v_a_1223_);
lean_dec_ref_known(v_a_1217_, 1);
v_a_1073_ = v_a_1223_;
goto v___jp_1072_;
}
}
else
{
lean_object* v_a_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1235_; 
lean_del_object(v___x_804_);
v_a_1224_ = lean_ctor_get(v___x_1216_, 0);
v_isSharedCheck_1235_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1226_ = v___x_1216_;
v_isShared_1227_ = v_isSharedCheck_1235_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_a_1224_);
lean_dec(v___x_1216_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1235_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1233_; 
v___x_1228_ = lean_io_error_to_string(v_a_1224_);
v___x_1229_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1228_);
v___x_1230_ = l_Lean_MessageData_ofFormat(v___x_1229_);
lean_inc(v_ref_806_);
v___x_1231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1231_, 0, v_ref_806_);
lean_ctor_set(v___x_1231_, 1, v___x_1230_);
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 0, v___x_1231_);
v___x_1233_ = v___x_1226_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v___x_1231_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
}
else
{
goto v___jp_1167_;
}
}
else
{
goto v___jp_1167_;
}
v___jp_1120_:
{
lean_object* v___x_1124_; double v___x_1125_; double v___x_1126_; double v___x_1127_; double v___x_1128_; double v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1124_ = lean_io_mono_nanos_now();
v___x_1125_ = lean_float_of_nat(v___y_1122_);
v___x_1126_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9);
v___x_1127_ = lean_float_div(v___x_1125_, v___x_1126_);
v___x_1128_ = lean_float_of_nat(v___x_1124_);
v___x_1129_ = lean_float_div(v___x_1128_, v___x_1126_);
v___x_1130_ = lean_box_float(v___x_1127_);
v___x_1131_ = lean_box_float(v___x_1129_);
v___x_1132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1130_);
lean_ctor_set(v___x_1132_, 1, v___x_1131_);
v___x_1133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1133_, 0, v_a_1123_);
lean_ctor_set(v___x_1133_, 1, v___x_1132_);
v___x_1134_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3(v___x_811_, v___x_861_, v___x_862_, v_options_801_, v___x_1119_, v___y_1121_, v___f_1117_, v___x_1133_, v_a_797_, v_a_798_);
v___y_1095_ = v___x_1134_;
goto v___jp_1094_;
}
v___jp_1135_:
{
lean_object* v___x_1139_; 
v___x_1139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1139_, 0, v_a_1138_);
v___y_1121_ = v___y_1136_;
v___y_1122_ = v___y_1137_;
v_a_1123_ = v___x_1139_;
goto v___jp_1120_;
}
v___jp_1140_:
{
lean_object* v___x_1144_; 
v___x_1144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1144_, 0, v_a_1143_);
v___y_1121_ = v___y_1141_;
v___y_1122_ = v___y_1142_;
v_a_1123_ = v___x_1144_;
goto v___jp_1120_;
}
v___jp_1145_:
{
lean_object* v___x_1149_; double v___x_1150_; double v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1149_ = lean_io_get_num_heartbeats();
v___x_1150_ = lean_float_of_nat(v___y_1147_);
v___x_1151_ = lean_float_of_nat(v___x_1149_);
v___x_1152_ = lean_box_float(v___x_1150_);
v___x_1153_ = lean_box_float(v___x_1151_);
v___x_1154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1152_);
lean_ctor_set(v___x_1154_, 1, v___x_1153_);
v___x_1155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1155_, 0, v_a_1148_);
lean_ctor_set(v___x_1155_, 1, v___x_1154_);
v___x_1156_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3(v___x_811_, v___x_861_, v___x_862_, v_options_801_, v___x_1119_, v___y_1146_, v___f_1117_, v___x_1155_, v_a_797_, v_a_798_);
v___y_1095_ = v___x_1156_;
goto v___jp_1094_;
}
v___jp_1157_:
{
lean_object* v___x_1161_; 
v___x_1161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1161_, 0, v_a_1160_);
v___y_1146_ = v___y_1158_;
v___y_1147_ = v___y_1159_;
v_a_1148_ = v___x_1161_;
goto v___jp_1145_;
}
v___jp_1162_:
{
lean_object* v___x_1166_; 
v___x_1166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1166_, 0, v_a_1165_);
v___y_1146_ = v___y_1163_;
v___y_1147_ = v___y_1164_;
v_a_1148_ = v___x_1166_;
goto v___jp_1145_;
}
v___jp_1167_:
{
lean_object* v___x_1168_; lean_object* v_a_1169_; lean_object* v___x_1170_; uint8_t v___x_1171_; 
v___x_1168_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg(v_a_798_);
v_a_1169_ = lean_ctor_get(v___x_1168_, 0);
lean_inc(v_a_1169_);
lean_dec_ref(v___x_1168_);
v___x_1170_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1171_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_options_801_, v___x_1170_);
if (v___x_1171_ == 0)
{
lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1172_ = lean_io_mono_nanos_now();
v___x_1173_ = l_IO_lazyPure___redArg(v___f_810_);
if (lean_obj_tag(v___x_1173_) == 0)
{
lean_object* v_a_1174_; 
v_a_1174_ = lean_ctor_get(v___x_1173_, 0);
lean_inc(v_a_1174_);
lean_dec_ref_known(v___x_1173_, 1);
if (lean_obj_tag(v_a_1174_) == 0)
{
lean_object* v_a_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v_a_1180_; 
v_a_1175_ = lean_ctor_get(v_a_1174_, 0);
lean_inc(v_a_1175_);
lean_dec_ref_known(v_a_1174_, 1);
v___x_1176_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12);
v___x_1177_ = l_Lean_stringToMessageData(v_a_1175_);
v___x_1178_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1176_);
lean_ctor_set(v___x_1178_, 1, v___x_1177_);
v___x_1179_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5___redArg(v___x_1178_, v_a_797_, v_a_798_);
v_a_1180_ = lean_ctor_get(v___x_1179_, 0);
lean_inc(v_a_1180_);
lean_dec_ref(v___x_1179_);
v___y_1136_ = v_a_1169_;
v___y_1137_ = v___x_1172_;
v_a_1138_ = v_a_1180_;
goto v___jp_1135_;
}
else
{
lean_object* v_a_1181_; 
v_a_1181_ = lean_ctor_get(v_a_1174_, 0);
lean_inc(v_a_1181_);
lean_dec_ref_known(v_a_1174_, 1);
v___y_1141_ = v_a_1169_;
v___y_1142_ = v___x_1172_;
v_a_1143_ = v_a_1181_;
goto v___jp_1140_;
}
}
else
{
lean_object* v_a_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1192_; 
v_a_1182_ = lean_ctor_get(v___x_1173_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1173_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1184_ = v___x_1173_;
v_isShared_1185_ = v_isSharedCheck_1192_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_a_1182_);
lean_dec(v___x_1173_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1192_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1186_; lean_object* v___x_1188_; 
v___x_1186_ = lean_io_error_to_string(v_a_1182_);
if (v_isShared_1185_ == 0)
{
lean_ctor_set_tag(v___x_1184_, 3);
lean_ctor_set(v___x_1184_, 0, v___x_1186_);
v___x_1188_ = v___x_1184_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v___x_1186_);
v___x_1188_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1189_ = l_Lean_MessageData_ofFormat(v___x_1188_);
lean_inc(v_ref_806_);
v___x_1190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1190_, 0, v_ref_806_);
lean_ctor_set(v___x_1190_, 1, v___x_1189_);
v___y_1136_ = v_a_1169_;
v___y_1137_ = v___x_1172_;
v_a_1138_ = v___x_1190_;
goto v___jp_1135_;
}
}
}
}
else
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1193_ = lean_io_get_num_heartbeats();
v___x_1194_ = l_IO_lazyPure___redArg(v___f_810_);
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v_a_1195_; 
v_a_1195_ = lean_ctor_get(v___x_1194_, 0);
lean_inc(v_a_1195_);
lean_dec_ref_known(v___x_1194_, 1);
if (lean_obj_tag(v_a_1195_) == 0)
{
lean_object* v_a_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v_a_1201_; 
v_a_1196_ = lean_ctor_get(v_a_1195_, 0);
lean_inc(v_a_1196_);
lean_dec_ref_known(v_a_1195_, 1);
v___x_1197_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12);
v___x_1198_ = l_Lean_stringToMessageData(v_a_1196_);
v___x_1199_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1197_);
lean_ctor_set(v___x_1199_, 1, v___x_1198_);
v___x_1200_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5___redArg(v___x_1199_, v_a_797_, v_a_798_);
v_a_1201_ = lean_ctor_get(v___x_1200_, 0);
lean_inc(v_a_1201_);
lean_dec_ref(v___x_1200_);
v___y_1158_ = v_a_1169_;
v___y_1159_ = v___x_1193_;
v_a_1160_ = v_a_1201_;
goto v___jp_1157_;
}
else
{
lean_object* v_a_1202_; 
v_a_1202_ = lean_ctor_get(v_a_1195_, 0);
lean_inc(v_a_1202_);
lean_dec_ref_known(v_a_1195_, 1);
v___y_1163_ = v_a_1169_;
v___y_1164_ = v___x_1193_;
v_a_1165_ = v_a_1202_;
goto v___jp_1162_;
}
}
else
{
lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1213_; 
v_a_1203_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1205_ = v___x_1194_;
v_isShared_1206_ = v_isSharedCheck_1213_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v___x_1194_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1213_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1207_; lean_object* v___x_1209_; 
v___x_1207_ = lean_io_error_to_string(v_a_1203_);
if (v_isShared_1206_ == 0)
{
lean_ctor_set_tag(v___x_1205_, 3);
lean_ctor_set(v___x_1205_, 0, v___x_1207_);
v___x_1209_ = v___x_1205_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v___x_1207_);
v___x_1209_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = l_Lean_MessageData_ofFormat(v___x_1209_);
lean_inc(v_ref_806_);
v___x_1211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1211_, 0, v_ref_806_);
lean_ctor_set(v___x_1211_, 1, v___x_1210_);
v___y_1158_ = v_a_1169_;
v___y_1159_ = v___x_1193_;
v_a_1160_ = v___x_1211_;
goto v___jp_1157_;
}
}
}
}
}
}
v___jp_812_:
{
lean_object* v___x_818_; uint8_t v___x_819_; 
v___x_818_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6);
v___x_819_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_816_, v_options_815_, v___x_818_);
if (v___x_819_ == 0)
{
lean_object* v___x_821_; 
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 0, v_proof_813_);
v___x_821_ = v___x_804_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_proof_813_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
else
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
lean_del_object(v___x_804_);
v___x_823_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__7));
v___x_824_ = lean_array_get_size(v_proof_813_);
v___x_825_ = l_Nat_reprFast(v___x_824_);
v___x_826_ = lean_string_append(v___x_823_, v___x_825_);
lean_dec_ref(v___x_825_);
v___x_827_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__8));
v___x_828_ = lean_string_append(v___x_826_, v___x_827_);
v___x_829_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_829_, 0, v___x_828_);
v___x_830_ = l_Lean_MessageData_ofFormat(v___x_829_);
v___x_831_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0(v___x_811_, v___x_830_, v___y_814_, v___y_817_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_838_; 
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_838_ == 0)
{
lean_object* v_unused_839_; 
v_unused_839_ = lean_ctor_get(v___x_831_, 0);
lean_dec(v_unused_839_);
v___x_833_ = v___x_831_;
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
else
{
lean_dec(v___x_831_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_836_; 
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 0, v_proof_813_);
v___x_836_ = v___x_833_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_proof_813_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
else
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_847_; 
lean_dec_ref(v_proof_813_);
v_a_840_ = lean_ctor_get(v___x_831_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_847_ == 0)
{
v___x_842_ = v___x_831_;
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_831_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_843_ == 0)
{
v___x_845_ = v___x_842_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_a_840_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
}
}
v___jp_848_:
{
lean_object* v_options_852_; uint8_t v_hasTrace_853_; 
v_options_852_ = lean_ctor_get(v___y_850_, 2);
v_hasTrace_853_ = lean_ctor_get_uint8(v_options_852_, sizeof(void*)*1);
if (v_hasTrace_853_ == 0)
{
lean_object* v___x_854_; 
lean_del_object(v___x_804_);
v___x_854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_854_, 0, v_proof_849_);
return v___x_854_;
}
else
{
lean_object* v_inheritedTraceOptions_855_; 
v_inheritedTraceOptions_855_ = lean_ctor_get(v___y_850_, 13);
v_proof_813_ = v_proof_849_;
v___y_814_ = v___y_850_;
v_options_815_ = v_options_852_;
v_inheritedTraceOptions_816_ = v_inheritedTraceOptions_855_;
v___y_817_ = v___y_851_;
goto v___jp_812_;
}
}
v___jp_856_:
{
if (lean_obj_tag(v___y_859_) == 0)
{
lean_object* v_a_860_; 
v_a_860_ = lean_ctor_get(v___y_859_, 0);
lean_inc(v_a_860_);
lean_dec_ref_known(v___y_859_, 1);
v_proof_849_ = v_a_860_;
v___y_850_ = v___y_857_;
v___y_851_ = v___y_858_;
goto v___jp_848_;
}
else
{
lean_del_object(v___x_804_);
return v___y_859_;
}
}
v___jp_863_:
{
lean_object* v___x_871_; double v___x_872_; double v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_871_ = lean_io_get_num_heartbeats();
v___x_872_ = lean_float_of_nat(v___y_865_);
v___x_873_ = lean_float_of_nat(v___x_871_);
v___x_874_ = lean_box_float(v___x_872_);
v___x_875_ = lean_box_float(v___x_873_);
v___x_876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_876_, 0, v___x_874_);
lean_ctor_set(v___x_876_, 1, v___x_875_);
v___x_877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_877_, 0, v_a_870_);
lean_ctor_set(v___x_877_, 1, v___x_876_);
v___x_878_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3(v___x_811_, v___x_861_, v___x_862_, v___y_867_, v___y_864_, v___y_869_, v___f_809_, v___x_877_, v___y_866_, v___y_868_);
v___y_857_ = v___y_866_;
v___y_858_ = v___y_868_;
v___y_859_ = v___x_878_;
goto v___jp_856_;
}
v___jp_879_:
{
lean_object* v___x_887_; 
v___x_887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_887_, 0, v_a_886_);
v___y_864_ = v___y_880_;
v___y_865_ = v___y_881_;
v___y_866_ = v___y_882_;
v___y_867_ = v___y_883_;
v___y_868_ = v___y_885_;
v___y_869_ = v___y_884_;
v_a_870_ = v___x_887_;
goto v___jp_863_;
}
v___jp_888_:
{
lean_object* v___x_896_; double v___x_897_; double v___x_898_; double v___x_899_; double v___x_900_; double v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_896_ = lean_io_mono_nanos_now();
v___x_897_ = lean_float_of_nat(v___y_894_);
v___x_898_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9);
v___x_899_ = lean_float_div(v___x_897_, v___x_898_);
v___x_900_ = lean_float_of_nat(v___x_896_);
v___x_901_ = lean_float_div(v___x_900_, v___x_898_);
v___x_902_ = lean_box_float(v___x_899_);
v___x_903_ = lean_box_float(v___x_901_);
v___x_904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_902_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
v___x_905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_905_, 0, v_a_895_);
lean_ctor_set(v___x_905_, 1, v___x_904_);
v___x_906_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3(v___x_811_, v___x_861_, v___x_862_, v___y_891_, v___y_889_, v___y_893_, v___f_809_, v___x_905_, v___y_890_, v___y_892_);
v___y_857_ = v___y_890_;
v___y_858_ = v___y_892_;
v___y_859_ = v___x_906_;
goto v___jp_856_;
}
v___jp_907_:
{
lean_object* v___x_915_; 
v___x_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_915_, 0, v_a_914_);
v___y_889_ = v___y_908_;
v___y_890_ = v___y_909_;
v___y_891_ = v___y_910_;
v___y_892_ = v___y_913_;
v___y_893_ = v___y_912_;
v___y_894_ = v___y_911_;
v_a_895_ = v___x_915_;
goto v___jp_888_;
}
v___jp_916_:
{
lean_object* v___x_923_; lean_object* v_a_924_; lean_object* v___x_925_; uint8_t v___x_926_; 
v___x_923_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg(v___y_922_);
v_a_924_ = lean_ctor_get(v___x_923_, 0);
lean_inc(v_a_924_);
lean_dec_ref(v___x_923_);
v___x_925_ = l_Lean_trace_profiler_useHeartbeats;
v___x_926_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v___y_920_, v___x_925_);
if (v___x_926_ == 0)
{
lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_927_ = lean_io_mono_nanos_now();
v___x_928_ = l_IO_lazyPure___redArg(v___y_918_);
if (lean_obj_tag(v___x_928_) == 0)
{
lean_object* v_a_929_; lean_object* v___x_930_; 
v_a_929_ = lean_ctor_get(v___x_928_, 0);
lean_inc(v_a_929_);
lean_dec_ref_known(v___x_928_, 1);
v___x_930_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__4___redArg(v_a_929_);
if (lean_obj_tag(v___x_930_) == 0)
{
lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_938_; 
v_a_931_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_938_ == 0)
{
v___x_933_ = v___x_930_;
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v___x_930_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_936_; 
if (v_isShared_934_ == 0)
{
lean_ctor_set_tag(v___x_933_, 1);
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
v___y_889_ = v___y_917_;
v___y_890_ = v___y_919_;
v___y_891_ = v___y_920_;
v___y_892_ = v___y_922_;
v___y_893_ = v_a_924_;
v___y_894_ = v___x_927_;
v_a_895_ = v___x_936_;
goto v___jp_888_;
}
}
}
else
{
lean_object* v_a_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_949_; 
v_a_939_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_949_ == 0)
{
v___x_941_ = v___x_930_;
v_isShared_942_ = v_isSharedCheck_949_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_a_939_);
lean_dec(v___x_930_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_949_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_943_; lean_object* v___x_945_; 
v___x_943_ = lean_io_error_to_string(v_a_939_);
if (v_isShared_942_ == 0)
{
lean_ctor_set_tag(v___x_941_, 3);
lean_ctor_set(v___x_941_, 0, v___x_943_);
v___x_945_ = v___x_941_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_943_);
v___x_945_ = v_reuseFailAlloc_948_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_946_ = l_Lean_MessageData_ofFormat(v___x_945_);
lean_inc(v___y_921_);
v___x_947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_947_, 0, v___y_921_);
lean_ctor_set(v___x_947_, 1, v___x_946_);
v___y_908_ = v___y_917_;
v___y_909_ = v___y_919_;
v___y_910_ = v___y_920_;
v___y_911_ = v___x_927_;
v___y_912_ = v_a_924_;
v___y_913_ = v___y_922_;
v_a_914_ = v___x_947_;
goto v___jp_907_;
}
}
}
}
else
{
lean_object* v_a_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_960_; 
v_a_950_ = lean_ctor_get(v___x_928_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_960_ == 0)
{
v___x_952_ = v___x_928_;
v_isShared_953_ = v_isSharedCheck_960_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_a_950_);
lean_dec(v___x_928_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_960_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_954_; lean_object* v___x_956_; 
v___x_954_ = lean_io_error_to_string(v_a_950_);
if (v_isShared_953_ == 0)
{
lean_ctor_set_tag(v___x_952_, 3);
lean_ctor_set(v___x_952_, 0, v___x_954_);
v___x_956_ = v___x_952_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v___x_954_);
v___x_956_ = v_reuseFailAlloc_959_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_957_ = l_Lean_MessageData_ofFormat(v___x_956_);
lean_inc(v___y_921_);
v___x_958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_958_, 0, v___y_921_);
lean_ctor_set(v___x_958_, 1, v___x_957_);
v___y_908_ = v___y_917_;
v___y_909_ = v___y_919_;
v___y_910_ = v___y_920_;
v___y_911_ = v___x_927_;
v___y_912_ = v_a_924_;
v___y_913_ = v___y_922_;
v_a_914_ = v___x_958_;
goto v___jp_907_;
}
}
}
}
else
{
lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_961_ = lean_io_get_num_heartbeats();
v___x_962_ = l_IO_lazyPure___redArg(v___y_918_);
if (lean_obj_tag(v___x_962_) == 0)
{
lean_object* v_a_963_; lean_object* v___x_964_; 
v_a_963_ = lean_ctor_get(v___x_962_, 0);
lean_inc(v_a_963_);
lean_dec_ref_known(v___x_962_, 1);
v___x_964_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__4___redArg(v_a_963_);
if (lean_obj_tag(v___x_964_) == 0)
{
lean_object* v_a_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_972_; 
v_a_965_ = lean_ctor_get(v___x_964_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_972_ == 0)
{
v___x_967_ = v___x_964_;
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_a_965_);
lean_dec(v___x_964_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_970_; 
if (v_isShared_968_ == 0)
{
lean_ctor_set_tag(v___x_967_, 1);
v___x_970_ = v___x_967_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_a_965_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
v___y_864_ = v___y_917_;
v___y_865_ = v___x_961_;
v___y_866_ = v___y_919_;
v___y_867_ = v___y_920_;
v___y_868_ = v___y_922_;
v___y_869_ = v_a_924_;
v_a_870_ = v___x_970_;
goto v___jp_863_;
}
}
}
else
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_983_; 
v_a_973_ = lean_ctor_get(v___x_964_, 0);
v_isSharedCheck_983_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_983_ == 0)
{
v___x_975_ = v___x_964_;
v_isShared_976_ = v_isSharedCheck_983_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_964_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_983_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_977_; lean_object* v___x_979_; 
v___x_977_ = lean_io_error_to_string(v_a_973_);
if (v_isShared_976_ == 0)
{
lean_ctor_set_tag(v___x_975_, 3);
lean_ctor_set(v___x_975_, 0, v___x_977_);
v___x_979_ = v___x_975_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v___x_977_);
v___x_979_ = v_reuseFailAlloc_982_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_980_ = l_Lean_MessageData_ofFormat(v___x_979_);
lean_inc(v___y_921_);
v___x_981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_981_, 0, v___y_921_);
lean_ctor_set(v___x_981_, 1, v___x_980_);
v___y_880_ = v___y_917_;
v___y_881_ = v___x_961_;
v___y_882_ = v___y_919_;
v___y_883_ = v___y_920_;
v___y_884_ = v_a_924_;
v___y_885_ = v___y_922_;
v_a_886_ = v___x_981_;
goto v___jp_879_;
}
}
}
}
else
{
lean_object* v_a_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_994_; 
v_a_984_ = lean_ctor_get(v___x_962_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_994_ == 0)
{
v___x_986_ = v___x_962_;
v_isShared_987_ = v_isSharedCheck_994_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_a_984_);
lean_dec(v___x_962_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_994_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_988_; lean_object* v___x_990_; 
v___x_988_ = lean_io_error_to_string(v_a_984_);
if (v_isShared_987_ == 0)
{
lean_ctor_set_tag(v___x_986_, 3);
lean_ctor_set(v___x_986_, 0, v___x_988_);
v___x_990_ = v___x_986_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v___x_988_);
v___x_990_ = v_reuseFailAlloc_993_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_991_ = l_Lean_MessageData_ofFormat(v___x_990_);
lean_inc(v___y_921_);
v___x_992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_992_, 0, v___y_921_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
v___y_880_ = v___y_917_;
v___y_881_ = v___x_961_;
v___y_882_ = v___y_919_;
v___y_883_ = v___y_920_;
v___y_884_ = v_a_924_;
v___y_885_ = v___y_922_;
v_a_886_ = v___x_992_;
goto v___jp_879_;
}
}
}
}
}
v___jp_995_:
{
if (v_trimProofs_796_ == 0)
{
lean_dec_ref(v___y_996_);
v_proof_849_ = v___y_997_;
v___y_850_ = v___y_998_;
v___y_851_ = v___y_999_;
goto v___jp_848_;
}
else
{
lean_object* v_options_1000_; uint8_t v_hasTrace_1001_; 
lean_dec_ref(v___y_997_);
v_options_1000_ = lean_ctor_get(v___y_998_, 2);
v_hasTrace_1001_ = lean_ctor_get_uint8(v_options_1000_, sizeof(void*)*1);
if (v_hasTrace_1001_ == 0)
{
lean_object* v_ref_1002_; lean_object* v___x_1003_; 
lean_del_object(v___x_804_);
v_ref_1002_ = lean_ctor_get(v___y_998_, 5);
v___x_1003_ = l_IO_lazyPure___redArg(v___y_996_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v___x_1005_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_a_1004_);
lean_dec_ref_known(v___x_1003_, 1);
v___x_1005_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__4___redArg(v_a_1004_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1013_; 
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1008_ = v___x_1005_;
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_1005_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1011_; 
if (v_isShared_1009_ == 0)
{
v___x_1011_ = v___x_1008_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_a_1006_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
else
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1025_; 
v_a_1014_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1016_ = v___x_1005_;
v_isShared_1017_ = v_isSharedCheck_1025_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_1005_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1025_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1023_; 
v___x_1018_ = lean_io_error_to_string(v_a_1014_);
v___x_1019_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1018_);
v___x_1020_ = l_Lean_MessageData_ofFormat(v___x_1019_);
lean_inc(v_ref_1002_);
v___x_1021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1021_, 0, v_ref_1002_);
lean_ctor_set(v___x_1021_, 1, v___x_1020_);
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 0, v___x_1021_);
v___x_1023_ = v___x_1016_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v___x_1021_);
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
else
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1037_; 
v_a_1026_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1028_ = v___x_1003_;
v_isShared_1029_ = v_isSharedCheck_1037_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_1003_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1037_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1035_; 
v___x_1030_ = lean_io_error_to_string(v_a_1026_);
v___x_1031_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1030_);
v___x_1032_ = l_Lean_MessageData_ofFormat(v___x_1031_);
lean_inc(v_ref_1002_);
v___x_1033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1033_, 0, v_ref_1002_);
lean_ctor_set(v___x_1033_, 1, v___x_1032_);
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 0, v___x_1033_);
v___x_1035_ = v___x_1028_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v___x_1033_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
}
}
else
{
lean_object* v_ref_1038_; lean_object* v_inheritedTraceOptions_1039_; lean_object* v___x_1040_; uint8_t v___x_1041_; 
v_ref_1038_ = lean_ctor_get(v___y_998_, 5);
v_inheritedTraceOptions_1039_ = lean_ctor_get(v___y_998_, 13);
v___x_1040_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6);
v___x_1041_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1039_, v_options_1000_, v___x_1040_);
if (v___x_1041_ == 0)
{
lean_object* v___x_1042_; uint8_t v___x_1043_; 
v___x_1042_ = l_Lean_trace_profiler;
v___x_1043_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_options_1000_, v___x_1042_);
if (v___x_1043_ == 0)
{
lean_object* v___x_1044_; 
v___x_1044_ = l_IO_lazyPure___redArg(v___y_996_);
if (lean_obj_tag(v___x_1044_) == 0)
{
lean_object* v_a_1045_; lean_object* v___x_1046_; 
v_a_1045_ = lean_ctor_get(v___x_1044_, 0);
lean_inc(v_a_1045_);
lean_dec_ref_known(v___x_1044_, 1);
v___x_1046_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__4___redArg(v_a_1045_);
if (lean_obj_tag(v___x_1046_) == 0)
{
lean_object* v_a_1047_; 
v_a_1047_ = lean_ctor_get(v___x_1046_, 0);
lean_inc(v_a_1047_);
lean_dec_ref_known(v___x_1046_, 1);
v_proof_813_ = v_a_1047_;
v___y_814_ = v___y_998_;
v_options_815_ = v_options_1000_;
v_inheritedTraceOptions_816_ = v_inheritedTraceOptions_1039_;
v___y_817_ = v___y_999_;
goto v___jp_812_;
}
else
{
lean_object* v_a_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1059_; 
lean_del_object(v___x_804_);
v_a_1048_ = lean_ctor_get(v___x_1046_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1050_ = v___x_1046_;
v_isShared_1051_ = v_isSharedCheck_1059_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_a_1048_);
lean_dec(v___x_1046_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1059_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1057_; 
v___x_1052_ = lean_io_error_to_string(v_a_1048_);
v___x_1053_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1052_);
v___x_1054_ = l_Lean_MessageData_ofFormat(v___x_1053_);
lean_inc(v_ref_1038_);
v___x_1055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1055_, 0, v_ref_1038_);
lean_ctor_set(v___x_1055_, 1, v___x_1054_);
if (v_isShared_1051_ == 0)
{
lean_ctor_set(v___x_1050_, 0, v___x_1055_);
v___x_1057_ = v___x_1050_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v___x_1055_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
else
{
lean_object* v_a_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1071_; 
lean_del_object(v___x_804_);
v_a_1060_ = lean_ctor_get(v___x_1044_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1062_ = v___x_1044_;
v_isShared_1063_ = v_isSharedCheck_1071_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_a_1060_);
lean_dec(v___x_1044_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1071_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1069_; 
v___x_1064_ = lean_io_error_to_string(v_a_1060_);
v___x_1065_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1064_);
v___x_1066_ = l_Lean_MessageData_ofFormat(v___x_1065_);
lean_inc(v_ref_1038_);
v___x_1067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1067_, 0, v_ref_1038_);
lean_ctor_set(v___x_1067_, 1, v___x_1066_);
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 0, v___x_1067_);
v___x_1069_ = v___x_1062_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1067_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
}
else
{
v___y_917_ = v___x_1041_;
v___y_918_ = v___y_996_;
v___y_919_ = v___y_998_;
v___y_920_ = v_options_1000_;
v___y_921_ = v_ref_1038_;
v___y_922_ = v___y_999_;
goto v___jp_916_;
}
}
else
{
v___y_917_ = v___x_1041_;
v___y_918_ = v___y_996_;
v___y_919_ = v___y_998_;
v___y_920_ = v_options_1000_;
v___y_921_ = v_ref_1038_;
v___y_922_ = v___y_999_;
goto v___jp_916_;
}
}
}
}
v___jp_1072_:
{
lean_object* v___f_1074_; 
lean_inc_ref(v_a_1073_);
v___f_1074_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__2___boxed), 2, 1);
lean_closure_set(v___f_1074_, 0, v_a_1073_);
if (v_hasTrace_808_ == 0)
{
v___y_996_ = v___f_1074_;
v___y_997_ = v_a_1073_;
v___y_998_ = v_a_797_;
v___y_999_ = v_a_798_;
goto v___jp_995_;
}
else
{
lean_object* v___x_1075_; uint8_t v___x_1076_; 
v___x_1075_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6);
v___x_1076_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_807_, v_options_801_, v___x_1075_);
if (v___x_1076_ == 0)
{
v___y_996_ = v___f_1074_;
v___y_997_ = v_a_1073_;
v___y_998_ = v_a_797_;
v___y_999_ = v_a_798_;
goto v___jp_995_;
}
else
{
lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1077_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__7));
v___x_1078_ = lean_array_get_size(v_a_1073_);
v___x_1079_ = l_Nat_reprFast(v___x_1078_);
v___x_1080_ = lean_string_append(v___x_1077_, v___x_1079_);
lean_dec_ref(v___x_1079_);
v___x_1081_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__10));
v___x_1082_ = lean_string_append(v___x_1080_, v___x_1081_);
v___x_1083_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1082_);
v___x_1084_ = l_Lean_MessageData_ofFormat(v___x_1083_);
v___x_1085_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0(v___x_811_, v___x_1084_, v_a_797_, v_a_798_);
if (lean_obj_tag(v___x_1085_) == 0)
{
lean_dec_ref_known(v___x_1085_, 1);
v___y_996_ = v___f_1074_;
v___y_997_ = v_a_1073_;
v___y_998_ = v_a_797_;
v___y_999_ = v_a_798_;
goto v___jp_995_;
}
else
{
lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1093_; 
lean_dec_ref(v___f_1074_);
lean_dec_ref(v_a_1073_);
lean_del_object(v___x_804_);
v_a_1086_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1088_ = v___x_1085_;
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v___x_1085_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1091_; 
if (v_isShared_1089_ == 0)
{
v___x_1091_ = v___x_1088_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_a_1086_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
}
}
}
v___jp_1094_:
{
if (lean_obj_tag(v___y_1095_) == 0)
{
lean_object* v_a_1096_; 
v_a_1096_ = lean_ctor_get(v___y_1095_, 0);
lean_inc(v_a_1096_);
lean_dec_ref_known(v___y_1095_, 1);
v_a_1073_ = v_a_1096_;
goto v___jp_1072_;
}
else
{
lean_del_object(v___x_804_);
return v___y_1095_;
}
}
}
}
else
{
lean_object* v_a_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1249_; 
v_a_1237_ = lean_ctor_get(v___x_800_, 0);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1239_ = v___x_800_;
v_isShared_1240_ = v_isSharedCheck_1249_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_a_1237_);
lean_dec(v___x_800_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1249_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v_ref_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1247_; 
v_ref_1241_ = lean_ctor_get(v_a_797_, 5);
v___x_1242_ = lean_io_error_to_string(v_a_1237_);
v___x_1243_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1242_);
v___x_1244_ = l_Lean_MessageData_ofFormat(v___x_1243_);
lean_inc(v_ref_1241_);
v___x_1245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1245_, 0, v_ref_1241_);
lean_ctor_set(v___x_1245_, 1, v___x_1244_);
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 0, v___x_1245_);
v___x_1247_ = v___x_1239_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v___x_1245_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___boxed(lean_object* v_lratPath_1250_, lean_object* v_trimProofs_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_){
_start:
{
uint8_t v_trimProofs_boxed_1255_; lean_object* v_res_1256_; 
v_trimProofs_boxed_1255_ = lean_unbox(v_trimProofs_1251_);
v_res_1256_ = l_Lean_Meta_Tactic_BVDecide_LratCert_load(v_lratPath_1250_, v_trimProofs_boxed_1255_, v_a_1252_, v_a_1253_);
lean_dec(v_a_1253_);
lean_dec_ref(v_a_1252_);
lean_dec_ref(v_lratPath_1250_);
return v_res_1256_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5(lean_object* v_00_u03b1_1257_, lean_object* v_x_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
lean_object* v___x_1262_; 
v___x_1262_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5___redArg(v_x_1258_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1263_, lean_object* v_x_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
lean_object* v_res_1268_; 
v_res_1268_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5(v_00_u03b1_1263_, v_x_1264_, v___y_1265_, v___y_1266_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5(lean_object* v_00_u03b1_1269_, lean_object* v_msg_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
lean_object* v___x_1274_; 
v___x_1274_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5___redArg(v_msg_1270_, v___y_1271_, v___y_1272_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5___boxed(lean_object* v_00_u03b1_1275_, lean_object* v_msg_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5(v_00_u03b1_1275_, v_msg_1276_, v___y_1277_, v___y_1278_);
lean_dec(v___y_1278_);
lean_dec_ref(v___y_1277_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(lean_object* v_lratPath_1281_, uint8_t v_trimProofs_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_){
_start:
{
lean_object* v___x_1286_; 
v___x_1286_ = l_Lean_Meta_Tactic_BVDecide_LratCert_load(v_lratPath_1281_, v_trimProofs_1282_, v_a_1283_, v_a_1284_);
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1295_; 
v_a_1287_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1289_ = v___x_1286_;
v_isShared_1290_ = v_isSharedCheck_1295_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_a_1287_);
lean_dec(v___x_1286_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1295_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1291_; lean_object* v___x_1293_; 
v___x_1291_ = l_Std_Tactic_BVDecide_LRAT_lratProofToString(v_a_1287_);
lean_dec(v_a_1287_);
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 0, v___x_1291_);
v___x_1293_ = v___x_1289_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v___x_1291_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
else
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1303_; 
v_a_1296_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1298_ = v___x_1286_;
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1286_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1301_; 
if (v_isShared_1299_ == 0)
{
v___x_1301_ = v___x_1298_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_a_1296_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile___boxed(lean_object* v_lratPath_1304_, lean_object* v_trimProofs_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_){
_start:
{
uint8_t v_trimProofs_boxed_1309_; lean_object* v_res_1310_; 
v_trimProofs_boxed_1309_ = lean_unbox(v_trimProofs_1305_);
v_res_1310_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_1304_, v_trimProofs_boxed_1309_, v_a_1306_, v_a_1307_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
lean_dec_ref(v_lratPath_1304_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg___lam__0(lean_object* v_snd_1311_, lean_object* v___y_1312_, lean_object* v_a_x3f_1313_){
_start:
{
lean_object* v___x_1315_; 
v___x_1315_ = lean_io_remove_file(v_snd_1311_);
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_object* v_a_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1323_; 
v_a_1316_ = lean_ctor_get(v___x_1315_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1318_ = v___x_1315_;
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_a_1316_);
lean_dec(v___x_1315_);
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
v_reuseFailAlloc_1322_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1336_; 
v_a_1324_ = lean_ctor_get(v___x_1315_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1326_ = v___x_1315_;
v_isShared_1327_ = v_isSharedCheck_1336_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_a_1324_);
lean_dec(v___x_1315_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1336_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v_ref_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1334_; 
v_ref_1328_ = lean_ctor_get(v___y_1312_, 5);
v___x_1329_ = lean_io_error_to_string(v_a_1324_);
v___x_1330_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1329_);
v___x_1331_ = l_Lean_MessageData_ofFormat(v___x_1330_);
lean_inc(v_ref_1328_);
v___x_1332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1332_, 0, v_ref_1328_);
lean_ctor_set(v___x_1332_, 1, v___x_1331_);
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 0, v___x_1332_);
v___x_1334_ = v___x_1326_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v___x_1332_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg___lam__0___boxed(lean_object* v_snd_1337_, lean_object* v___y_1338_, lean_object* v_a_x3f_1339_, lean_object* v___y_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg___lam__0(v_snd_1337_, v___y_1338_, v_a_x3f_1339_);
lean_dec(v_a_x3f_1339_);
lean_dec_ref(v___y_1338_);
lean_dec_ref(v_snd_1337_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg(lean_object* v_f_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_){
_start:
{
lean_object* v___x_1346_; 
v___x_1346_ = lean_io_create_tempfile();
if (lean_obj_tag(v___x_1346_) == 0)
{
lean_object* v_a_1347_; lean_object* v_fst_1348_; lean_object* v_snd_1349_; lean_object* v_r_1350_; 
v_a_1347_ = lean_ctor_get(v___x_1346_, 0);
lean_inc(v_a_1347_);
lean_dec_ref_known(v___x_1346_, 1);
v_fst_1348_ = lean_ctor_get(v_a_1347_, 0);
lean_inc(v_fst_1348_);
v_snd_1349_ = lean_ctor_get(v_a_1347_, 1);
lean_inc_n(v_snd_1349_, 2);
lean_dec(v_a_1347_);
lean_inc(v___y_1344_);
lean_inc_ref(v___y_1343_);
v_r_1350_ = lean_apply_5(v_f_1342_, v_fst_1348_, v_snd_1349_, v___y_1343_, v___y_1344_, lean_box(0));
if (lean_obj_tag(v_r_1350_) == 0)
{
lean_object* v_a_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1375_; 
v_a_1351_ = lean_ctor_get(v_r_1350_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v_r_1350_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1353_ = v_r_1350_;
v_isShared_1354_ = v_isSharedCheck_1375_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_a_1351_);
lean_dec(v_r_1350_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1375_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1356_; 
lean_inc(v_a_1351_);
if (v_isShared_1354_ == 0)
{
lean_ctor_set_tag(v___x_1353_, 1);
v___x_1356_ = v___x_1353_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_a_1351_);
v___x_1356_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
lean_object* v___x_1357_; 
v___x_1357_ = l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg___lam__0(v_snd_1349_, v___y_1343_, v___x_1356_);
lean_dec_ref(v___x_1356_);
lean_dec(v_snd_1349_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1364_; 
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1364_ == 0)
{
lean_object* v_unused_1365_; 
v_unused_1365_ = lean_ctor_get(v___x_1357_, 0);
lean_dec(v_unused_1365_);
v___x_1359_ = v___x_1357_;
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
else
{
lean_dec(v___x_1357_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1362_; 
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 0, v_a_1351_);
v___x_1362_ = v___x_1359_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_a_1351_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
}
else
{
lean_object* v_a_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1373_; 
lean_dec(v_a_1351_);
v_a_1366_ = lean_ctor_get(v___x_1357_, 0);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1368_ = v___x_1357_;
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_a_1366_);
lean_dec(v___x_1357_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v___x_1371_; 
if (v_isShared_1369_ == 0)
{
v___x_1371_ = v___x_1368_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_a_1366_);
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
else
{
lean_object* v_a_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; 
v_a_1376_ = lean_ctor_get(v_r_1350_, 0);
lean_inc(v_a_1376_);
lean_dec_ref_known(v_r_1350_, 1);
v___x_1377_ = lean_box(0);
v___x_1378_ = l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg___lam__0(v_snd_1349_, v___y_1343_, v___x_1377_);
lean_dec(v_snd_1349_);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1385_; 
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1385_ == 0)
{
lean_object* v_unused_1386_; 
v_unused_1386_ = lean_ctor_get(v___x_1378_, 0);
lean_dec(v_unused_1386_);
v___x_1380_ = v___x_1378_;
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
else
{
lean_dec(v___x_1378_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1383_; 
if (v_isShared_1381_ == 0)
{
lean_ctor_set_tag(v___x_1380_, 1);
lean_ctor_set(v___x_1380_, 0, v_a_1376_);
v___x_1383_ = v___x_1380_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_a_1376_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
}
else
{
lean_object* v_a_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1394_; 
lean_dec(v_a_1376_);
v_a_1387_ = lean_ctor_get(v___x_1378_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1389_ = v___x_1378_;
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_a_1387_);
lean_dec(v___x_1378_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1392_; 
if (v_isShared_1390_ == 0)
{
v___x_1392_ = v___x_1389_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_a_1387_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
}
}
else
{
lean_object* v_a_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1407_; 
lean_dec_ref(v_f_1342_);
v_a_1395_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1397_ = v___x_1346_;
v_isShared_1398_ = v_isSharedCheck_1407_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_a_1395_);
lean_dec(v___x_1346_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1407_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v_ref_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1405_; 
v_ref_1399_ = lean_ctor_get(v___y_1343_, 5);
v___x_1400_ = lean_io_error_to_string(v_a_1395_);
v___x_1401_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1401_, 0, v___x_1400_);
v___x_1402_ = l_Lean_MessageData_ofFormat(v___x_1401_);
lean_inc(v_ref_1399_);
v___x_1403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1403_, 0, v_ref_1399_);
lean_ctor_set(v___x_1403_, 1, v___x_1402_);
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 0, v___x_1403_);
v___x_1405_ = v___x_1397_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v___x_1403_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg___boxed(lean_object* v_f_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg(v_f_1408_, v___y_1409_, v___y_1410_);
lean_dec(v___y_1410_);
lean_dec_ref(v___y_1409_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3(lean_object* v_00_u03b1_1413_, lean_object* v_f_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
lean_object* v___x_1418_; 
v___x_1418_ = l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg(v_f_1414_, v___y_1415_, v___y_1416_);
return v___x_1418_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___boxed(lean_object* v_00_u03b1_1419_, lean_object* v_f_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3(v_00_u03b1_1419_, v_f_1420_, v___y_1421_, v___y_1422_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__0(lean_object* v_cnf_1425_, lean_object* v_x_1426_){
_start:
{
lean_object* v___x_1427_; 
v___x_1427_ = l_Std_Sat_CNF_dimacs(v_cnf_1425_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__0___boxed(lean_object* v_cnf_1428_, lean_object* v_x_1429_){
_start:
{
lean_object* v_res_1430_; 
v_res_1430_ = l_Lean_Meta_Tactic_BVDecide_runExternal___lam__0(v_cnf_1428_, v_x_1429_);
lean_dec_ref(v_cnf_1428_);
return v_res_1430_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1434_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1___closed__1));
v___x_1435_ = l_Lean_MessageData_ofFormat(v___x_1434_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1(lean_object* v_x_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_){
_start:
{
lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1440_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1___closed__2, &l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1___closed__2);
v___x_1441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1440_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1___boxed(lean_object* v_x_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1(v_x_1442_, v___y_1443_, v___y_1444_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
lean_dec_ref(v_x_1442_);
return v_res_1446_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2___closed__2(void){
_start:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1450_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2___closed__1));
v___x_1451_ = l_Lean_MessageData_ofFormat(v___x_1450_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2(lean_object* v_x_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_){
_start:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1456_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2___closed__2, &l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2___closed__2);
v___x_1457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1456_);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2___boxed(lean_object* v_x_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_){
_start:
{
lean_object* v_res_1462_; 
v_res_1462_ = l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2(v_x_1458_, v___y_1459_, v___y_1460_);
lean_dec(v___y_1460_);
lean_dec_ref(v___y_1459_);
lean_dec_ref(v_x_1458_);
return v_res_1462_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3___closed__2(void){
_start:
{
lean_object* v___x_1466_; lean_object* v___x_1467_; 
v___x_1466_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3___closed__1));
v___x_1467_ = l_Lean_MessageData_ofFormat(v___x_1466_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3(lean_object* v_x_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_){
_start:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1472_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3___closed__2, &l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3___closed__2);
v___x_1473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1472_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3___boxed(lean_object* v_x_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_){
_start:
{
lean_object* v_res_1478_; 
v_res_1478_ = l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3(v_x_1474_, v___y_1475_, v___y_1476_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
lean_dec_ref(v_x_1474_);
return v_res_1478_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2_spec__4(lean_object* v_e_1479_){
_start:
{
if (lean_obj_tag(v_e_1479_) == 0)
{
uint8_t v___x_1480_; 
v___x_1480_ = 2;
return v___x_1480_;
}
else
{
uint8_t v___x_1481_; 
v___x_1481_ = 0;
return v___x_1481_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2_spec__4___boxed(lean_object* v_e_1482_){
_start:
{
uint8_t v_res_1483_; lean_object* v_r_1484_; 
v_res_1483_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2_spec__4(v_e_1482_);
lean_dec_ref(v_e_1482_);
v_r_1484_ = lean_box(v_res_1483_);
return v_r_1484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2(lean_object* v_cls_1485_, uint8_t v_collapsed_1486_, lean_object* v_tag_1487_, lean_object* v_opts_1488_, uint8_t v_clsEnabled_1489_, lean_object* v_oldTraces_1490_, lean_object* v_msg_1491_, lean_object* v_resStartStop_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_){
_start:
{
lean_object* v_fst_1496_; lean_object* v_snd_1497_; lean_object* v___y_1499_; lean_object* v___y_1500_; lean_object* v_data_1501_; lean_object* v_fst_1504_; lean_object* v_snd_1505_; lean_object* v___x_1506_; uint8_t v___x_1507_; lean_object* v___y_1509_; lean_object* v_a_1510_; uint8_t v___y_1525_; double v___y_1556_; 
v_fst_1496_ = lean_ctor_get(v_resStartStop_1492_, 0);
lean_inc(v_fst_1496_);
v_snd_1497_ = lean_ctor_get(v_resStartStop_1492_, 1);
lean_inc(v_snd_1497_);
lean_dec_ref(v_resStartStop_1492_);
v_fst_1504_ = lean_ctor_get(v_snd_1497_, 0);
lean_inc(v_fst_1504_);
v_snd_1505_ = lean_ctor_get(v_snd_1497_, 1);
lean_inc(v_snd_1505_);
lean_dec(v_snd_1497_);
v___x_1506_ = l_Lean_trace_profiler;
v___x_1507_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_opts_1488_, v___x_1506_);
if (v___x_1507_ == 0)
{
v___y_1525_ = v___x_1507_;
goto v___jp_1524_;
}
else
{
lean_object* v___x_1561_; uint8_t v___x_1562_; 
v___x_1561_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1562_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_opts_1488_, v___x_1561_);
if (v___x_1562_ == 0)
{
lean_object* v___x_1563_; lean_object* v___x_1564_; double v___x_1565_; double v___x_1566_; double v___x_1567_; 
v___x_1563_ = l_Lean_trace_profiler_threshold;
v___x_1564_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(v_opts_1488_, v___x_1563_);
v___x_1565_ = lean_float_of_nat(v___x_1564_);
v___x_1566_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3);
v___x_1567_ = lean_float_div(v___x_1565_, v___x_1566_);
v___y_1556_ = v___x_1567_;
goto v___jp_1555_;
}
else
{
lean_object* v___x_1568_; lean_object* v___x_1569_; double v___x_1570_; 
v___x_1568_ = l_Lean_trace_profiler_threshold;
v___x_1569_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(v_opts_1488_, v___x_1568_);
v___x_1570_ = lean_float_of_nat(v___x_1569_);
v___y_1556_ = v___x_1570_;
goto v___jp_1555_;
}
}
v___jp_1498_:
{
lean_object* v___x_1502_; 
lean_inc(v___y_1499_);
v___x_1502_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__4(v_oldTraces_1490_, v_data_1501_, v___y_1499_, v___y_1500_, v___y_1493_, v___y_1494_);
if (lean_obj_tag(v___x_1502_) == 0)
{
lean_object* v___x_1503_; 
lean_dec_ref_known(v___x_1502_, 1);
v___x_1503_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5___redArg(v_fst_1496_);
return v___x_1503_;
}
else
{
lean_dec(v_fst_1496_);
return v___x_1502_;
}
}
v___jp_1508_:
{
uint8_t v_result_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; double v___x_1514_; lean_object* v_data_1515_; 
v_result_1511_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2_spec__4(v_fst_1496_);
v___x_1512_ = lean_box(v_result_1511_);
v___x_1513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1513_, 0, v___x_1512_);
v___x_1514_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0);
lean_inc_ref(v_tag_1487_);
lean_inc_ref(v___x_1513_);
lean_inc(v_cls_1485_);
v_data_1515_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1515_, 0, v_cls_1485_);
lean_ctor_set(v_data_1515_, 1, v___x_1513_);
lean_ctor_set(v_data_1515_, 2, v_tag_1487_);
lean_ctor_set_float(v_data_1515_, sizeof(void*)*3, v___x_1514_);
lean_ctor_set_float(v_data_1515_, sizeof(void*)*3 + 8, v___x_1514_);
lean_ctor_set_uint8(v_data_1515_, sizeof(void*)*3 + 16, v_collapsed_1486_);
if (v___x_1507_ == 0)
{
lean_dec_ref_known(v___x_1513_, 1);
lean_dec(v_snd_1505_);
lean_dec(v_fst_1504_);
lean_dec_ref(v_tag_1487_);
lean_dec(v_cls_1485_);
v___y_1499_ = v___y_1509_;
v___y_1500_ = v_a_1510_;
v_data_1501_ = v_data_1515_;
goto v___jp_1498_;
}
else
{
lean_object* v_data_1516_; double v___x_1517_; double v___x_1518_; 
lean_dec_ref_known(v_data_1515_, 3);
v_data_1516_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1516_, 0, v_cls_1485_);
lean_ctor_set(v_data_1516_, 1, v___x_1513_);
lean_ctor_set(v_data_1516_, 2, v_tag_1487_);
v___x_1517_ = lean_unbox_float(v_fst_1504_);
lean_dec(v_fst_1504_);
lean_ctor_set_float(v_data_1516_, sizeof(void*)*3, v___x_1517_);
v___x_1518_ = lean_unbox_float(v_snd_1505_);
lean_dec(v_snd_1505_);
lean_ctor_set_float(v_data_1516_, sizeof(void*)*3 + 8, v___x_1518_);
lean_ctor_set_uint8(v_data_1516_, sizeof(void*)*3 + 16, v_collapsed_1486_);
v___y_1499_ = v___y_1509_;
v___y_1500_ = v_a_1510_;
v_data_1501_ = v_data_1516_;
goto v___jp_1498_;
}
}
v___jp_1519_:
{
lean_object* v_ref_1520_; lean_object* v___x_1521_; 
v_ref_1520_ = lean_ctor_get(v___y_1493_, 5);
lean_inc(v___y_1494_);
lean_inc_ref(v___y_1493_);
lean_inc(v_fst_1496_);
v___x_1521_ = lean_apply_4(v_msg_1491_, v_fst_1496_, v___y_1493_, v___y_1494_, lean_box(0));
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_object* v_a_1522_; 
v_a_1522_ = lean_ctor_get(v___x_1521_, 0);
lean_inc(v_a_1522_);
lean_dec_ref_known(v___x_1521_, 1);
v___y_1509_ = v_ref_1520_;
v_a_1510_ = v_a_1522_;
goto v___jp_1508_;
}
else
{
lean_object* v___x_1523_; 
lean_dec_ref_known(v___x_1521_, 1);
v___x_1523_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2);
v___y_1509_ = v_ref_1520_;
v_a_1510_ = v___x_1523_;
goto v___jp_1508_;
}
}
v___jp_1524_:
{
if (v_clsEnabled_1489_ == 0)
{
if (v___y_1525_ == 0)
{
lean_object* v___x_1526_; lean_object* v_traceState_1527_; lean_object* v_env_1528_; lean_object* v_nextMacroScope_1529_; lean_object* v_ngen_1530_; lean_object* v_auxDeclNGen_1531_; lean_object* v_cache_1532_; lean_object* v_messages_1533_; lean_object* v_infoState_1534_; lean_object* v_snapshotTasks_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1554_; 
lean_dec(v_snd_1505_);
lean_dec(v_fst_1504_);
lean_dec_ref(v_msg_1491_);
lean_dec_ref(v_tag_1487_);
lean_dec(v_cls_1485_);
v___x_1526_ = lean_st_ref_take(v___y_1494_);
v_traceState_1527_ = lean_ctor_get(v___x_1526_, 4);
v_env_1528_ = lean_ctor_get(v___x_1526_, 0);
v_nextMacroScope_1529_ = lean_ctor_get(v___x_1526_, 1);
v_ngen_1530_ = lean_ctor_get(v___x_1526_, 2);
v_auxDeclNGen_1531_ = lean_ctor_get(v___x_1526_, 3);
v_cache_1532_ = lean_ctor_get(v___x_1526_, 5);
v_messages_1533_ = lean_ctor_get(v___x_1526_, 6);
v_infoState_1534_ = lean_ctor_get(v___x_1526_, 7);
v_snapshotTasks_1535_ = lean_ctor_get(v___x_1526_, 8);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1526_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1537_ = v___x_1526_;
v_isShared_1538_ = v_isSharedCheck_1554_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_snapshotTasks_1535_);
lean_inc(v_infoState_1534_);
lean_inc(v_messages_1533_);
lean_inc(v_cache_1532_);
lean_inc(v_traceState_1527_);
lean_inc(v_auxDeclNGen_1531_);
lean_inc(v_ngen_1530_);
lean_inc(v_nextMacroScope_1529_);
lean_inc(v_env_1528_);
lean_dec(v___x_1526_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1554_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
uint64_t v_tid_1539_; lean_object* v_traces_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1553_; 
v_tid_1539_ = lean_ctor_get_uint64(v_traceState_1527_, sizeof(void*)*1);
v_traces_1540_ = lean_ctor_get(v_traceState_1527_, 0);
v_isSharedCheck_1553_ = !lean_is_exclusive(v_traceState_1527_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1542_ = v_traceState_1527_;
v_isShared_1543_ = v_isSharedCheck_1553_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_traces_1540_);
lean_dec(v_traceState_1527_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1553_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v___x_1544_; lean_object* v___x_1546_; 
v___x_1544_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1490_, v_traces_1540_);
lean_dec_ref(v_traces_1540_);
if (v_isShared_1543_ == 0)
{
lean_ctor_set(v___x_1542_, 0, v___x_1544_);
v___x_1546_ = v___x_1542_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v___x_1544_);
lean_ctor_set_uint64(v_reuseFailAlloc_1552_, sizeof(void*)*1, v_tid_1539_);
v___x_1546_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
lean_object* v___x_1548_; 
if (v_isShared_1538_ == 0)
{
lean_ctor_set(v___x_1537_, 4, v___x_1546_);
v___x_1548_ = v___x_1537_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v_env_1528_);
lean_ctor_set(v_reuseFailAlloc_1551_, 1, v_nextMacroScope_1529_);
lean_ctor_set(v_reuseFailAlloc_1551_, 2, v_ngen_1530_);
lean_ctor_set(v_reuseFailAlloc_1551_, 3, v_auxDeclNGen_1531_);
lean_ctor_set(v_reuseFailAlloc_1551_, 4, v___x_1546_);
lean_ctor_set(v_reuseFailAlloc_1551_, 5, v_cache_1532_);
lean_ctor_set(v_reuseFailAlloc_1551_, 6, v_messages_1533_);
lean_ctor_set(v_reuseFailAlloc_1551_, 7, v_infoState_1534_);
lean_ctor_set(v_reuseFailAlloc_1551_, 8, v_snapshotTasks_1535_);
v___x_1548_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1549_ = lean_st_ref_set(v___y_1494_, v___x_1548_);
v___x_1550_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5___redArg(v_fst_1496_);
return v___x_1550_;
}
}
}
}
}
else
{
goto v___jp_1519_;
}
}
else
{
goto v___jp_1519_;
}
}
v___jp_1555_:
{
double v___x_1557_; double v___x_1558_; double v___x_1559_; uint8_t v___x_1560_; 
v___x_1557_ = lean_unbox_float(v_snd_1505_);
v___x_1558_ = lean_unbox_float(v_fst_1504_);
v___x_1559_ = lean_float_sub(v___x_1557_, v___x_1558_);
v___x_1560_ = lean_float_decLt(v___y_1556_, v___x_1559_);
v___y_1525_ = v___x_1560_;
goto v___jp_1524_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2___boxed(lean_object* v_cls_1571_, lean_object* v_collapsed_1572_, lean_object* v_tag_1573_, lean_object* v_opts_1574_, lean_object* v_clsEnabled_1575_, lean_object* v_oldTraces_1576_, lean_object* v_msg_1577_, lean_object* v_resStartStop_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_){
_start:
{
uint8_t v_collapsed_boxed_1582_; uint8_t v_clsEnabled_boxed_1583_; lean_object* v_res_1584_; 
v_collapsed_boxed_1582_ = lean_unbox(v_collapsed_1572_);
v_clsEnabled_boxed_1583_ = lean_unbox(v_clsEnabled_1575_);
v_res_1584_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2(v_cls_1571_, v_collapsed_boxed_1582_, v_tag_1573_, v_opts_1574_, v_clsEnabled_boxed_1583_, v_oldTraces_1576_, v_msg_1577_, v_resStartStop_1578_, v___y_1579_, v___y_1580_);
lean_dec(v___y_1580_);
lean_dec_ref(v___y_1579_);
lean_dec_ref(v_opts_1574_);
return v_res_1584_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0_spec__0(lean_object* v_e_1585_){
_start:
{
if (lean_obj_tag(v_e_1585_) == 0)
{
uint8_t v___x_1586_; 
v___x_1586_ = 2;
return v___x_1586_;
}
else
{
uint8_t v___x_1587_; 
v___x_1587_ = 0;
return v___x_1587_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0_spec__0___boxed(lean_object* v_e_1588_){
_start:
{
uint8_t v_res_1589_; lean_object* v_r_1590_; 
v_res_1589_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0_spec__0(v_e_1588_);
lean_dec_ref(v_e_1588_);
v_r_1590_ = lean_box(v_res_1589_);
return v_r_1590_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0(lean_object* v_cls_1591_, uint8_t v_collapsed_1592_, lean_object* v_tag_1593_, lean_object* v_opts_1594_, uint8_t v_clsEnabled_1595_, lean_object* v_oldTraces_1596_, lean_object* v_msg_1597_, lean_object* v_resStartStop_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_){
_start:
{
lean_object* v_fst_1602_; lean_object* v_snd_1603_; lean_object* v___y_1605_; lean_object* v___y_1606_; lean_object* v_data_1607_; lean_object* v_fst_1618_; lean_object* v_snd_1619_; lean_object* v___x_1620_; uint8_t v___x_1621_; lean_object* v___y_1623_; lean_object* v_a_1624_; uint8_t v___y_1639_; double v___y_1670_; 
v_fst_1602_ = lean_ctor_get(v_resStartStop_1598_, 0);
lean_inc(v_fst_1602_);
v_snd_1603_ = lean_ctor_get(v_resStartStop_1598_, 1);
lean_inc(v_snd_1603_);
lean_dec_ref(v_resStartStop_1598_);
v_fst_1618_ = lean_ctor_get(v_snd_1603_, 0);
lean_inc(v_fst_1618_);
v_snd_1619_ = lean_ctor_get(v_snd_1603_, 1);
lean_inc(v_snd_1619_);
lean_dec(v_snd_1603_);
v___x_1620_ = l_Lean_trace_profiler;
v___x_1621_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_opts_1594_, v___x_1620_);
if (v___x_1621_ == 0)
{
v___y_1639_ = v___x_1621_;
goto v___jp_1638_;
}
else
{
lean_object* v___x_1675_; uint8_t v___x_1676_; 
v___x_1675_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1676_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_opts_1594_, v___x_1675_);
if (v___x_1676_ == 0)
{
lean_object* v___x_1677_; lean_object* v___x_1678_; double v___x_1679_; double v___x_1680_; double v___x_1681_; 
v___x_1677_ = l_Lean_trace_profiler_threshold;
v___x_1678_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(v_opts_1594_, v___x_1677_);
v___x_1679_ = lean_float_of_nat(v___x_1678_);
v___x_1680_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3);
v___x_1681_ = lean_float_div(v___x_1679_, v___x_1680_);
v___y_1670_ = v___x_1681_;
goto v___jp_1669_;
}
else
{
lean_object* v___x_1682_; lean_object* v___x_1683_; double v___x_1684_; 
v___x_1682_ = l_Lean_trace_profiler_threshold;
v___x_1683_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(v_opts_1594_, v___x_1682_);
v___x_1684_ = lean_float_of_nat(v___x_1683_);
v___y_1670_ = v___x_1684_;
goto v___jp_1669_;
}
}
v___jp_1604_:
{
lean_object* v___x_1608_; 
lean_inc(v___y_1605_);
v___x_1608_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__4(v_oldTraces_1596_, v_data_1607_, v___y_1605_, v___y_1606_, v___y_1599_, v___y_1600_);
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_object* v___x_1609_; 
lean_dec_ref_known(v___x_1608_, 1);
v___x_1609_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5___redArg(v_fst_1602_);
return v___x_1609_;
}
else
{
lean_object* v_a_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1617_; 
lean_dec(v_fst_1602_);
v_a_1610_ = lean_ctor_get(v___x_1608_, 0);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1612_ = v___x_1608_;
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_a_1610_);
lean_dec(v___x_1608_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v___x_1615_; 
if (v_isShared_1613_ == 0)
{
v___x_1615_ = v___x_1612_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_a_1610_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
}
}
v___jp_1622_:
{
uint8_t v_result_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; double v___x_1628_; lean_object* v_data_1629_; 
v_result_1625_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0_spec__0(v_fst_1602_);
v___x_1626_ = lean_box(v_result_1625_);
v___x_1627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1626_);
v___x_1628_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0);
lean_inc_ref(v_tag_1593_);
lean_inc_ref(v___x_1627_);
lean_inc(v_cls_1591_);
v_data_1629_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1629_, 0, v_cls_1591_);
lean_ctor_set(v_data_1629_, 1, v___x_1627_);
lean_ctor_set(v_data_1629_, 2, v_tag_1593_);
lean_ctor_set_float(v_data_1629_, sizeof(void*)*3, v___x_1628_);
lean_ctor_set_float(v_data_1629_, sizeof(void*)*3 + 8, v___x_1628_);
lean_ctor_set_uint8(v_data_1629_, sizeof(void*)*3 + 16, v_collapsed_1592_);
if (v___x_1621_ == 0)
{
lean_dec_ref_known(v___x_1627_, 1);
lean_dec(v_snd_1619_);
lean_dec(v_fst_1618_);
lean_dec_ref(v_tag_1593_);
lean_dec(v_cls_1591_);
v___y_1605_ = v___y_1623_;
v___y_1606_ = v_a_1624_;
v_data_1607_ = v_data_1629_;
goto v___jp_1604_;
}
else
{
lean_object* v_data_1630_; double v___x_1631_; double v___x_1632_; 
lean_dec_ref_known(v_data_1629_, 3);
v_data_1630_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1630_, 0, v_cls_1591_);
lean_ctor_set(v_data_1630_, 1, v___x_1627_);
lean_ctor_set(v_data_1630_, 2, v_tag_1593_);
v___x_1631_ = lean_unbox_float(v_fst_1618_);
lean_dec(v_fst_1618_);
lean_ctor_set_float(v_data_1630_, sizeof(void*)*3, v___x_1631_);
v___x_1632_ = lean_unbox_float(v_snd_1619_);
lean_dec(v_snd_1619_);
lean_ctor_set_float(v_data_1630_, sizeof(void*)*3 + 8, v___x_1632_);
lean_ctor_set_uint8(v_data_1630_, sizeof(void*)*3 + 16, v_collapsed_1592_);
v___y_1605_ = v___y_1623_;
v___y_1606_ = v_a_1624_;
v_data_1607_ = v_data_1630_;
goto v___jp_1604_;
}
}
v___jp_1633_:
{
lean_object* v_ref_1634_; lean_object* v___x_1635_; 
v_ref_1634_ = lean_ctor_get(v___y_1599_, 5);
lean_inc(v___y_1600_);
lean_inc_ref(v___y_1599_);
lean_inc(v_fst_1602_);
v___x_1635_ = lean_apply_4(v_msg_1597_, v_fst_1602_, v___y_1599_, v___y_1600_, lean_box(0));
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_object* v_a_1636_; 
v_a_1636_ = lean_ctor_get(v___x_1635_, 0);
lean_inc(v_a_1636_);
lean_dec_ref_known(v___x_1635_, 1);
v___y_1623_ = v_ref_1634_;
v_a_1624_ = v_a_1636_;
goto v___jp_1622_;
}
else
{
lean_object* v___x_1637_; 
lean_dec_ref_known(v___x_1635_, 1);
v___x_1637_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2);
v___y_1623_ = v_ref_1634_;
v_a_1624_ = v___x_1637_;
goto v___jp_1622_;
}
}
v___jp_1638_:
{
if (v_clsEnabled_1595_ == 0)
{
if (v___y_1639_ == 0)
{
lean_object* v___x_1640_; lean_object* v_traceState_1641_; lean_object* v_env_1642_; lean_object* v_nextMacroScope_1643_; lean_object* v_ngen_1644_; lean_object* v_auxDeclNGen_1645_; lean_object* v_cache_1646_; lean_object* v_messages_1647_; lean_object* v_infoState_1648_; lean_object* v_snapshotTasks_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1668_; 
lean_dec(v_snd_1619_);
lean_dec(v_fst_1618_);
lean_dec_ref(v_msg_1597_);
lean_dec_ref(v_tag_1593_);
lean_dec(v_cls_1591_);
v___x_1640_ = lean_st_ref_take(v___y_1600_);
v_traceState_1641_ = lean_ctor_get(v___x_1640_, 4);
v_env_1642_ = lean_ctor_get(v___x_1640_, 0);
v_nextMacroScope_1643_ = lean_ctor_get(v___x_1640_, 1);
v_ngen_1644_ = lean_ctor_get(v___x_1640_, 2);
v_auxDeclNGen_1645_ = lean_ctor_get(v___x_1640_, 3);
v_cache_1646_ = lean_ctor_get(v___x_1640_, 5);
v_messages_1647_ = lean_ctor_get(v___x_1640_, 6);
v_infoState_1648_ = lean_ctor_get(v___x_1640_, 7);
v_snapshotTasks_1649_ = lean_ctor_get(v___x_1640_, 8);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1640_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1651_ = v___x_1640_;
v_isShared_1652_ = v_isSharedCheck_1668_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_snapshotTasks_1649_);
lean_inc(v_infoState_1648_);
lean_inc(v_messages_1647_);
lean_inc(v_cache_1646_);
lean_inc(v_traceState_1641_);
lean_inc(v_auxDeclNGen_1645_);
lean_inc(v_ngen_1644_);
lean_inc(v_nextMacroScope_1643_);
lean_inc(v_env_1642_);
lean_dec(v___x_1640_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1668_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
uint64_t v_tid_1653_; lean_object* v_traces_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1667_; 
v_tid_1653_ = lean_ctor_get_uint64(v_traceState_1641_, sizeof(void*)*1);
v_traces_1654_ = lean_ctor_get(v_traceState_1641_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v_traceState_1641_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1656_ = v_traceState_1641_;
v_isShared_1657_ = v_isSharedCheck_1667_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_traces_1654_);
lean_dec(v_traceState_1641_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1667_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1658_; lean_object* v___x_1660_; 
v___x_1658_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1596_, v_traces_1654_);
lean_dec_ref(v_traces_1654_);
if (v_isShared_1657_ == 0)
{
lean_ctor_set(v___x_1656_, 0, v___x_1658_);
v___x_1660_ = v___x_1656_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v___x_1658_);
lean_ctor_set_uint64(v_reuseFailAlloc_1666_, sizeof(void*)*1, v_tid_1653_);
v___x_1660_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
lean_object* v___x_1662_; 
if (v_isShared_1652_ == 0)
{
lean_ctor_set(v___x_1651_, 4, v___x_1660_);
v___x_1662_ = v___x_1651_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_env_1642_);
lean_ctor_set(v_reuseFailAlloc_1665_, 1, v_nextMacroScope_1643_);
lean_ctor_set(v_reuseFailAlloc_1665_, 2, v_ngen_1644_);
lean_ctor_set(v_reuseFailAlloc_1665_, 3, v_auxDeclNGen_1645_);
lean_ctor_set(v_reuseFailAlloc_1665_, 4, v___x_1660_);
lean_ctor_set(v_reuseFailAlloc_1665_, 5, v_cache_1646_);
lean_ctor_set(v_reuseFailAlloc_1665_, 6, v_messages_1647_);
lean_ctor_set(v_reuseFailAlloc_1665_, 7, v_infoState_1648_);
lean_ctor_set(v_reuseFailAlloc_1665_, 8, v_snapshotTasks_1649_);
v___x_1662_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
lean_object* v___x_1663_; lean_object* v___x_1664_; 
v___x_1663_ = lean_st_ref_set(v___y_1600_, v___x_1662_);
v___x_1664_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5___redArg(v_fst_1602_);
return v___x_1664_;
}
}
}
}
}
else
{
goto v___jp_1633_;
}
}
else
{
goto v___jp_1633_;
}
}
v___jp_1669_:
{
double v___x_1671_; double v___x_1672_; double v___x_1673_; uint8_t v___x_1674_; 
v___x_1671_ = lean_unbox_float(v_snd_1619_);
v___x_1672_ = lean_unbox_float(v_fst_1618_);
v___x_1673_ = lean_float_sub(v___x_1671_, v___x_1672_);
v___x_1674_ = lean_float_decLt(v___y_1670_, v___x_1673_);
v___y_1639_ = v___x_1674_;
goto v___jp_1638_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0___boxed(lean_object* v_cls_1685_, lean_object* v_collapsed_1686_, lean_object* v_tag_1687_, lean_object* v_opts_1688_, lean_object* v_clsEnabled_1689_, lean_object* v_oldTraces_1690_, lean_object* v_msg_1691_, lean_object* v_resStartStop_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_){
_start:
{
uint8_t v_collapsed_boxed_1696_; uint8_t v_clsEnabled_boxed_1697_; lean_object* v_res_1698_; 
v_collapsed_boxed_1696_ = lean_unbox(v_collapsed_1686_);
v_clsEnabled_boxed_1697_ = lean_unbox(v_clsEnabled_1689_);
v_res_1698_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0(v_cls_1685_, v_collapsed_boxed_1696_, v_tag_1687_, v_opts_1688_, v_clsEnabled_boxed_1697_, v_oldTraces_1690_, v_msg_1691_, v_resStartStop_1692_, v___y_1693_, v___y_1694_);
lean_dec(v___y_1694_);
lean_dec_ref(v___y_1693_);
lean_dec_ref(v_opts_1688_);
return v_res_1698_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1_spec__2(lean_object* v_e_1699_){
_start:
{
if (lean_obj_tag(v_e_1699_) == 0)
{
uint8_t v___x_1700_; 
v___x_1700_ = 2;
return v___x_1700_;
}
else
{
uint8_t v___x_1701_; 
v___x_1701_ = 0;
return v___x_1701_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1_spec__2___boxed(lean_object* v_e_1702_){
_start:
{
uint8_t v_res_1703_; lean_object* v_r_1704_; 
v_res_1703_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1_spec__2(v_e_1702_);
lean_dec_ref(v_e_1702_);
v_r_1704_ = lean_box(v_res_1703_);
return v_r_1704_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1(lean_object* v_cls_1705_, uint8_t v_collapsed_1706_, lean_object* v_tag_1707_, lean_object* v_opts_1708_, uint8_t v_clsEnabled_1709_, lean_object* v_oldTraces_1710_, lean_object* v_msg_1711_, lean_object* v_resStartStop_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_){
_start:
{
lean_object* v_fst_1716_; lean_object* v_snd_1717_; lean_object* v___y_1719_; lean_object* v___y_1720_; lean_object* v_data_1721_; lean_object* v_fst_1732_; lean_object* v_snd_1733_; lean_object* v___x_1734_; uint8_t v___x_1735_; lean_object* v___y_1737_; lean_object* v_a_1738_; uint8_t v___y_1753_; double v___y_1784_; 
v_fst_1716_ = lean_ctor_get(v_resStartStop_1712_, 0);
lean_inc(v_fst_1716_);
v_snd_1717_ = lean_ctor_get(v_resStartStop_1712_, 1);
lean_inc(v_snd_1717_);
lean_dec_ref(v_resStartStop_1712_);
v_fst_1732_ = lean_ctor_get(v_snd_1717_, 0);
lean_inc(v_fst_1732_);
v_snd_1733_ = lean_ctor_get(v_snd_1717_, 1);
lean_inc(v_snd_1733_);
lean_dec(v_snd_1717_);
v___x_1734_ = l_Lean_trace_profiler;
v___x_1735_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_opts_1708_, v___x_1734_);
if (v___x_1735_ == 0)
{
v___y_1753_ = v___x_1735_;
goto v___jp_1752_;
}
else
{
lean_object* v___x_1789_; uint8_t v___x_1790_; 
v___x_1789_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1790_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_opts_1708_, v___x_1789_);
if (v___x_1790_ == 0)
{
lean_object* v___x_1791_; lean_object* v___x_1792_; double v___x_1793_; double v___x_1794_; double v___x_1795_; 
v___x_1791_ = l_Lean_trace_profiler_threshold;
v___x_1792_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(v_opts_1708_, v___x_1791_);
v___x_1793_ = lean_float_of_nat(v___x_1792_);
v___x_1794_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3);
v___x_1795_ = lean_float_div(v___x_1793_, v___x_1794_);
v___y_1784_ = v___x_1795_;
goto v___jp_1783_;
}
else
{
lean_object* v___x_1796_; lean_object* v___x_1797_; double v___x_1798_; 
v___x_1796_ = l_Lean_trace_profiler_threshold;
v___x_1797_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(v_opts_1708_, v___x_1796_);
v___x_1798_ = lean_float_of_nat(v___x_1797_);
v___y_1784_ = v___x_1798_;
goto v___jp_1783_;
}
}
v___jp_1718_:
{
lean_object* v___x_1722_; 
lean_inc(v___y_1719_);
v___x_1722_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__4(v_oldTraces_1710_, v_data_1721_, v___y_1719_, v___y_1720_, v___y_1713_, v___y_1714_);
if (lean_obj_tag(v___x_1722_) == 0)
{
lean_object* v___x_1723_; 
lean_dec_ref_known(v___x_1722_, 1);
v___x_1723_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5___redArg(v_fst_1716_);
return v___x_1723_;
}
else
{
lean_object* v_a_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1731_; 
lean_dec(v_fst_1716_);
v_a_1724_ = lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1726_ = v___x_1722_;
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_a_1724_);
lean_dec(v___x_1722_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1729_; 
if (v_isShared_1727_ == 0)
{
v___x_1729_ = v___x_1726_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_a_1724_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
}
}
v___jp_1736_:
{
uint8_t v_result_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; double v___x_1742_; lean_object* v_data_1743_; 
v_result_1739_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1_spec__2(v_fst_1716_);
v___x_1740_ = lean_box(v_result_1739_);
v___x_1741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1741_, 0, v___x_1740_);
v___x_1742_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0);
lean_inc_ref(v_tag_1707_);
lean_inc_ref(v___x_1741_);
lean_inc(v_cls_1705_);
v_data_1743_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1743_, 0, v_cls_1705_);
lean_ctor_set(v_data_1743_, 1, v___x_1741_);
lean_ctor_set(v_data_1743_, 2, v_tag_1707_);
lean_ctor_set_float(v_data_1743_, sizeof(void*)*3, v___x_1742_);
lean_ctor_set_float(v_data_1743_, sizeof(void*)*3 + 8, v___x_1742_);
lean_ctor_set_uint8(v_data_1743_, sizeof(void*)*3 + 16, v_collapsed_1706_);
if (v___x_1735_ == 0)
{
lean_dec_ref_known(v___x_1741_, 1);
lean_dec(v_snd_1733_);
lean_dec(v_fst_1732_);
lean_dec_ref(v_tag_1707_);
lean_dec(v_cls_1705_);
v___y_1719_ = v___y_1737_;
v___y_1720_ = v_a_1738_;
v_data_1721_ = v_data_1743_;
goto v___jp_1718_;
}
else
{
lean_object* v_data_1744_; double v___x_1745_; double v___x_1746_; 
lean_dec_ref_known(v_data_1743_, 3);
v_data_1744_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1744_, 0, v_cls_1705_);
lean_ctor_set(v_data_1744_, 1, v___x_1741_);
lean_ctor_set(v_data_1744_, 2, v_tag_1707_);
v___x_1745_ = lean_unbox_float(v_fst_1732_);
lean_dec(v_fst_1732_);
lean_ctor_set_float(v_data_1744_, sizeof(void*)*3, v___x_1745_);
v___x_1746_ = lean_unbox_float(v_snd_1733_);
lean_dec(v_snd_1733_);
lean_ctor_set_float(v_data_1744_, sizeof(void*)*3 + 8, v___x_1746_);
lean_ctor_set_uint8(v_data_1744_, sizeof(void*)*3 + 16, v_collapsed_1706_);
v___y_1719_ = v___y_1737_;
v___y_1720_ = v_a_1738_;
v_data_1721_ = v_data_1744_;
goto v___jp_1718_;
}
}
v___jp_1747_:
{
lean_object* v_ref_1748_; lean_object* v___x_1749_; 
v_ref_1748_ = lean_ctor_get(v___y_1713_, 5);
lean_inc(v___y_1714_);
lean_inc_ref(v___y_1713_);
lean_inc(v_fst_1716_);
v___x_1749_ = lean_apply_4(v_msg_1711_, v_fst_1716_, v___y_1713_, v___y_1714_, lean_box(0));
if (lean_obj_tag(v___x_1749_) == 0)
{
lean_object* v_a_1750_; 
v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
lean_inc(v_a_1750_);
lean_dec_ref_known(v___x_1749_, 1);
v___y_1737_ = v_ref_1748_;
v_a_1738_ = v_a_1750_;
goto v___jp_1736_;
}
else
{
lean_object* v___x_1751_; 
lean_dec_ref_known(v___x_1749_, 1);
v___x_1751_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2);
v___y_1737_ = v_ref_1748_;
v_a_1738_ = v___x_1751_;
goto v___jp_1736_;
}
}
v___jp_1752_:
{
if (v_clsEnabled_1709_ == 0)
{
if (v___y_1753_ == 0)
{
lean_object* v___x_1754_; lean_object* v_traceState_1755_; lean_object* v_env_1756_; lean_object* v_nextMacroScope_1757_; lean_object* v_ngen_1758_; lean_object* v_auxDeclNGen_1759_; lean_object* v_cache_1760_; lean_object* v_messages_1761_; lean_object* v_infoState_1762_; lean_object* v_snapshotTasks_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1782_; 
lean_dec(v_snd_1733_);
lean_dec(v_fst_1732_);
lean_dec_ref(v_msg_1711_);
lean_dec_ref(v_tag_1707_);
lean_dec(v_cls_1705_);
v___x_1754_ = lean_st_ref_take(v___y_1714_);
v_traceState_1755_ = lean_ctor_get(v___x_1754_, 4);
v_env_1756_ = lean_ctor_get(v___x_1754_, 0);
v_nextMacroScope_1757_ = lean_ctor_get(v___x_1754_, 1);
v_ngen_1758_ = lean_ctor_get(v___x_1754_, 2);
v_auxDeclNGen_1759_ = lean_ctor_get(v___x_1754_, 3);
v_cache_1760_ = lean_ctor_get(v___x_1754_, 5);
v_messages_1761_ = lean_ctor_get(v___x_1754_, 6);
v_infoState_1762_ = lean_ctor_get(v___x_1754_, 7);
v_snapshotTasks_1763_ = lean_ctor_get(v___x_1754_, 8);
v_isSharedCheck_1782_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1765_ = v___x_1754_;
v_isShared_1766_ = v_isSharedCheck_1782_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_snapshotTasks_1763_);
lean_inc(v_infoState_1762_);
lean_inc(v_messages_1761_);
lean_inc(v_cache_1760_);
lean_inc(v_traceState_1755_);
lean_inc(v_auxDeclNGen_1759_);
lean_inc(v_ngen_1758_);
lean_inc(v_nextMacroScope_1757_);
lean_inc(v_env_1756_);
lean_dec(v___x_1754_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1782_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
uint64_t v_tid_1767_; lean_object* v_traces_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1781_; 
v_tid_1767_ = lean_ctor_get_uint64(v_traceState_1755_, sizeof(void*)*1);
v_traces_1768_ = lean_ctor_get(v_traceState_1755_, 0);
v_isSharedCheck_1781_ = !lean_is_exclusive(v_traceState_1755_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1770_ = v_traceState_1755_;
v_isShared_1771_ = v_isSharedCheck_1781_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_traces_1768_);
lean_dec(v_traceState_1755_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1781_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1772_; lean_object* v___x_1774_; 
v___x_1772_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1710_, v_traces_1768_);
lean_dec_ref(v_traces_1768_);
if (v_isShared_1771_ == 0)
{
lean_ctor_set(v___x_1770_, 0, v___x_1772_);
v___x_1774_ = v___x_1770_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v___x_1772_);
lean_ctor_set_uint64(v_reuseFailAlloc_1780_, sizeof(void*)*1, v_tid_1767_);
v___x_1774_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
lean_object* v___x_1776_; 
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 4, v___x_1774_);
v___x_1776_ = v___x_1765_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_env_1756_);
lean_ctor_set(v_reuseFailAlloc_1779_, 1, v_nextMacroScope_1757_);
lean_ctor_set(v_reuseFailAlloc_1779_, 2, v_ngen_1758_);
lean_ctor_set(v_reuseFailAlloc_1779_, 3, v_auxDeclNGen_1759_);
lean_ctor_set(v_reuseFailAlloc_1779_, 4, v___x_1774_);
lean_ctor_set(v_reuseFailAlloc_1779_, 5, v_cache_1760_);
lean_ctor_set(v_reuseFailAlloc_1779_, 6, v_messages_1761_);
lean_ctor_set(v_reuseFailAlloc_1779_, 7, v_infoState_1762_);
lean_ctor_set(v_reuseFailAlloc_1779_, 8, v_snapshotTasks_1763_);
v___x_1776_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1777_ = lean_st_ref_set(v___y_1714_, v___x_1776_);
v___x_1778_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5___redArg(v_fst_1716_);
return v___x_1778_;
}
}
}
}
}
else
{
goto v___jp_1747_;
}
}
else
{
goto v___jp_1747_;
}
}
v___jp_1783_:
{
double v___x_1785_; double v___x_1786_; double v___x_1787_; uint8_t v___x_1788_; 
v___x_1785_ = lean_unbox_float(v_snd_1733_);
v___x_1786_ = lean_unbox_float(v_fst_1732_);
v___x_1787_ = lean_float_sub(v___x_1785_, v___x_1786_);
v___x_1788_ = lean_float_decLt(v___y_1784_, v___x_1787_);
v___y_1753_ = v___x_1788_;
goto v___jp_1752_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1___boxed(lean_object* v_cls_1799_, lean_object* v_collapsed_1800_, lean_object* v_tag_1801_, lean_object* v_opts_1802_, lean_object* v_clsEnabled_1803_, lean_object* v_oldTraces_1804_, lean_object* v_msg_1805_, lean_object* v_resStartStop_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_){
_start:
{
uint8_t v_collapsed_boxed_1810_; uint8_t v_clsEnabled_boxed_1811_; lean_object* v_res_1812_; 
v_collapsed_boxed_1810_ = lean_unbox(v_collapsed_1800_);
v_clsEnabled_boxed_1811_ = lean_unbox(v_clsEnabled_1803_);
v_res_1812_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1(v_cls_1799_, v_collapsed_boxed_1810_, v_tag_1801_, v_opts_1802_, v_clsEnabled_boxed_1811_, v_oldTraces_1804_, v_msg_1805_, v_resStartStop_1806_, v___y_1807_, v___y_1808_);
lean_dec(v___y_1808_);
lean_dec_ref(v___y_1807_);
lean_dec_ref(v_opts_1802_);
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__4(lean_object* v___f_1813_, lean_object* v_lratPath_1814_, uint8_t v_trimProofs_1815_, lean_object* v___f_1816_, lean_object* v_solver_1817_, lean_object* v_timeout_1818_, uint8_t v_binaryProofs_1819_, uint8_t v_solverMode_1820_, lean_object* v___f_1821_, lean_object* v___f_1822_, lean_object* v_cnfHandle_1823_, lean_object* v_cnfPath_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_){
_start:
{
lean_object* v___y_1829_; lean_object* v_options_1847_; lean_object* v_ref_1848_; lean_object* v_inheritedTraceOptions_1849_; uint8_t v_hasTrace_1850_; lean_object* v___x_1851_; uint8_t v___x_1852_; lean_object* v___x_1853_; lean_object* v___y_1855_; lean_object* v___y_1856_; uint8_t v___y_1857_; lean_object* v___y_1858_; lean_object* v_a_1859_; lean_object* v___y_1872_; lean_object* v___y_1873_; uint8_t v___y_1874_; lean_object* v___y_1875_; lean_object* v_a_1876_; lean_object* v___y_1886_; uint8_t v___y_1887_; lean_object* v___y_1929_; lean_object* v___y_1961_; lean_object* v___y_1962_; uint8_t v___y_1963_; lean_object* v___y_1964_; lean_object* v_a_1965_; lean_object* v___y_1978_; lean_object* v___y_1979_; uint8_t v___y_1980_; lean_object* v___y_1981_; lean_object* v_a_1982_; lean_object* v___y_1992_; uint8_t v___y_1993_; lean_object* v___y_2042_; 
v_options_1847_ = lean_ctor_get(v___y_1825_, 2);
v_ref_1848_ = lean_ctor_get(v___y_1825_, 5);
v_inheritedTraceOptions_1849_ = lean_ctor_get(v___y_1825_, 13);
v_hasTrace_1850_ = lean_ctor_get_uint8(v_options_1847_, sizeof(void*)*1);
v___x_1851_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__3));
v___x_1852_ = 1;
v___x_1853_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0___closed__0));
if (v_hasTrace_1850_ == 0)
{
lean_object* v___x_2051_; 
lean_dec_ref(v___f_1822_);
v___x_2051_ = l_IO_lazyPure___redArg(v___f_1821_);
if (lean_obj_tag(v___x_2051_) == 0)
{
lean_object* v_a_2052_; lean_object* v___x_2053_; 
v_a_2052_ = lean_ctor_get(v___x_2051_, 0);
lean_inc(v_a_2052_);
lean_dec_ref_known(v___x_2051_, 1);
v___x_2053_ = lean_io_prim_handle_put_str(v_cnfHandle_1823_, v_a_2052_);
lean_dec(v_a_2052_);
if (lean_obj_tag(v___x_2053_) == 0)
{
lean_object* v___x_2054_; 
lean_dec_ref_known(v___x_2053_, 1);
v___x_2054_ = lean_io_prim_handle_flush(v_cnfHandle_1823_);
if (lean_obj_tag(v___x_2054_) == 0)
{
lean_dec_ref_known(v___x_2054_, 1);
goto v___jp_2034_;
}
else
{
lean_object* v_a_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2066_; 
lean_dec_ref(v_cnfPath_1824_);
lean_dec_ref(v_solver_1817_);
lean_dec_ref(v___f_1816_);
lean_dec_ref(v_lratPath_1814_);
lean_dec_ref(v___f_1813_);
v_a_2055_ = lean_ctor_get(v___x_2054_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2057_ = v___x_2054_;
v_isShared_2058_ = v_isSharedCheck_2066_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_a_2055_);
lean_dec(v___x_2054_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2066_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2064_; 
v___x_2059_ = lean_io_error_to_string(v_a_2055_);
v___x_2060_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2060_, 0, v___x_2059_);
v___x_2061_ = l_Lean_MessageData_ofFormat(v___x_2060_);
lean_inc(v_ref_1848_);
v___x_2062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2062_, 0, v_ref_1848_);
lean_ctor_set(v___x_2062_, 1, v___x_2061_);
if (v_isShared_2058_ == 0)
{
lean_ctor_set(v___x_2057_, 0, v___x_2062_);
v___x_2064_ = v___x_2057_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v___x_2062_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
}
}
}
}
else
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2078_; 
lean_dec_ref(v_cnfPath_1824_);
lean_dec_ref(v_solver_1817_);
lean_dec_ref(v___f_1816_);
lean_dec_ref(v_lratPath_1814_);
lean_dec_ref(v___f_1813_);
v_a_2067_ = lean_ctor_get(v___x_2053_, 0);
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2053_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2069_ = v___x_2053_;
v_isShared_2070_ = v_isSharedCheck_2078_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_2053_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2078_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2076_; 
v___x_2071_ = lean_io_error_to_string(v_a_2067_);
v___x_2072_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2071_);
v___x_2073_ = l_Lean_MessageData_ofFormat(v___x_2072_);
lean_inc(v_ref_1848_);
v___x_2074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2074_, 0, v_ref_1848_);
lean_ctor_set(v___x_2074_, 1, v___x_2073_);
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 0, v___x_2074_);
v___x_2076_ = v___x_2069_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v___x_2074_);
v___x_2076_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
return v___x_2076_;
}
}
}
}
else
{
lean_object* v_a_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2090_; 
lean_dec_ref(v_cnfPath_1824_);
lean_dec_ref(v_solver_1817_);
lean_dec_ref(v___f_1816_);
lean_dec_ref(v_lratPath_1814_);
lean_dec_ref(v___f_1813_);
v_a_2079_ = lean_ctor_get(v___x_2051_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2081_ = v___x_2051_;
v_isShared_2082_ = v_isSharedCheck_2090_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_a_2079_);
lean_dec(v___x_2051_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2090_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2088_; 
v___x_2083_ = lean_io_error_to_string(v_a_2079_);
v___x_2084_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2083_);
v___x_2085_ = l_Lean_MessageData_ofFormat(v___x_2084_);
lean_inc(v_ref_1848_);
v___x_2086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2086_, 0, v_ref_1848_);
lean_ctor_set(v___x_2086_, 1, v___x_2085_);
if (v_isShared_2082_ == 0)
{
lean_ctor_set(v___x_2081_, 0, v___x_2086_);
v___x_2088_ = v___x_2081_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v___x_2086_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
}
}
else
{
lean_object* v___x_2091_; uint8_t v___x_2092_; lean_object* v___y_2094_; lean_object* v___y_2095_; lean_object* v_a_2096_; lean_object* v___y_2109_; lean_object* v___y_2110_; lean_object* v_a_2111_; lean_object* v___y_2114_; lean_object* v___y_2115_; lean_object* v_a_2116_; lean_object* v___y_2126_; lean_object* v___y_2127_; lean_object* v_a_2128_; 
v___x_2091_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6);
v___x_2092_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1849_, v_options_1847_, v___x_2091_);
if (v___x_2092_ == 0)
{
lean_object* v___x_2227_; uint8_t v___x_2228_; 
v___x_2227_ = l_Lean_trace_profiler;
v___x_2228_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_options_1847_, v___x_2227_);
if (v___x_2228_ == 0)
{
lean_object* v___x_2229_; 
lean_dec_ref(v___f_1822_);
v___x_2229_ = l_IO_lazyPure___redArg(v___f_1821_);
if (lean_obj_tag(v___x_2229_) == 0)
{
lean_object* v_a_2230_; lean_object* v___x_2231_; 
v_a_2230_ = lean_ctor_get(v___x_2229_, 0);
lean_inc(v_a_2230_);
lean_dec_ref_known(v___x_2229_, 1);
v___x_2231_ = lean_io_prim_handle_put_str(v_cnfHandle_1823_, v_a_2230_);
lean_dec(v_a_2230_);
if (lean_obj_tag(v___x_2231_) == 0)
{
lean_object* v___x_2232_; 
lean_dec_ref_known(v___x_2231_, 1);
v___x_2232_ = lean_io_prim_handle_flush(v_cnfHandle_1823_);
if (lean_obj_tag(v___x_2232_) == 0)
{
lean_dec_ref_known(v___x_2232_, 1);
goto v___jp_2034_;
}
else
{
lean_object* v_a_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2244_; 
lean_dec_ref(v_cnfPath_1824_);
lean_dec_ref(v_solver_1817_);
lean_dec_ref(v___f_1816_);
lean_dec_ref(v_lratPath_1814_);
lean_dec_ref(v___f_1813_);
v_a_2233_ = lean_ctor_get(v___x_2232_, 0);
v_isSharedCheck_2244_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2244_ == 0)
{
v___x_2235_ = v___x_2232_;
v_isShared_2236_ = v_isSharedCheck_2244_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_a_2233_);
lean_dec(v___x_2232_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2244_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2242_; 
v___x_2237_ = lean_io_error_to_string(v_a_2233_);
v___x_2238_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2238_, 0, v___x_2237_);
v___x_2239_ = l_Lean_MessageData_ofFormat(v___x_2238_);
lean_inc(v_ref_1848_);
v___x_2240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2240_, 0, v_ref_1848_);
lean_ctor_set(v___x_2240_, 1, v___x_2239_);
if (v_isShared_2236_ == 0)
{
lean_ctor_set(v___x_2235_, 0, v___x_2240_);
v___x_2242_ = v___x_2235_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v___x_2240_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
}
}
}
}
else
{
lean_object* v_a_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2256_; 
lean_dec_ref(v_cnfPath_1824_);
lean_dec_ref(v_solver_1817_);
lean_dec_ref(v___f_1816_);
lean_dec_ref(v_lratPath_1814_);
lean_dec_ref(v___f_1813_);
v_a_2245_ = lean_ctor_get(v___x_2231_, 0);
v_isSharedCheck_2256_ = !lean_is_exclusive(v___x_2231_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2247_ = v___x_2231_;
v_isShared_2248_ = v_isSharedCheck_2256_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_a_2245_);
lean_dec(v___x_2231_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2256_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2254_; 
v___x_2249_ = lean_io_error_to_string(v_a_2245_);
v___x_2250_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2250_, 0, v___x_2249_);
v___x_2251_ = l_Lean_MessageData_ofFormat(v___x_2250_);
lean_inc(v_ref_1848_);
v___x_2252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2252_, 0, v_ref_1848_);
lean_ctor_set(v___x_2252_, 1, v___x_2251_);
if (v_isShared_2248_ == 0)
{
lean_ctor_set(v___x_2247_, 0, v___x_2252_);
v___x_2254_ = v___x_2247_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v___x_2252_);
v___x_2254_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
return v___x_2254_;
}
}
}
}
else
{
lean_object* v_a_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2268_; 
lean_dec_ref(v_cnfPath_1824_);
lean_dec_ref(v_solver_1817_);
lean_dec_ref(v___f_1816_);
lean_dec_ref(v_lratPath_1814_);
lean_dec_ref(v___f_1813_);
v_a_2257_ = lean_ctor_get(v___x_2229_, 0);
v_isSharedCheck_2268_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2268_ == 0)
{
v___x_2259_ = v___x_2229_;
v_isShared_2260_ = v_isSharedCheck_2268_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_a_2257_);
lean_dec(v___x_2229_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2268_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2266_; 
v___x_2261_ = lean_io_error_to_string(v_a_2257_);
v___x_2262_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2262_, 0, v___x_2261_);
v___x_2263_ = l_Lean_MessageData_ofFormat(v___x_2262_);
lean_inc(v_ref_1848_);
v___x_2264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2264_, 0, v_ref_1848_);
lean_ctor_set(v___x_2264_, 1, v___x_2263_);
if (v_isShared_2260_ == 0)
{
lean_ctor_set(v___x_2259_, 0, v___x_2264_);
v___x_2266_ = v___x_2259_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v___x_2264_);
v___x_2266_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
return v___x_2266_;
}
}
}
}
else
{
goto v___jp_2130_;
}
}
else
{
goto v___jp_2130_;
}
v___jp_2093_:
{
lean_object* v___x_2097_; double v___x_2098_; double v___x_2099_; double v___x_2100_; double v___x_2101_; double v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; 
v___x_2097_ = lean_io_mono_nanos_now();
v___x_2098_ = lean_float_of_nat(v___y_2094_);
v___x_2099_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9);
v___x_2100_ = lean_float_div(v___x_2098_, v___x_2099_);
v___x_2101_ = lean_float_of_nat(v___x_2097_);
v___x_2102_ = lean_float_div(v___x_2101_, v___x_2099_);
v___x_2103_ = lean_box_float(v___x_2100_);
v___x_2104_ = lean_box_float(v___x_2102_);
v___x_2105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2105_, 0, v___x_2103_);
lean_ctor_set(v___x_2105_, 1, v___x_2104_);
v___x_2106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2106_, 0, v_a_2096_);
lean_ctor_set(v___x_2106_, 1, v___x_2105_);
v___x_2107_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2(v___x_1851_, v___x_1852_, v___x_1853_, v_options_1847_, v___x_2092_, v___y_2095_, v___f_1822_, v___x_2106_, v___y_1825_, v___y_1826_);
v___y_2042_ = v___x_2107_;
goto v___jp_2041_;
}
v___jp_2108_:
{
lean_object* v___x_2112_; 
v___x_2112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2112_, 0, v_a_2111_);
v___y_2094_ = v___y_2109_;
v___y_2095_ = v___y_2110_;
v_a_2096_ = v___x_2112_;
goto v___jp_2093_;
}
v___jp_2113_:
{
lean_object* v___x_2117_; double v___x_2118_; double v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; 
v___x_2117_ = lean_io_get_num_heartbeats();
v___x_2118_ = lean_float_of_nat(v___y_2115_);
v___x_2119_ = lean_float_of_nat(v___x_2117_);
v___x_2120_ = lean_box_float(v___x_2118_);
v___x_2121_ = lean_box_float(v___x_2119_);
v___x_2122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2120_);
lean_ctor_set(v___x_2122_, 1, v___x_2121_);
v___x_2123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2123_, 0, v_a_2116_);
lean_ctor_set(v___x_2123_, 1, v___x_2122_);
v___x_2124_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2(v___x_1851_, v___x_1852_, v___x_1853_, v_options_1847_, v___x_2092_, v___y_2114_, v___f_1822_, v___x_2123_, v___y_1825_, v___y_1826_);
v___y_2042_ = v___x_2124_;
goto v___jp_2041_;
}
v___jp_2125_:
{
lean_object* v___x_2129_; 
v___x_2129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2129_, 0, v_a_2128_);
v___y_2114_ = v___y_2126_;
v___y_2115_ = v___y_2127_;
v_a_2116_ = v___x_2129_;
goto v___jp_2113_;
}
v___jp_2130_:
{
lean_object* v___x_2131_; lean_object* v_a_2132_; lean_object* v___x_2133_; uint8_t v___x_2134_; 
v___x_2131_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg(v___y_1826_);
v_a_2132_ = lean_ctor_get(v___x_2131_, 0);
lean_inc(v_a_2132_);
lean_dec_ref(v___x_2131_);
v___x_2133_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2134_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_options_1847_, v___x_2133_);
if (v___x_2134_ == 0)
{
lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2135_ = lean_io_mono_nanos_now();
v___x_2136_ = l_IO_lazyPure___redArg(v___f_1821_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_object* v_a_2137_; lean_object* v___x_2138_; 
v_a_2137_ = lean_ctor_get(v___x_2136_, 0);
lean_inc(v_a_2137_);
lean_dec_ref_known(v___x_2136_, 1);
v___x_2138_ = lean_io_prim_handle_put_str(v_cnfHandle_1823_, v_a_2137_);
lean_dec(v_a_2137_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v___x_2139_; 
lean_dec_ref_known(v___x_2138_, 1);
v___x_2139_ = lean_io_prim_handle_flush(v_cnfHandle_1823_);
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_object* v_a_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2147_; 
v_a_2140_ = lean_ctor_get(v___x_2139_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2142_ = v___x_2139_;
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_a_2140_);
lean_dec(v___x_2139_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2145_; 
if (v_isShared_2143_ == 0)
{
lean_ctor_set_tag(v___x_2142_, 1);
v___x_2145_ = v___x_2142_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_a_2140_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
v___y_2094_ = v___x_2135_;
v___y_2095_ = v_a_2132_;
v_a_2096_ = v___x_2145_;
goto v___jp_2093_;
}
}
}
else
{
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2158_; 
v_a_2148_ = lean_ctor_get(v___x_2139_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2150_ = v___x_2139_;
v_isShared_2151_ = v_isSharedCheck_2158_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2139_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2158_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2152_; lean_object* v___x_2154_; 
v___x_2152_ = lean_io_error_to_string(v_a_2148_);
if (v_isShared_2151_ == 0)
{
lean_ctor_set_tag(v___x_2150_, 3);
lean_ctor_set(v___x_2150_, 0, v___x_2152_);
v___x_2154_ = v___x_2150_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v___x_2152_);
v___x_2154_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; 
v___x_2155_ = l_Lean_MessageData_ofFormat(v___x_2154_);
lean_inc(v_ref_1848_);
v___x_2156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2156_, 0, v_ref_1848_);
lean_ctor_set(v___x_2156_, 1, v___x_2155_);
v___y_2109_ = v___x_2135_;
v___y_2110_ = v_a_2132_;
v_a_2111_ = v___x_2156_;
goto v___jp_2108_;
}
}
}
}
else
{
lean_object* v_a_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2169_; 
v_a_2159_ = lean_ctor_get(v___x_2138_, 0);
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2161_ = v___x_2138_;
v_isShared_2162_ = v_isSharedCheck_2169_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_a_2159_);
lean_dec(v___x_2138_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2169_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v___x_2163_; lean_object* v___x_2165_; 
v___x_2163_ = lean_io_error_to_string(v_a_2159_);
if (v_isShared_2162_ == 0)
{
lean_ctor_set_tag(v___x_2161_, 3);
lean_ctor_set(v___x_2161_, 0, v___x_2163_);
v___x_2165_ = v___x_2161_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v___x_2163_);
v___x_2165_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2166_ = l_Lean_MessageData_ofFormat(v___x_2165_);
lean_inc(v_ref_1848_);
v___x_2167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2167_, 0, v_ref_1848_);
lean_ctor_set(v___x_2167_, 1, v___x_2166_);
v___y_2109_ = v___x_2135_;
v___y_2110_ = v_a_2132_;
v_a_2111_ = v___x_2167_;
goto v___jp_2108_;
}
}
}
}
else
{
lean_object* v_a_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2180_; 
v_a_2170_ = lean_ctor_get(v___x_2136_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2172_ = v___x_2136_;
v_isShared_2173_ = v_isSharedCheck_2180_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_a_2170_);
lean_dec(v___x_2136_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2180_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v___x_2174_; lean_object* v___x_2176_; 
v___x_2174_ = lean_io_error_to_string(v_a_2170_);
if (v_isShared_2173_ == 0)
{
lean_ctor_set_tag(v___x_2172_, 3);
lean_ctor_set(v___x_2172_, 0, v___x_2174_);
v___x_2176_ = v___x_2172_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v___x_2174_);
v___x_2176_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2177_ = l_Lean_MessageData_ofFormat(v___x_2176_);
lean_inc(v_ref_1848_);
v___x_2178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2178_, 0, v_ref_1848_);
lean_ctor_set(v___x_2178_, 1, v___x_2177_);
v___y_2109_ = v___x_2135_;
v___y_2110_ = v_a_2132_;
v_a_2111_ = v___x_2178_;
goto v___jp_2108_;
}
}
}
}
else
{
lean_object* v___x_2181_; lean_object* v___x_2182_; 
v___x_2181_ = lean_io_get_num_heartbeats();
v___x_2182_ = l_IO_lazyPure___redArg(v___f_1821_);
if (lean_obj_tag(v___x_2182_) == 0)
{
lean_object* v_a_2183_; lean_object* v___x_2184_; 
v_a_2183_ = lean_ctor_get(v___x_2182_, 0);
lean_inc(v_a_2183_);
lean_dec_ref_known(v___x_2182_, 1);
v___x_2184_ = lean_io_prim_handle_put_str(v_cnfHandle_1823_, v_a_2183_);
lean_dec(v_a_2183_);
if (lean_obj_tag(v___x_2184_) == 0)
{
lean_object* v___x_2185_; 
lean_dec_ref_known(v___x_2184_, 1);
v___x_2185_ = lean_io_prim_handle_flush(v_cnfHandle_1823_);
if (lean_obj_tag(v___x_2185_) == 0)
{
lean_object* v_a_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2193_; 
v_a_2186_ = lean_ctor_get(v___x_2185_, 0);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2185_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2188_ = v___x_2185_;
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_a_2186_);
lean_dec(v___x_2185_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2191_; 
if (v_isShared_2189_ == 0)
{
lean_ctor_set_tag(v___x_2188_, 1);
v___x_2191_ = v___x_2188_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_a_2186_);
v___x_2191_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
v___y_2114_ = v_a_2132_;
v___y_2115_ = v___x_2181_;
v_a_2116_ = v___x_2191_;
goto v___jp_2113_;
}
}
}
else
{
lean_object* v_a_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2204_; 
v_a_2194_ = lean_ctor_get(v___x_2185_, 0);
v_isSharedCheck_2204_ = !lean_is_exclusive(v___x_2185_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2196_ = v___x_2185_;
v_isShared_2197_ = v_isSharedCheck_2204_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_a_2194_);
lean_dec(v___x_2185_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2204_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v___x_2198_; lean_object* v___x_2200_; 
v___x_2198_ = lean_io_error_to_string(v_a_2194_);
if (v_isShared_2197_ == 0)
{
lean_ctor_set_tag(v___x_2196_, 3);
lean_ctor_set(v___x_2196_, 0, v___x_2198_);
v___x_2200_ = v___x_2196_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v___x_2198_);
v___x_2200_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2201_ = l_Lean_MessageData_ofFormat(v___x_2200_);
lean_inc(v_ref_1848_);
v___x_2202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2202_, 0, v_ref_1848_);
lean_ctor_set(v___x_2202_, 1, v___x_2201_);
v___y_2126_ = v_a_2132_;
v___y_2127_ = v___x_2181_;
v_a_2128_ = v___x_2202_;
goto v___jp_2125_;
}
}
}
}
else
{
lean_object* v_a_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2215_; 
v_a_2205_ = lean_ctor_get(v___x_2184_, 0);
v_isSharedCheck_2215_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2207_ = v___x_2184_;
v_isShared_2208_ = v_isSharedCheck_2215_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_a_2205_);
lean_dec(v___x_2184_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2215_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2209_; lean_object* v___x_2211_; 
v___x_2209_ = lean_io_error_to_string(v_a_2205_);
if (v_isShared_2208_ == 0)
{
lean_ctor_set_tag(v___x_2207_, 3);
lean_ctor_set(v___x_2207_, 0, v___x_2209_);
v___x_2211_ = v___x_2207_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v___x_2209_);
v___x_2211_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2212_ = l_Lean_MessageData_ofFormat(v___x_2211_);
lean_inc(v_ref_1848_);
v___x_2213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2213_, 0, v_ref_1848_);
lean_ctor_set(v___x_2213_, 1, v___x_2212_);
v___y_2126_ = v_a_2132_;
v___y_2127_ = v___x_2181_;
v_a_2128_ = v___x_2213_;
goto v___jp_2125_;
}
}
}
}
else
{
lean_object* v_a_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2226_; 
v_a_2216_ = lean_ctor_get(v___x_2182_, 0);
v_isSharedCheck_2226_ = !lean_is_exclusive(v___x_2182_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2218_ = v___x_2182_;
v_isShared_2219_ = v_isSharedCheck_2226_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_a_2216_);
lean_dec(v___x_2182_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2226_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2220_; lean_object* v___x_2222_; 
v___x_2220_ = lean_io_error_to_string(v_a_2216_);
if (v_isShared_2219_ == 0)
{
lean_ctor_set_tag(v___x_2218_, 3);
lean_ctor_set(v___x_2218_, 0, v___x_2220_);
v___x_2222_ = v___x_2218_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v___x_2220_);
v___x_2222_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
lean_object* v___x_2223_; lean_object* v___x_2224_; 
v___x_2223_ = l_Lean_MessageData_ofFormat(v___x_2222_);
lean_inc(v_ref_1848_);
v___x_2224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2224_, 0, v_ref_1848_);
lean_ctor_set(v___x_2224_, 1, v___x_2223_);
v___y_2126_ = v_a_2132_;
v___y_2127_ = v___x_2181_;
v_a_2128_ = v___x_2224_;
goto v___jp_2125_;
}
}
}
}
}
}
v___jp_1828_:
{
if (lean_obj_tag(v___y_1829_) == 0)
{
lean_object* v_a_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1838_; 
v_a_1830_ = lean_ctor_get(v___y_1829_, 0);
v_isSharedCheck_1838_ = !lean_is_exclusive(v___y_1829_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1832_ = v___y_1829_;
v_isShared_1833_ = v_isSharedCheck_1838_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_a_1830_);
lean_dec(v___y_1829_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1838_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1834_; lean_object* v___x_1836_; 
v___x_1834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1834_, 0, v_a_1830_);
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 0, v___x_1834_);
v___x_1836_ = v___x_1832_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v___x_1834_);
v___x_1836_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
return v___x_1836_;
}
}
}
else
{
lean_object* v_a_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1846_; 
v_a_1839_ = lean_ctor_get(v___y_1829_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___y_1829_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1841_ = v___y_1829_;
v_isShared_1842_ = v_isSharedCheck_1846_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_a_1839_);
lean_dec(v___y_1829_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1846_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v___x_1844_; 
if (v_isShared_1842_ == 0)
{
v___x_1844_ = v___x_1841_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_a_1839_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
}
}
v___jp_1854_:
{
lean_object* v___x_1860_; double v___x_1861_; double v___x_1862_; double v___x_1863_; double v___x_1864_; double v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; 
v___x_1860_ = lean_io_mono_nanos_now();
v___x_1861_ = lean_float_of_nat(v___y_1858_);
v___x_1862_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9);
v___x_1863_ = lean_float_div(v___x_1861_, v___x_1862_);
v___x_1864_ = lean_float_of_nat(v___x_1860_);
v___x_1865_ = lean_float_div(v___x_1864_, v___x_1862_);
v___x_1866_ = lean_box_float(v___x_1863_);
v___x_1867_ = lean_box_float(v___x_1865_);
v___x_1868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1868_, 0, v___x_1866_);
lean_ctor_set(v___x_1868_, 1, v___x_1867_);
v___x_1869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1869_, 0, v_a_1859_);
lean_ctor_set(v___x_1869_, 1, v___x_1868_);
v___x_1870_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0(v___x_1851_, v___x_1852_, v___x_1853_, v___y_1855_, v___y_1857_, v___y_1856_, v___f_1813_, v___x_1869_, v___y_1825_, v___y_1826_);
v___y_1829_ = v___x_1870_;
goto v___jp_1828_;
}
v___jp_1871_:
{
lean_object* v___x_1877_; double v___x_1878_; double v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; 
v___x_1877_ = lean_io_get_num_heartbeats();
v___x_1878_ = lean_float_of_nat(v___y_1875_);
v___x_1879_ = lean_float_of_nat(v___x_1877_);
v___x_1880_ = lean_box_float(v___x_1878_);
v___x_1881_ = lean_box_float(v___x_1879_);
v___x_1882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1880_);
lean_ctor_set(v___x_1882_, 1, v___x_1881_);
v___x_1883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1883_, 0, v_a_1876_);
lean_ctor_set(v___x_1883_, 1, v___x_1882_);
v___x_1884_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0(v___x_1851_, v___x_1852_, v___x_1853_, v___y_1872_, v___y_1874_, v___y_1873_, v___f_1813_, v___x_1883_, v___y_1825_, v___y_1826_);
v___y_1829_ = v___x_1884_;
goto v___jp_1828_;
}
v___jp_1885_:
{
lean_object* v___x_1888_; lean_object* v_a_1889_; lean_object* v___x_1890_; uint8_t v___x_1891_; 
v___x_1888_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg(v___y_1826_);
v_a_1889_ = lean_ctor_get(v___x_1888_, 0);
lean_inc(v_a_1889_);
lean_dec_ref(v___x_1888_);
v___x_1890_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1891_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v___y_1886_, v___x_1890_);
if (v___x_1891_ == 0)
{
lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1892_ = lean_io_mono_nanos_now();
v___x_1893_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_1814_, v_trimProofs_1815_, v___y_1825_, v___y_1826_);
lean_dec_ref(v_lratPath_1814_);
if (lean_obj_tag(v___x_1893_) == 0)
{
lean_object* v_a_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1901_; 
v_a_1894_ = lean_ctor_get(v___x_1893_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1893_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1896_ = v___x_1893_;
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_a_1894_);
lean_dec(v___x_1893_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1899_; 
if (v_isShared_1897_ == 0)
{
lean_ctor_set_tag(v___x_1896_, 1);
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
v___y_1855_ = v___y_1886_;
v___y_1856_ = v_a_1889_;
v___y_1857_ = v___y_1887_;
v___y_1858_ = v___x_1892_;
v_a_1859_ = v___x_1899_;
goto v___jp_1854_;
}
}
}
else
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1909_; 
v_a_1902_ = lean_ctor_get(v___x_1893_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___x_1893_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1904_ = v___x_1893_;
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v___x_1893_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1907_; 
if (v_isShared_1905_ == 0)
{
lean_ctor_set_tag(v___x_1904_, 0);
v___x_1907_ = v___x_1904_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_a_1902_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
v___y_1855_ = v___y_1886_;
v___y_1856_ = v_a_1889_;
v___y_1857_ = v___y_1887_;
v___y_1858_ = v___x_1892_;
v_a_1859_ = v___x_1907_;
goto v___jp_1854_;
}
}
}
}
else
{
lean_object* v___x_1910_; lean_object* v___x_1911_; 
v___x_1910_ = lean_io_get_num_heartbeats();
v___x_1911_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_1814_, v_trimProofs_1815_, v___y_1825_, v___y_1826_);
lean_dec_ref(v_lratPath_1814_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_object* v_a_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1919_; 
v_a_1912_ = lean_ctor_get(v___x_1911_, 0);
v_isSharedCheck_1919_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1914_ = v___x_1911_;
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_a_1912_);
lean_dec(v___x_1911_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v___x_1917_; 
if (v_isShared_1915_ == 0)
{
lean_ctor_set_tag(v___x_1914_, 1);
v___x_1917_ = v___x_1914_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_a_1912_);
v___x_1917_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
v___y_1872_ = v___y_1886_;
v___y_1873_ = v_a_1889_;
v___y_1874_ = v___y_1887_;
v___y_1875_ = v___x_1910_;
v_a_1876_ = v___x_1917_;
goto v___jp_1871_;
}
}
}
else
{
lean_object* v_a_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1927_; 
v_a_1920_ = lean_ctor_get(v___x_1911_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1922_ = v___x_1911_;
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_dec(v___x_1911_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1925_; 
if (v_isShared_1923_ == 0)
{
lean_ctor_set_tag(v___x_1922_, 0);
v___x_1925_ = v___x_1922_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_a_1920_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
v___y_1872_ = v___y_1886_;
v___y_1873_ = v_a_1889_;
v___y_1874_ = v___y_1887_;
v___y_1875_ = v___x_1910_;
v_a_1876_ = v___x_1925_;
goto v___jp_1871_;
}
}
}
}
}
v___jp_1928_:
{
if (lean_obj_tag(v___y_1929_) == 0)
{
lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1951_; 
v_a_1930_ = lean_ctor_get(v___y_1929_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___y_1929_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1932_ = v___y_1929_;
v_isShared_1933_ = v_isSharedCheck_1951_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v___y_1929_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1951_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
if (lean_obj_tag(v_a_1930_) == 0)
{
lean_object* v_assignment_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1944_; 
lean_dec_ref(v_lratPath_1814_);
lean_dec_ref(v___f_1813_);
v_assignment_1934_ = lean_ctor_get(v_a_1930_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v_a_1930_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1936_ = v_a_1930_;
v_isShared_1937_ = v_isSharedCheck_1944_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_assignment_1934_);
lean_dec(v_a_1930_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1944_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___x_1939_; 
if (v_isShared_1937_ == 0)
{
v___x_1939_ = v___x_1936_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_assignment_1934_);
v___x_1939_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
lean_object* v___x_1941_; 
if (v_isShared_1933_ == 0)
{
lean_ctor_set(v___x_1932_, 0, v___x_1939_);
v___x_1941_ = v___x_1932_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v___x_1939_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
return v___x_1941_;
}
}
}
}
else
{
lean_del_object(v___x_1932_);
lean_dec(v_a_1930_);
if (v_hasTrace_1850_ == 0)
{
lean_object* v___x_1945_; 
lean_dec_ref(v___f_1813_);
v___x_1945_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_1814_, v_trimProofs_1815_, v___y_1825_, v___y_1826_);
lean_dec_ref(v_lratPath_1814_);
v___y_1829_ = v___x_1945_;
goto v___jp_1828_;
}
else
{
lean_object* v___x_1946_; uint8_t v___x_1947_; 
v___x_1946_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6);
v___x_1947_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1849_, v_options_1847_, v___x_1946_);
if (v___x_1947_ == 0)
{
lean_object* v___x_1948_; uint8_t v___x_1949_; 
v___x_1948_ = l_Lean_trace_profiler;
v___x_1949_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_options_1847_, v___x_1948_);
if (v___x_1949_ == 0)
{
lean_object* v___x_1950_; 
lean_dec_ref(v___f_1813_);
v___x_1950_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_1814_, v_trimProofs_1815_, v___y_1825_, v___y_1826_);
lean_dec_ref(v_lratPath_1814_);
v___y_1829_ = v___x_1950_;
goto v___jp_1828_;
}
else
{
v___y_1886_ = v_options_1847_;
v___y_1887_ = v___x_1947_;
goto v___jp_1885_;
}
}
else
{
v___y_1886_ = v_options_1847_;
v___y_1887_ = v___x_1947_;
goto v___jp_1885_;
}
}
}
}
}
else
{
lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1959_; 
lean_dec_ref(v_lratPath_1814_);
lean_dec_ref(v___f_1813_);
v_a_1952_ = lean_ctor_get(v___y_1929_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___y_1929_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1954_ = v___y_1929_;
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_dec(v___y_1929_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1957_; 
if (v_isShared_1955_ == 0)
{
v___x_1957_ = v___x_1954_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_a_1952_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
}
v___jp_1960_:
{
lean_object* v___x_1966_; double v___x_1967_; double v___x_1968_; double v___x_1969_; double v___x_1970_; double v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; 
v___x_1966_ = lean_io_mono_nanos_now();
v___x_1967_ = lean_float_of_nat(v___y_1964_);
v___x_1968_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9);
v___x_1969_ = lean_float_div(v___x_1967_, v___x_1968_);
v___x_1970_ = lean_float_of_nat(v___x_1966_);
v___x_1971_ = lean_float_div(v___x_1970_, v___x_1968_);
v___x_1972_ = lean_box_float(v___x_1969_);
v___x_1973_ = lean_box_float(v___x_1971_);
v___x_1974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1974_, 0, v___x_1972_);
lean_ctor_set(v___x_1974_, 1, v___x_1973_);
v___x_1975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1975_, 0, v_a_1965_);
lean_ctor_set(v___x_1975_, 1, v___x_1974_);
v___x_1976_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1(v___x_1851_, v___x_1852_, v___x_1853_, v___y_1961_, v___y_1963_, v___y_1962_, v___f_1816_, v___x_1975_, v___y_1825_, v___y_1826_);
v___y_1929_ = v___x_1976_;
goto v___jp_1928_;
}
v___jp_1977_:
{
lean_object* v___x_1983_; double v___x_1984_; double v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; 
v___x_1983_ = lean_io_get_num_heartbeats();
v___x_1984_ = lean_float_of_nat(v___y_1981_);
v___x_1985_ = lean_float_of_nat(v___x_1983_);
v___x_1986_ = lean_box_float(v___x_1984_);
v___x_1987_ = lean_box_float(v___x_1985_);
v___x_1988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1986_);
lean_ctor_set(v___x_1988_, 1, v___x_1987_);
v___x_1989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1989_, 0, v_a_1982_);
lean_ctor_set(v___x_1989_, 1, v___x_1988_);
v___x_1990_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1(v___x_1851_, v___x_1852_, v___x_1853_, v___y_1978_, v___y_1980_, v___y_1979_, v___f_1816_, v___x_1989_, v___y_1825_, v___y_1826_);
v___y_1929_ = v___x_1990_;
goto v___jp_1928_;
}
v___jp_1991_:
{
lean_object* v___x_1994_; lean_object* v_a_1995_; lean_object* v___x_1996_; uint8_t v___x_1997_; 
v___x_1994_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg(v___y_1826_);
v_a_1995_ = lean_ctor_get(v___x_1994_, 0);
lean_inc(v_a_1995_);
lean_dec_ref(v___x_1994_);
v___x_1996_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1997_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v___y_1992_, v___x_1996_);
if (v___x_1997_ == 0)
{
lean_object* v___x_1998_; lean_object* v___x_1999_; 
v___x_1998_ = lean_io_mono_nanos_now();
lean_inc_ref(v_lratPath_1814_);
v___x_1999_ = l_Lean_Meta_Tactic_BVDecide_External_satQuery(v_solver_1817_, v_cnfPath_1824_, v_lratPath_1814_, v_timeout_1818_, v_binaryProofs_1819_, v_solverMode_1820_, v___y_1825_, v___y_1826_);
if (lean_obj_tag(v___x_1999_) == 0)
{
lean_object* v_a_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2007_; 
v_a_2000_ = lean_ctor_get(v___x_1999_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1999_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_2002_ = v___x_1999_;
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_a_2000_);
lean_dec(v___x_1999_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2005_; 
if (v_isShared_2003_ == 0)
{
lean_ctor_set_tag(v___x_2002_, 1);
v___x_2005_ = v___x_2002_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_a_2000_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
v___y_1961_ = v___y_1992_;
v___y_1962_ = v_a_1995_;
v___y_1963_ = v___y_1993_;
v___y_1964_ = v___x_1998_;
v_a_1965_ = v___x_2005_;
goto v___jp_1960_;
}
}
}
else
{
lean_object* v_a_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2015_; 
v_a_2008_ = lean_ctor_get(v___x_1999_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_1999_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2010_ = v___x_1999_;
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_a_2008_);
lean_dec(v___x_1999_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2013_; 
if (v_isShared_2011_ == 0)
{
lean_ctor_set_tag(v___x_2010_, 0);
v___x_2013_ = v___x_2010_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_a_2008_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
v___y_1961_ = v___y_1992_;
v___y_1962_ = v_a_1995_;
v___y_1963_ = v___y_1993_;
v___y_1964_ = v___x_1998_;
v_a_1965_ = v___x_2013_;
goto v___jp_1960_;
}
}
}
}
else
{
lean_object* v___x_2016_; lean_object* v___x_2017_; 
v___x_2016_ = lean_io_get_num_heartbeats();
lean_inc_ref(v_lratPath_1814_);
v___x_2017_ = l_Lean_Meta_Tactic_BVDecide_External_satQuery(v_solver_1817_, v_cnfPath_1824_, v_lratPath_1814_, v_timeout_1818_, v_binaryProofs_1819_, v_solverMode_1820_, v___y_1825_, v___y_1826_);
if (lean_obj_tag(v___x_2017_) == 0)
{
lean_object* v_a_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2025_; 
v_a_2018_ = lean_ctor_get(v___x_2017_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_2017_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2020_ = v___x_2017_;
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_a_2018_);
lean_dec(v___x_2017_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2023_; 
if (v_isShared_2021_ == 0)
{
lean_ctor_set_tag(v___x_2020_, 1);
v___x_2023_ = v___x_2020_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_a_2018_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
v___y_1978_ = v___y_1992_;
v___y_1979_ = v_a_1995_;
v___y_1980_ = v___y_1993_;
v___y_1981_ = v___x_2016_;
v_a_1982_ = v___x_2023_;
goto v___jp_1977_;
}
}
}
else
{
lean_object* v_a_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2033_; 
v_a_2026_ = lean_ctor_get(v___x_2017_, 0);
v_isSharedCheck_2033_ = !lean_is_exclusive(v___x_2017_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_2028_ = v___x_2017_;
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_a_2026_);
lean_dec(v___x_2017_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___x_2031_; 
if (v_isShared_2029_ == 0)
{
lean_ctor_set_tag(v___x_2028_, 0);
v___x_2031_ = v___x_2028_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_a_2026_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
v___y_1978_ = v___y_1992_;
v___y_1979_ = v_a_1995_;
v___y_1980_ = v___y_1993_;
v___y_1981_ = v___x_2016_;
v_a_1982_ = v___x_2031_;
goto v___jp_1977_;
}
}
}
}
}
v___jp_2034_:
{
if (v_hasTrace_1850_ == 0)
{
lean_object* v___x_2035_; 
lean_dec_ref(v___f_1816_);
lean_inc_ref(v_lratPath_1814_);
v___x_2035_ = l_Lean_Meta_Tactic_BVDecide_External_satQuery(v_solver_1817_, v_cnfPath_1824_, v_lratPath_1814_, v_timeout_1818_, v_binaryProofs_1819_, v_solverMode_1820_, v___y_1825_, v___y_1826_);
v___y_1929_ = v___x_2035_;
goto v___jp_1928_;
}
else
{
lean_object* v___x_2036_; uint8_t v___x_2037_; 
v___x_2036_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6);
v___x_2037_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1849_, v_options_1847_, v___x_2036_);
if (v___x_2037_ == 0)
{
lean_object* v___x_2038_; uint8_t v___x_2039_; 
v___x_2038_ = l_Lean_trace_profiler;
v___x_2039_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_options_1847_, v___x_2038_);
if (v___x_2039_ == 0)
{
lean_object* v___x_2040_; 
lean_dec_ref(v___f_1816_);
lean_inc_ref(v_lratPath_1814_);
v___x_2040_ = l_Lean_Meta_Tactic_BVDecide_External_satQuery(v_solver_1817_, v_cnfPath_1824_, v_lratPath_1814_, v_timeout_1818_, v_binaryProofs_1819_, v_solverMode_1820_, v___y_1825_, v___y_1826_);
v___y_1929_ = v___x_2040_;
goto v___jp_1928_;
}
else
{
v___y_1992_ = v_options_1847_;
v___y_1993_ = v___x_2037_;
goto v___jp_1991_;
}
}
else
{
v___y_1992_ = v_options_1847_;
v___y_1993_ = v___x_2037_;
goto v___jp_1991_;
}
}
}
v___jp_2041_:
{
if (lean_obj_tag(v___y_2042_) == 0)
{
lean_dec_ref_known(v___y_2042_, 1);
goto v___jp_2034_;
}
else
{
lean_object* v_a_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2050_; 
lean_dec_ref(v_cnfPath_1824_);
lean_dec_ref(v_solver_1817_);
lean_dec_ref(v___f_1816_);
lean_dec_ref(v_lratPath_1814_);
lean_dec_ref(v___f_1813_);
v_a_2043_ = lean_ctor_get(v___y_2042_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___y_2042_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2045_ = v___y_2042_;
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_a_2043_);
lean_dec(v___y_2042_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2048_; 
if (v_isShared_2046_ == 0)
{
v___x_2048_ = v___x_2045_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_a_2043_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__4___boxed(lean_object* v___f_2269_, lean_object* v_lratPath_2270_, lean_object* v_trimProofs_2271_, lean_object* v___f_2272_, lean_object* v_solver_2273_, lean_object* v_timeout_2274_, lean_object* v_binaryProofs_2275_, lean_object* v_solverMode_2276_, lean_object* v___f_2277_, lean_object* v___f_2278_, lean_object* v_cnfHandle_2279_, lean_object* v_cnfPath_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_){
_start:
{
uint8_t v_trimProofs_boxed_2284_; uint8_t v_binaryProofs_boxed_2285_; uint8_t v_solverMode_boxed_2286_; lean_object* v_res_2287_; 
v_trimProofs_boxed_2284_ = lean_unbox(v_trimProofs_2271_);
v_binaryProofs_boxed_2285_ = lean_unbox(v_binaryProofs_2275_);
v_solverMode_boxed_2286_ = lean_unbox(v_solverMode_2276_);
v_res_2287_ = l_Lean_Meta_Tactic_BVDecide_runExternal___lam__4(v___f_2269_, v_lratPath_2270_, v_trimProofs_boxed_2284_, v___f_2272_, v_solver_2273_, v_timeout_2274_, v_binaryProofs_boxed_2285_, v_solverMode_boxed_2286_, v___f_2277_, v___f_2278_, v_cnfHandle_2279_, v_cnfPath_2280_, v___y_2281_, v___y_2282_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
lean_dec(v_cnfHandle_2279_);
lean_dec(v_timeout_2274_);
return v_res_2287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal(lean_object* v_cnf_2291_, lean_object* v_solver_2292_, lean_object* v_lratPath_2293_, uint8_t v_trimProofs_2294_, lean_object* v_timeout_2295_, uint8_t v_binaryProofs_2296_, uint8_t v_solverMode_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_){
_start:
{
lean_object* v___f_2301_; lean_object* v___f_2302_; lean_object* v___f_2303_; lean_object* v___f_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___f_2308_; lean_object* v___x_2309_; 
v___f_2301_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_runExternal___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2301_, 0, v_cnf_2291_);
v___f_2302_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_runExternal___closed__0));
v___f_2303_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_runExternal___closed__1));
v___f_2304_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_runExternal___closed__2));
v___x_2305_ = lean_box(v_trimProofs_2294_);
v___x_2306_ = lean_box(v_binaryProofs_2296_);
v___x_2307_ = lean_box(v_solverMode_2297_);
v___f_2308_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_runExternal___lam__4___boxed), 15, 10);
lean_closure_set(v___f_2308_, 0, v___f_2303_);
lean_closure_set(v___f_2308_, 1, v_lratPath_2293_);
lean_closure_set(v___f_2308_, 2, v___x_2305_);
lean_closure_set(v___f_2308_, 3, v___f_2302_);
lean_closure_set(v___f_2308_, 4, v_solver_2292_);
lean_closure_set(v___f_2308_, 5, v_timeout_2295_);
lean_closure_set(v___f_2308_, 6, v___x_2306_);
lean_closure_set(v___f_2308_, 7, v___x_2307_);
lean_closure_set(v___f_2308_, 8, v___f_2301_);
lean_closure_set(v___f_2308_, 9, v___f_2304_);
v___x_2309_ = l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg(v___f_2308_, v_a_2298_, v_a_2299_);
return v___x_2309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___boxed(lean_object* v_cnf_2310_, lean_object* v_solver_2311_, lean_object* v_lratPath_2312_, lean_object* v_trimProofs_2313_, lean_object* v_timeout_2314_, lean_object* v_binaryProofs_2315_, lean_object* v_solverMode_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_){
_start:
{
uint8_t v_trimProofs_boxed_2320_; uint8_t v_binaryProofs_boxed_2321_; uint8_t v_solverMode_boxed_2322_; lean_object* v_res_2323_; 
v_trimProofs_boxed_2320_ = lean_unbox(v_trimProofs_2313_);
v_binaryProofs_boxed_2321_ = lean_unbox(v_binaryProofs_2315_);
v_solverMode_boxed_2322_ = lean_unbox(v_solverMode_2316_);
v_res_2323_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_cnf_2310_, v_solver_2311_, v_lratPath_2312_, v_trimProofs_boxed_2320_, v_timeout_2314_, v_binaryProofs_boxed_2321_, v_solverMode_boxed_2322_, v_a_2317_, v_a_2318_);
lean_dec(v_a_2318_);
lean_dec_ref(v_a_2317_);
return v_res_2323_;
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
