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
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
lean_object* l_IO_FS_readBinFile(lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_parseLRATProof(lean_object*);
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
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Parsing LRAT file"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__1___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__1___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__1___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__3___boxed(lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__1_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__2_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "sat"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__2_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__12_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__3_value),LEAN_SCALAR_PTR_LITERAL(174, 199, 37, 233, 64, 174, 173, 134)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__4_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__5_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__7;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "LRAT proof has "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__8 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__8_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = " steps after trimming"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__10;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = " steps before trimming"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__11 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__11_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "SAT solver produced invalid LRAT: "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__13;
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
lean_object* v___x_277_; lean_object* v_traceState_278_; lean_object* v_traces_279_; lean_object* v___x_280_; lean_object* v_traceState_281_; lean_object* v_env_282_; lean_object* v_nextMacroScope_283_; lean_object* v_ngen_284_; lean_object* v_auxDeclNGen_285_; lean_object* v_cache_286_; lean_object* v_recordedDeps_287_; lean_object* v_messages_288_; lean_object* v_infoState_289_; lean_object* v_snapshotTasks_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_309_; 
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
v_recordedDeps_287_ = lean_ctor_get(v___x_280_, 6);
v_messages_288_ = lean_ctor_get(v___x_280_, 7);
v_infoState_289_ = lean_ctor_get(v___x_280_, 8);
v_snapshotTasks_290_ = lean_ctor_get(v___x_280_, 9);
v_isSharedCheck_309_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_309_ == 0)
{
v___x_292_ = v___x_280_;
v_isShared_293_ = v_isSharedCheck_309_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_snapshotTasks_290_);
lean_inc(v_infoState_289_);
lean_inc(v_messages_288_);
lean_inc(v_recordedDeps_287_);
lean_inc(v_cache_286_);
lean_inc(v_traceState_281_);
lean_inc(v_auxDeclNGen_285_);
lean_inc(v_ngen_284_);
lean_inc(v_nextMacroScope_283_);
lean_inc(v_env_282_);
lean_dec(v___x_280_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_309_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
uint64_t v_tid_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_307_; 
v_tid_294_ = lean_ctor_get_uint64(v_traceState_281_, sizeof(void*)*1);
v_isSharedCheck_307_ = !lean_is_exclusive(v_traceState_281_);
if (v_isSharedCheck_307_ == 0)
{
lean_object* v_unused_308_; 
v_unused_308_ = lean_ctor_get(v_traceState_281_, 0);
lean_dec(v_unused_308_);
v___x_296_ = v_traceState_281_;
v_isShared_297_ = v_isSharedCheck_307_;
goto v_resetjp_295_;
}
else
{
lean_dec(v_traceState_281_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_307_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_298_; lean_object* v___x_300_; 
v___x_298_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg___closed__1);
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 0, v___x_298_);
v___x_300_ = v___x_296_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v___x_298_);
lean_ctor_set_uint64(v_reuseFailAlloc_306_, sizeof(void*)*1, v_tid_294_);
v___x_300_ = v_reuseFailAlloc_306_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
lean_object* v___x_302_; 
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 4, v___x_300_);
v___x_302_ = v___x_292_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_env_282_);
lean_ctor_set(v_reuseFailAlloc_305_, 1, v_nextMacroScope_283_);
lean_ctor_set(v_reuseFailAlloc_305_, 2, v_ngen_284_);
lean_ctor_set(v_reuseFailAlloc_305_, 3, v_auxDeclNGen_285_);
lean_ctor_set(v_reuseFailAlloc_305_, 4, v___x_300_);
lean_ctor_set(v_reuseFailAlloc_305_, 5, v_cache_286_);
lean_ctor_set(v_reuseFailAlloc_305_, 6, v_recordedDeps_287_);
lean_ctor_set(v_reuseFailAlloc_305_, 7, v_messages_288_);
lean_ctor_set(v_reuseFailAlloc_305_, 8, v_infoState_289_);
lean_ctor_set(v_reuseFailAlloc_305_, 9, v_snapshotTasks_290_);
v___x_302_ = v_reuseFailAlloc_305_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_303_ = lean_st_ref_put(v___y_275_, v___x_302_);
v___x_304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_304_, 0, v_traces_279_);
return v___x_304_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg___boxed(lean_object* v___y_310_, lean_object* v___y_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg(v___y_310_);
lean_dec(v___y_310_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1(lean_object* v___y_313_, lean_object* v___y_314_){
_start:
{
lean_object* v___x_316_; 
v___x_316_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg(v___y_314_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___boxed(lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1(v___y_317_, v___y_318_);
lean_dec(v___y_318_);
lean_dec_ref(v___y_317_);
return v_res_320_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(lean_object* v_opts_321_, lean_object* v_opt_322_){
_start:
{
lean_object* v_name_323_; lean_object* v_defValue_324_; lean_object* v_map_325_; lean_object* v___x_326_; 
v_name_323_ = lean_ctor_get(v_opt_322_, 0);
v_defValue_324_ = lean_ctor_get(v_opt_322_, 1);
v_map_325_ = lean_ctor_get(v_opts_321_, 0);
v___x_326_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_325_, v_name_323_);
if (lean_obj_tag(v___x_326_) == 0)
{
uint8_t v___x_327_; 
v___x_327_ = lean_unbox(v_defValue_324_);
return v___x_327_;
}
else
{
lean_object* v_val_328_; 
v_val_328_ = lean_ctor_get(v___x_326_, 0);
lean_inc(v_val_328_);
lean_dec_ref_known(v___x_326_, 1);
if (lean_obj_tag(v_val_328_) == 1)
{
uint8_t v_v_329_; 
v_v_329_ = lean_ctor_get_uint8(v_val_328_, 0);
lean_dec_ref_known(v_val_328_, 0);
return v_v_329_;
}
else
{
uint8_t v___x_330_; 
lean_dec(v_val_328_);
v___x_330_ = lean_unbox(v_defValue_324_);
return v___x_330_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2___boxed(lean_object* v_opts_331_, lean_object* v_opt_332_){
_start:
{
uint8_t v_res_333_; lean_object* v_r_334_; 
v_res_333_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_opts_331_, v_opt_332_);
lean_dec_ref(v_opt_332_);
lean_dec_ref(v_opts_331_);
v_r_334_ = lean_box(v_res_333_);
return v_r_334_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__4___redArg(lean_object* v_e_335_){
_start:
{
if (lean_obj_tag(v_e_335_) == 0)
{
lean_object* v_a_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_345_; 
v_a_337_ = lean_ctor_get(v_e_335_, 0);
v_isSharedCheck_345_ = !lean_is_exclusive(v_e_335_);
if (v_isSharedCheck_345_ == 0)
{
v___x_339_ = v_e_335_;
v_isShared_340_ = v_isSharedCheck_345_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_a_337_);
lean_dec(v_e_335_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_345_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_341_; lean_object* v___x_343_; 
v___x_341_ = lean_mk_io_user_error(v_a_337_);
if (v_isShared_340_ == 0)
{
lean_ctor_set_tag(v___x_339_, 1);
lean_ctor_set(v___x_339_, 0, v___x_341_);
v___x_343_ = v___x_339_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v___x_341_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
}
else
{
lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_353_; 
v_a_346_ = lean_ctor_get(v_e_335_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v_e_335_);
if (v_isSharedCheck_353_ == 0)
{
v___x_348_ = v_e_335_;
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_a_346_);
lean_dec(v_e_335_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_351_; 
if (v_isShared_349_ == 0)
{
lean_ctor_set_tag(v___x_348_, 0);
v___x_351_ = v___x_348_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_a_346_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__4___redArg___boxed(lean_object* v_e_354_, lean_object* v_a_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__4___redArg(v_e_354_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__4(lean_object* v_00_u03b1_357_, lean_object* v_e_358_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__4___redArg(v_e_358_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__4___boxed(lean_object* v_00_u03b1_361_, lean_object* v_e_362_, lean_object* v_a_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__4(v_00_u03b1_361_, v_e_362_);
return v_res_364_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__0___closed__2(void){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__0___closed__1));
v___x_369_ = l_Lean_MessageData_ofFormat(v___x_368_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__0(lean_object* v_x_370_, lean_object* v___y_371_, lean_object* v___y_372_){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_374_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__0___closed__2, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__0___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__0___closed__2);
v___x_375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_375_, 0, v___x_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__0___boxed(lean_object* v_x_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__0(v_x_376_, v___y_377_, v___y_378_);
lean_dec(v___y_378_);
lean_dec_ref(v___y_377_);
lean_dec_ref(v_x_376_);
return v_res_380_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__1___closed__2(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__1___closed__1));
v___x_385_ = l_Lean_MessageData_ofFormat(v___x_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__1(lean_object* v_x_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_390_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__1___closed__2, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__1___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__1___closed__2);
v___x_391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__1___boxed(lean_object* v_x_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__1(v_x_392_, v___y_393_, v___y_394_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
lean_dec_ref(v_x_392_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__2(lean_object* v_a_397_, lean_object* v_x_398_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = l_Std_Tactic_BVDecide_LRAT_parseLRATProof(v_a_397_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__3(lean_object* v_a_400_, lean_object* v_x_401_){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = l_Lean_Meta_Tactic_BVDecide_LRAT_trim(v_a_400_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__3___boxed(lean_object* v_a_403_, lean_object* v_x_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__3(v_a_403_, v_x_404_);
lean_dec_ref(v_a_403_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5___redArg(lean_object* v_x_406_){
_start:
{
if (lean_obj_tag(v_x_406_) == 0)
{
lean_object* v_a_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_415_; 
v_a_408_ = lean_ctor_get(v_x_406_, 0);
v_isSharedCheck_415_ = !lean_is_exclusive(v_x_406_);
if (v_isSharedCheck_415_ == 0)
{
v___x_410_ = v_x_406_;
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_a_408_);
lean_dec(v_x_406_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_413_; 
if (v_isShared_411_ == 0)
{
lean_ctor_set_tag(v___x_410_, 1);
v___x_413_ = v___x_410_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(1, 1, 0);
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
else
{
lean_object* v_a_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_423_; 
v_a_416_ = lean_ctor_get(v_x_406_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v_x_406_);
if (v_isSharedCheck_423_ == 0)
{
v___x_418_ = v_x_406_;
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_a_416_);
lean_dec(v_x_406_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_421_; 
if (v_isShared_419_ == 0)
{
lean_ctor_set_tag(v___x_418_, 0);
v___x_421_ = v___x_418_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_a_416_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5___redArg___boxed(lean_object* v_x_424_, lean_object* v___y_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5___redArg(v_x_424_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__4_spec__6(size_t v_sz_427_, size_t v_i_428_, lean_object* v_bs_429_){
_start:
{
uint8_t v___x_430_; 
v___x_430_ = lean_usize_dec_lt(v_i_428_, v_sz_427_);
if (v___x_430_ == 0)
{
return v_bs_429_;
}
else
{
lean_object* v_v_431_; lean_object* v_msg_432_; lean_object* v___x_433_; lean_object* v_bs_x27_434_; size_t v___x_435_; size_t v___x_436_; lean_object* v___x_437_; 
v_v_431_ = lean_array_uget_borrowed(v_bs_429_, v_i_428_);
v_msg_432_ = lean_ctor_get(v_v_431_, 1);
lean_inc_ref(v_msg_432_);
v___x_433_ = lean_unsigned_to_nat(0u);
v_bs_x27_434_ = lean_array_uset(v_bs_429_, v_i_428_, v___x_433_);
v___x_435_ = ((size_t)1ULL);
v___x_436_ = lean_usize_add(v_i_428_, v___x_435_);
v___x_437_ = lean_array_uset(v_bs_x27_434_, v_i_428_, v_msg_432_);
v_i_428_ = v___x_436_;
v_bs_429_ = v___x_437_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__4_spec__6___boxed(lean_object* v_sz_439_, lean_object* v_i_440_, lean_object* v_bs_441_){
_start:
{
size_t v_sz_boxed_442_; size_t v_i_boxed_443_; lean_object* v_res_444_; 
v_sz_boxed_442_ = lean_unbox_usize(v_sz_439_);
lean_dec(v_sz_439_);
v_i_boxed_443_ = lean_unbox_usize(v_i_440_);
lean_dec(v_i_440_);
v_res_444_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__4_spec__6(v_sz_boxed_442_, v_i_boxed_443_, v_bs_441_);
return v_res_444_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_445_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_446_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__0);
v___x_447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_447_, 0, v___x_446_);
return v___x_447_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_448_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__1);
v___x_449_ = lean_unsigned_to_nat(0u);
v___x_450_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_450_, 0, v___x_449_);
lean_ctor_set(v___x_450_, 1, v___x_449_);
lean_ctor_set(v___x_450_, 2, v___x_449_);
lean_ctor_set(v___x_450_, 3, v___x_449_);
lean_ctor_set(v___x_450_, 4, v___x_448_);
lean_ctor_set(v___x_450_, 5, v___x_448_);
lean_ctor_set(v___x_450_, 6, v___x_448_);
lean_ctor_set(v___x_450_, 7, v___x_448_);
lean_ctor_set(v___x_450_, 8, v___x_448_);
lean_ctor_set(v___x_450_, 9, v___x_448_);
lean_ctor_set(v___x_450_, 10, v___x_448_);
return v___x_450_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_451_ = lean_unsigned_to_nat(32u);
v___x_452_ = lean_mk_empty_array_with_capacity(v___x_451_);
v___x_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_453_, 0, v___x_452_);
return v___x_453_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_454_ = ((size_t)5ULL);
v___x_455_ = lean_unsigned_to_nat(0u);
v___x_456_ = lean_unsigned_to_nat(32u);
v___x_457_ = lean_mk_empty_array_with_capacity(v___x_456_);
v___x_458_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__3);
v___x_459_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_459_, 0, v___x_458_);
lean_ctor_set(v___x_459_, 1, v___x_457_);
lean_ctor_set(v___x_459_, 2, v___x_455_);
lean_ctor_set(v___x_459_, 3, v___x_455_);
lean_ctor_set_usize(v___x_459_, 4, v___x_454_);
return v___x_459_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_460_ = lean_box(1);
v___x_461_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__4);
v___x_462_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__1);
v___x_463_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_463_, 0, v___x_462_);
lean_ctor_set(v___x_463_, 1, v___x_461_);
lean_ctor_set(v___x_463_, 2, v___x_460_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0(lean_object* v_msgData_464_, lean_object* v___y_465_, lean_object* v___y_466_){
_start:
{
lean_object* v___x_468_; lean_object* v_toCold_469_; lean_object* v_env_470_; lean_object* v_options_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_468_ = lean_st_ref_get(v___y_466_);
v_toCold_469_ = lean_ctor_get(v___y_465_, 0);
v_env_470_ = lean_ctor_get(v___x_468_, 0);
lean_inc_ref(v_env_470_);
lean_dec(v___x_468_);
v_options_471_ = lean_ctor_get(v_toCold_469_, 2);
v___x_472_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__2);
v___x_473_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_471_);
v___x_474_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_474_, 0, v_env_470_);
lean_ctor_set(v___x_474_, 1, v___x_472_);
lean_ctor_set(v___x_474_, 2, v___x_473_);
lean_ctor_set(v___x_474_, 3, v_options_471_);
v___x_475_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_475_, 0, v___x_474_);
lean_ctor_set(v___x_475_, 1, v_msgData_464_);
v___x_476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_476_, 0, v___x_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___boxed(lean_object* v_msgData_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0(v_msgData_477_, v___y_478_, v___y_479_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__4(lean_object* v_oldTraces_482_, lean_object* v_data_483_, lean_object* v_ref_484_, lean_object* v_msg_485_, lean_object* v___y_486_, lean_object* v___y_487_){
_start:
{
lean_object* v_toCold_489_; lean_object* v_currRecDepth_490_; lean_object* v_ref_491_; uint16_t v_optionFlags_492_; uint8_t v_suppressElabErrors_493_; uint8_t v_isRecordingDeps_494_; lean_object* v_ref_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v_traceState_498_; lean_object* v_traces_499_; lean_object* v___x_500_; size_t v_sz_501_; size_t v___x_502_; lean_object* v___x_503_; lean_object* v_msg_504_; lean_object* v___x_505_; lean_object* v_a_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_544_; 
v_toCold_489_ = lean_ctor_get(v___y_486_, 0);
v_currRecDepth_490_ = lean_ctor_get(v___y_486_, 1);
v_ref_491_ = lean_ctor_get(v___y_486_, 2);
v_optionFlags_492_ = lean_ctor_get_uint16(v___y_486_, sizeof(void*)*3);
v_suppressElabErrors_493_ = lean_ctor_get_uint8(v___y_486_, sizeof(void*)*3 + 2);
v_isRecordingDeps_494_ = lean_ctor_get_uint8(v___y_486_, sizeof(void*)*3 + 3);
v_ref_495_ = l_Lean_replaceRef(v_ref_484_, v_ref_491_);
lean_inc(v_currRecDepth_490_);
lean_inc_ref(v_toCold_489_);
v___x_496_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_496_, 0, v_toCold_489_);
lean_ctor_set(v___x_496_, 1, v_currRecDepth_490_);
lean_ctor_set(v___x_496_, 2, v_ref_495_);
lean_ctor_set_uint16(v___x_496_, sizeof(void*)*3, v_optionFlags_492_);
lean_ctor_set_uint8(v___x_496_, sizeof(void*)*3 + 2, v_suppressElabErrors_493_);
lean_ctor_set_uint8(v___x_496_, sizeof(void*)*3 + 3, v_isRecordingDeps_494_);
v___x_497_ = lean_st_ref_get(v___y_487_);
v_traceState_498_ = lean_ctor_get(v___x_497_, 4);
lean_inc_ref(v_traceState_498_);
lean_dec(v___x_497_);
v_traces_499_ = lean_ctor_get(v_traceState_498_, 0);
lean_inc_ref(v_traces_499_);
lean_dec_ref(v_traceState_498_);
v___x_500_ = l_Lean_PersistentArray_toArray___redArg(v_traces_499_);
lean_dec_ref(v_traces_499_);
v_sz_501_ = lean_array_size(v___x_500_);
v___x_502_ = ((size_t)0ULL);
v___x_503_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__4_spec__6(v_sz_501_, v___x_502_, v___x_500_);
v_msg_504_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_504_, 0, v_data_483_);
lean_ctor_set(v_msg_504_, 1, v_msg_485_);
lean_ctor_set(v_msg_504_, 2, v___x_503_);
v___x_505_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0(v_msg_504_, v___x_496_, v___y_487_);
lean_dec_ref_known(v___x_496_, 3);
v_a_506_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_544_ == 0)
{
v___x_508_ = v___x_505_;
v_isShared_509_ = v_isSharedCheck_544_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_a_506_);
lean_dec(v___x_505_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_544_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_510_; lean_object* v_traceState_511_; lean_object* v_env_512_; lean_object* v_nextMacroScope_513_; lean_object* v_ngen_514_; lean_object* v_auxDeclNGen_515_; lean_object* v_cache_516_; lean_object* v_recordedDeps_517_; lean_object* v_messages_518_; lean_object* v_infoState_519_; lean_object* v_snapshotTasks_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_543_; 
v___x_510_ = lean_st_ref_take(v___y_487_);
v_traceState_511_ = lean_ctor_get(v___x_510_, 4);
v_env_512_ = lean_ctor_get(v___x_510_, 0);
v_nextMacroScope_513_ = lean_ctor_get(v___x_510_, 1);
v_ngen_514_ = lean_ctor_get(v___x_510_, 2);
v_auxDeclNGen_515_ = lean_ctor_get(v___x_510_, 3);
v_cache_516_ = lean_ctor_get(v___x_510_, 5);
v_recordedDeps_517_ = lean_ctor_get(v___x_510_, 6);
v_messages_518_ = lean_ctor_get(v___x_510_, 7);
v_infoState_519_ = lean_ctor_get(v___x_510_, 8);
v_snapshotTasks_520_ = lean_ctor_get(v___x_510_, 9);
v_isSharedCheck_543_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_543_ == 0)
{
v___x_522_ = v___x_510_;
v_isShared_523_ = v_isSharedCheck_543_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_snapshotTasks_520_);
lean_inc(v_infoState_519_);
lean_inc(v_messages_518_);
lean_inc(v_recordedDeps_517_);
lean_inc(v_cache_516_);
lean_inc(v_traceState_511_);
lean_inc(v_auxDeclNGen_515_);
lean_inc(v_ngen_514_);
lean_inc(v_nextMacroScope_513_);
lean_inc(v_env_512_);
lean_dec(v___x_510_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_543_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
uint64_t v_tid_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_541_; 
v_tid_524_ = lean_ctor_get_uint64(v_traceState_511_, sizeof(void*)*1);
v_isSharedCheck_541_ = !lean_is_exclusive(v_traceState_511_);
if (v_isSharedCheck_541_ == 0)
{
lean_object* v_unused_542_; 
v_unused_542_ = lean_ctor_get(v_traceState_511_, 0);
lean_dec(v_unused_542_);
v___x_526_ = v_traceState_511_;
v_isShared_527_ = v_isSharedCheck_541_;
goto v_resetjp_525_;
}
else
{
lean_dec(v_traceState_511_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_541_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_532_; 
v___x_528_ = lean_box(0);
v___x_529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_529_, 0, v_ref_484_);
lean_ctor_set(v___x_529_, 1, v_a_506_);
v___x_530_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_482_, v___x_529_);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 0, v___x_530_);
v___x_532_ = v___x_526_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v___x_530_);
lean_ctor_set_uint64(v_reuseFailAlloc_540_, sizeof(void*)*1, v_tid_524_);
v___x_532_ = v_reuseFailAlloc_540_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
lean_object* v___x_534_; 
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 4, v___x_532_);
v___x_534_ = v___x_522_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_env_512_);
lean_ctor_set(v_reuseFailAlloc_539_, 1, v_nextMacroScope_513_);
lean_ctor_set(v_reuseFailAlloc_539_, 2, v_ngen_514_);
lean_ctor_set(v_reuseFailAlloc_539_, 3, v_auxDeclNGen_515_);
lean_ctor_set(v_reuseFailAlloc_539_, 4, v___x_532_);
lean_ctor_set(v_reuseFailAlloc_539_, 5, v_cache_516_);
lean_ctor_set(v_reuseFailAlloc_539_, 6, v_recordedDeps_517_);
lean_ctor_set(v_reuseFailAlloc_539_, 7, v_messages_518_);
lean_ctor_set(v_reuseFailAlloc_539_, 8, v_infoState_519_);
lean_ctor_set(v_reuseFailAlloc_539_, 9, v_snapshotTasks_520_);
v___x_534_ = v_reuseFailAlloc_539_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
lean_object* v___x_535_; lean_object* v___x_537_; 
v___x_535_ = lean_st_ref_put(v___y_487_, v___x_534_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 0, v___x_528_);
v___x_537_ = v___x_508_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v___x_528_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__4___boxed(lean_object* v_oldTraces_545_, lean_object* v_data_546_, lean_object* v_ref_547_, lean_object* v_msg_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__4(v_oldTraces_545_, v_data_546_, v_ref_547_, v_msg_548_, v___y_549_, v___y_550_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
return v_res_552_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__6(lean_object* v_e_553_){
_start:
{
if (lean_obj_tag(v_e_553_) == 0)
{
uint8_t v___x_554_; 
v___x_554_ = 2;
return v___x_554_;
}
else
{
uint8_t v___x_555_; 
v___x_555_ = 0;
return v___x_555_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__6___boxed(lean_object* v_e_556_){
_start:
{
uint8_t v_res_557_; lean_object* v_r_558_; 
v_res_557_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__6(v_e_556_);
lean_dec_ref(v_e_556_);
v_r_558_ = lean_box(v_res_557_);
return v_r_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(lean_object* v_opts_559_, lean_object* v_opt_560_){
_start:
{
lean_object* v_name_561_; lean_object* v_defValue_562_; lean_object* v_map_563_; lean_object* v___x_564_; 
v_name_561_ = lean_ctor_get(v_opt_560_, 0);
v_defValue_562_ = lean_ctor_get(v_opt_560_, 1);
v_map_563_ = lean_ctor_get(v_opts_559_, 0);
v___x_564_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_563_, v_name_561_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_inc(v_defValue_562_);
return v_defValue_562_;
}
else
{
lean_object* v_val_565_; 
v_val_565_ = lean_ctor_get(v___x_564_, 0);
lean_inc(v_val_565_);
lean_dec_ref_known(v___x_564_, 1);
if (lean_obj_tag(v_val_565_) == 3)
{
lean_object* v_v_566_; 
v_v_566_ = lean_ctor_get(v_val_565_, 0);
lean_inc(v_v_566_);
lean_dec_ref_known(v_val_565_, 1);
return v_v_566_;
}
else
{
lean_dec(v_val_565_);
lean_inc(v_defValue_562_);
return v_defValue_562_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7___boxed(lean_object* v_opts_567_, lean_object* v_opt_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(v_opts_567_, v_opt_568_);
lean_dec_ref(v_opt_568_);
lean_dec_ref(v_opts_567_);
return v_res_569_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0(void){
_start:
{
lean_object* v___x_570_; double v___x_571_; 
v___x_570_ = lean_unsigned_to_nat(0u);
v___x_571_ = lean_float_of_nat(v___x_570_);
return v___x_571_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2(void){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_573_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__1));
v___x_574_ = l_Lean_stringToMessageData(v___x_573_);
return v___x_574_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3(void){
_start:
{
lean_object* v___x_575_; double v___x_576_; 
v___x_575_ = lean_unsigned_to_nat(1000u);
v___x_576_ = lean_float_of_nat(v___x_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3(lean_object* v_cls_577_, uint8_t v_collapsed_578_, lean_object* v_tag_579_, lean_object* v_opts_580_, uint8_t v_clsEnabled_581_, lean_object* v_oldTraces_582_, lean_object* v_msg_583_, lean_object* v_resStartStop_584_, lean_object* v___y_585_, lean_object* v___y_586_){
_start:
{
lean_object* v_fst_588_; lean_object* v_snd_589_; lean_object* v___y_591_; lean_object* v___y_592_; lean_object* v_data_593_; lean_object* v_fst_604_; lean_object* v_snd_605_; lean_object* v___x_606_; uint8_t v___x_607_; lean_object* v___y_609_; lean_object* v_a_610_; uint8_t v___y_625_; double v___y_657_; 
v_fst_588_ = lean_ctor_get(v_resStartStop_584_, 0);
lean_inc(v_fst_588_);
v_snd_589_ = lean_ctor_get(v_resStartStop_584_, 1);
lean_inc(v_snd_589_);
lean_dec_ref(v_resStartStop_584_);
v_fst_604_ = lean_ctor_get(v_snd_589_, 0);
lean_inc(v_fst_604_);
v_snd_605_ = lean_ctor_get(v_snd_589_, 1);
lean_inc(v_snd_605_);
lean_dec(v_snd_589_);
v___x_606_ = l_Lean_trace_profiler;
v___x_607_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_opts_580_, v___x_606_);
if (v___x_607_ == 0)
{
v___y_625_ = v___x_607_;
goto v___jp_624_;
}
else
{
lean_object* v___x_662_; uint8_t v___x_663_; 
v___x_662_ = l_Lean_trace_profiler_useHeartbeats;
v___x_663_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_opts_580_, v___x_662_);
if (v___x_663_ == 0)
{
lean_object* v___x_664_; lean_object* v___x_665_; double v___x_666_; double v___x_667_; double v___x_668_; 
v___x_664_ = l_Lean_trace_profiler_threshold;
v___x_665_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(v_opts_580_, v___x_664_);
v___x_666_ = lean_float_of_nat(v___x_665_);
v___x_667_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3);
v___x_668_ = lean_float_div(v___x_666_, v___x_667_);
v___y_657_ = v___x_668_;
goto v___jp_656_;
}
else
{
lean_object* v___x_669_; lean_object* v___x_670_; double v___x_671_; 
v___x_669_ = l_Lean_trace_profiler_threshold;
v___x_670_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(v_opts_580_, v___x_669_);
v___x_671_ = lean_float_of_nat(v___x_670_);
v___y_657_ = v___x_671_;
goto v___jp_656_;
}
}
v___jp_590_:
{
lean_object* v___x_594_; 
lean_inc(v___y_592_);
v___x_594_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__4(v_oldTraces_582_, v_data_593_, v___y_592_, v___y_591_, v___y_585_, v___y_586_);
if (lean_obj_tag(v___x_594_) == 0)
{
lean_object* v___x_595_; 
lean_dec_ref_known(v___x_594_, 1);
v___x_595_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5___redArg(v_fst_588_);
return v___x_595_;
}
else
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_603_; 
lean_dec(v_fst_588_);
v_a_596_ = lean_ctor_get(v___x_594_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_603_ == 0)
{
v___x_598_ = v___x_594_;
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_594_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_601_; 
if (v_isShared_599_ == 0)
{
v___x_601_ = v___x_598_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_a_596_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
}
v___jp_608_:
{
uint8_t v_result_611_; lean_object* v___x_612_; lean_object* v___x_613_; double v___x_614_; lean_object* v_data_615_; 
v_result_611_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__6(v_fst_588_);
v___x_612_ = lean_box(v_result_611_);
v___x_613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
v___x_614_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0);
lean_inc_ref(v_tag_579_);
lean_inc_ref(v___x_613_);
lean_inc(v_cls_577_);
v_data_615_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_615_, 0, v_cls_577_);
lean_ctor_set(v_data_615_, 1, v___x_613_);
lean_ctor_set(v_data_615_, 2, v_tag_579_);
lean_ctor_set_float(v_data_615_, sizeof(void*)*3, v___x_614_);
lean_ctor_set_float(v_data_615_, sizeof(void*)*3 + 8, v___x_614_);
lean_ctor_set_uint8(v_data_615_, sizeof(void*)*3 + 16, v_collapsed_578_);
if (v___x_607_ == 0)
{
lean_dec_ref_known(v___x_613_, 1);
lean_dec(v_snd_605_);
lean_dec(v_fst_604_);
lean_dec_ref(v_tag_579_);
lean_dec(v_cls_577_);
v___y_591_ = v_a_610_;
v___y_592_ = v___y_609_;
v_data_593_ = v_data_615_;
goto v___jp_590_;
}
else
{
lean_object* v_data_616_; double v___x_617_; double v___x_618_; 
lean_dec_ref_known(v_data_615_, 3);
v_data_616_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_616_, 0, v_cls_577_);
lean_ctor_set(v_data_616_, 1, v___x_613_);
lean_ctor_set(v_data_616_, 2, v_tag_579_);
v___x_617_ = lean_unbox_float(v_fst_604_);
lean_dec(v_fst_604_);
lean_ctor_set_float(v_data_616_, sizeof(void*)*3, v___x_617_);
v___x_618_ = lean_unbox_float(v_snd_605_);
lean_dec(v_snd_605_);
lean_ctor_set_float(v_data_616_, sizeof(void*)*3 + 8, v___x_618_);
lean_ctor_set_uint8(v_data_616_, sizeof(void*)*3 + 16, v_collapsed_578_);
v___y_591_ = v_a_610_;
v___y_592_ = v___y_609_;
v_data_593_ = v_data_616_;
goto v___jp_590_;
}
}
v___jp_619_:
{
lean_object* v_ref_620_; lean_object* v___x_621_; 
v_ref_620_ = lean_ctor_get(v___y_585_, 2);
lean_inc(v___y_586_);
lean_inc_ref(v___y_585_);
lean_inc(v_fst_588_);
v___x_621_ = lean_apply_4(v_msg_583_, v_fst_588_, v___y_585_, v___y_586_, lean_box(0));
if (lean_obj_tag(v___x_621_) == 0)
{
lean_object* v_a_622_; 
v_a_622_ = lean_ctor_get(v___x_621_, 0);
lean_inc(v_a_622_);
lean_dec_ref_known(v___x_621_, 1);
v___y_609_ = v_ref_620_;
v_a_610_ = v_a_622_;
goto v___jp_608_;
}
else
{
lean_object* v___x_623_; 
lean_dec_ref_known(v___x_621_, 1);
v___x_623_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2);
v___y_609_ = v_ref_620_;
v_a_610_ = v___x_623_;
goto v___jp_608_;
}
}
v___jp_624_:
{
if (v_clsEnabled_581_ == 0)
{
if (v___y_625_ == 0)
{
lean_object* v___x_626_; lean_object* v_traceState_627_; lean_object* v_env_628_; lean_object* v_nextMacroScope_629_; lean_object* v_ngen_630_; lean_object* v_auxDeclNGen_631_; lean_object* v_cache_632_; lean_object* v_recordedDeps_633_; lean_object* v_messages_634_; lean_object* v_infoState_635_; lean_object* v_snapshotTasks_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_655_; 
lean_dec(v_snd_605_);
lean_dec(v_fst_604_);
lean_dec_ref(v_msg_583_);
lean_dec_ref(v_tag_579_);
lean_dec(v_cls_577_);
v___x_626_ = lean_st_ref_take(v___y_586_);
v_traceState_627_ = lean_ctor_get(v___x_626_, 4);
v_env_628_ = lean_ctor_get(v___x_626_, 0);
v_nextMacroScope_629_ = lean_ctor_get(v___x_626_, 1);
v_ngen_630_ = lean_ctor_get(v___x_626_, 2);
v_auxDeclNGen_631_ = lean_ctor_get(v___x_626_, 3);
v_cache_632_ = lean_ctor_get(v___x_626_, 5);
v_recordedDeps_633_ = lean_ctor_get(v___x_626_, 6);
v_messages_634_ = lean_ctor_get(v___x_626_, 7);
v_infoState_635_ = lean_ctor_get(v___x_626_, 8);
v_snapshotTasks_636_ = lean_ctor_get(v___x_626_, 9);
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_655_ == 0)
{
v___x_638_ = v___x_626_;
v_isShared_639_ = v_isSharedCheck_655_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_snapshotTasks_636_);
lean_inc(v_infoState_635_);
lean_inc(v_messages_634_);
lean_inc(v_recordedDeps_633_);
lean_inc(v_cache_632_);
lean_inc(v_traceState_627_);
lean_inc(v_auxDeclNGen_631_);
lean_inc(v_ngen_630_);
lean_inc(v_nextMacroScope_629_);
lean_inc(v_env_628_);
lean_dec(v___x_626_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_655_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
uint64_t v_tid_640_; lean_object* v_traces_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_654_; 
v_tid_640_ = lean_ctor_get_uint64(v_traceState_627_, sizeof(void*)*1);
v_traces_641_ = lean_ctor_get(v_traceState_627_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v_traceState_627_);
if (v_isSharedCheck_654_ == 0)
{
v___x_643_ = v_traceState_627_;
v_isShared_644_ = v_isSharedCheck_654_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_traces_641_);
lean_dec(v_traceState_627_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_654_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_645_; lean_object* v___x_647_; 
v___x_645_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_582_, v_traces_641_);
lean_dec_ref(v_traces_641_);
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 0, v___x_645_);
v___x_647_ = v___x_643_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_645_);
lean_ctor_set_uint64(v_reuseFailAlloc_653_, sizeof(void*)*1, v_tid_640_);
v___x_647_ = v_reuseFailAlloc_653_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
lean_object* v___x_649_; 
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 4, v___x_647_);
v___x_649_ = v___x_638_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_env_628_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v_nextMacroScope_629_);
lean_ctor_set(v_reuseFailAlloc_652_, 2, v_ngen_630_);
lean_ctor_set(v_reuseFailAlloc_652_, 3, v_auxDeclNGen_631_);
lean_ctor_set(v_reuseFailAlloc_652_, 4, v___x_647_);
lean_ctor_set(v_reuseFailAlloc_652_, 5, v_cache_632_);
lean_ctor_set(v_reuseFailAlloc_652_, 6, v_recordedDeps_633_);
lean_ctor_set(v_reuseFailAlloc_652_, 7, v_messages_634_);
lean_ctor_set(v_reuseFailAlloc_652_, 8, v_infoState_635_);
lean_ctor_set(v_reuseFailAlloc_652_, 9, v_snapshotTasks_636_);
v___x_649_ = v_reuseFailAlloc_652_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = lean_st_ref_put(v___y_586_, v___x_649_);
v___x_651_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5___redArg(v_fst_588_);
return v___x_651_;
}
}
}
}
}
else
{
goto v___jp_619_;
}
}
else
{
goto v___jp_619_;
}
}
v___jp_656_:
{
double v___x_658_; double v___x_659_; double v___x_660_; uint8_t v___x_661_; 
v___x_658_ = lean_unbox_float(v_snd_605_);
v___x_659_ = lean_unbox_float(v_fst_604_);
v___x_660_ = lean_float_sub(v___x_658_, v___x_659_);
v___x_661_ = lean_float_decLt(v___y_657_, v___x_660_);
v___y_625_ = v___x_661_;
goto v___jp_624_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___boxed(lean_object* v_cls_672_, lean_object* v_collapsed_673_, lean_object* v_tag_674_, lean_object* v_opts_675_, lean_object* v_clsEnabled_676_, lean_object* v_oldTraces_677_, lean_object* v_msg_678_, lean_object* v_resStartStop_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_){
_start:
{
uint8_t v_collapsed_boxed_683_; uint8_t v_clsEnabled_boxed_684_; lean_object* v_res_685_; 
v_collapsed_boxed_683_ = lean_unbox(v_collapsed_673_);
v_clsEnabled_boxed_684_ = lean_unbox(v_clsEnabled_676_);
v_res_685_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3(v_cls_672_, v_collapsed_boxed_683_, v_tag_674_, v_opts_675_, v_clsEnabled_boxed_684_, v_oldTraces_677_, v_msg_678_, v_resStartStop_679_, v___y_680_, v___y_681_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec_ref(v_opts_675_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5___redArg(lean_object* v_msg_686_, lean_object* v___y_687_, lean_object* v___y_688_){
_start:
{
lean_object* v_ref_690_; lean_object* v___x_691_; lean_object* v_a_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_700_; 
v_ref_690_ = lean_ctor_get(v___y_687_, 2);
v___x_691_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0(v_msg_686_, v___y_687_, v___y_688_);
v_a_692_ = lean_ctor_get(v___x_691_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_700_ == 0)
{
v___x_694_ = v___x_691_;
v_isShared_695_ = v_isSharedCheck_700_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_a_692_);
lean_dec(v___x_691_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_700_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_696_; lean_object* v___x_698_; 
lean_inc(v_ref_690_);
v___x_696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_696_, 0, v_ref_690_);
lean_ctor_set(v___x_696_, 1, v_a_692_);
if (v_isShared_695_ == 0)
{
lean_ctor_set_tag(v___x_694_, 1);
lean_ctor_set(v___x_694_, 0, v___x_696_);
v___x_698_ = v___x_694_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v___x_696_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5___redArg___boxed(lean_object* v_msg_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5___redArg(v_msg_701_, v___y_702_, v___y_703_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0(lean_object* v_cls_709_, lean_object* v_msg_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
lean_object* v_ref_714_; lean_object* v___x_715_; lean_object* v_a_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_761_; 
v_ref_714_ = lean_ctor_get(v___y_711_, 2);
v___x_715_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0(v_msg_710_, v___y_711_, v___y_712_);
v_a_716_ = lean_ctor_get(v___x_715_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_761_ == 0)
{
v___x_718_ = v___x_715_;
v_isShared_719_ = v_isSharedCheck_761_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_a_716_);
lean_dec(v___x_715_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_761_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_720_; lean_object* v_traceState_721_; lean_object* v_env_722_; lean_object* v_nextMacroScope_723_; lean_object* v_ngen_724_; lean_object* v_auxDeclNGen_725_; lean_object* v_cache_726_; lean_object* v_recordedDeps_727_; lean_object* v_messages_728_; lean_object* v_infoState_729_; lean_object* v_snapshotTasks_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_760_; 
v___x_720_ = lean_st_ref_take(v___y_712_);
v_traceState_721_ = lean_ctor_get(v___x_720_, 4);
v_env_722_ = lean_ctor_get(v___x_720_, 0);
v_nextMacroScope_723_ = lean_ctor_get(v___x_720_, 1);
v_ngen_724_ = lean_ctor_get(v___x_720_, 2);
v_auxDeclNGen_725_ = lean_ctor_get(v___x_720_, 3);
v_cache_726_ = lean_ctor_get(v___x_720_, 5);
v_recordedDeps_727_ = lean_ctor_get(v___x_720_, 6);
v_messages_728_ = lean_ctor_get(v___x_720_, 7);
v_infoState_729_ = lean_ctor_get(v___x_720_, 8);
v_snapshotTasks_730_ = lean_ctor_get(v___x_720_, 9);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_760_ == 0)
{
v___x_732_ = v___x_720_;
v_isShared_733_ = v_isSharedCheck_760_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_snapshotTasks_730_);
lean_inc(v_infoState_729_);
lean_inc(v_messages_728_);
lean_inc(v_recordedDeps_727_);
lean_inc(v_cache_726_);
lean_inc(v_traceState_721_);
lean_inc(v_auxDeclNGen_725_);
lean_inc(v_ngen_724_);
lean_inc(v_nextMacroScope_723_);
lean_inc(v_env_722_);
lean_dec(v___x_720_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_760_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
uint64_t v_tid_734_; lean_object* v_traces_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_759_; 
v_tid_734_ = lean_ctor_get_uint64(v_traceState_721_, sizeof(void*)*1);
v_traces_735_ = lean_ctor_get(v_traceState_721_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v_traceState_721_);
if (v_isSharedCheck_759_ == 0)
{
v___x_737_ = v_traceState_721_;
v_isShared_738_ = v_isSharedCheck_759_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_traces_735_);
lean_dec(v_traceState_721_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_759_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_739_; lean_object* v___x_740_; double v___x_741_; uint8_t v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_750_; 
v___x_739_ = lean_box(0);
v___x_740_ = lean_box(0);
v___x_741_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0);
v___x_742_ = 0;
v___x_743_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0___closed__0));
v___x_744_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_744_, 0, v_cls_709_);
lean_ctor_set(v___x_744_, 1, v___x_740_);
lean_ctor_set(v___x_744_, 2, v___x_743_);
lean_ctor_set_float(v___x_744_, sizeof(void*)*3, v___x_741_);
lean_ctor_set_float(v___x_744_, sizeof(void*)*3 + 8, v___x_741_);
lean_ctor_set_uint8(v___x_744_, sizeof(void*)*3 + 16, v___x_742_);
v___x_745_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0___closed__1));
v___x_746_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_746_, 0, v___x_744_);
lean_ctor_set(v___x_746_, 1, v_a_716_);
lean_ctor_set(v___x_746_, 2, v___x_745_);
lean_inc(v_ref_714_);
v___x_747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_747_, 0, v_ref_714_);
lean_ctor_set(v___x_747_, 1, v___x_746_);
v___x_748_ = l_Lean_PersistentArray_push___redArg(v_traces_735_, v___x_747_);
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 0, v___x_748_);
v___x_750_ = v___x_737_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_748_);
lean_ctor_set_uint64(v_reuseFailAlloc_758_, sizeof(void*)*1, v_tid_734_);
v___x_750_ = v_reuseFailAlloc_758_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
lean_object* v___x_752_; 
if (v_isShared_733_ == 0)
{
lean_ctor_set(v___x_732_, 4, v___x_750_);
v___x_752_ = v___x_732_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_env_722_);
lean_ctor_set(v_reuseFailAlloc_757_, 1, v_nextMacroScope_723_);
lean_ctor_set(v_reuseFailAlloc_757_, 2, v_ngen_724_);
lean_ctor_set(v_reuseFailAlloc_757_, 3, v_auxDeclNGen_725_);
lean_ctor_set(v_reuseFailAlloc_757_, 4, v___x_750_);
lean_ctor_set(v_reuseFailAlloc_757_, 5, v_cache_726_);
lean_ctor_set(v_reuseFailAlloc_757_, 6, v_recordedDeps_727_);
lean_ctor_set(v_reuseFailAlloc_757_, 7, v_messages_728_);
lean_ctor_set(v_reuseFailAlloc_757_, 8, v_infoState_729_);
lean_ctor_set(v_reuseFailAlloc_757_, 9, v_snapshotTasks_730_);
v___x_752_ = v_reuseFailAlloc_757_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
lean_object* v___x_753_; lean_object* v___x_755_; 
v___x_753_ = lean_st_ref_put(v___y_712_, v___x_752_);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 0, v___x_739_);
v___x_755_ = v___x_718_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_739_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0___boxed(lean_object* v_cls_762_, lean_object* v_msg_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0(v_cls_762_, v_msg_763_, v___y_764_, v___y_765_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
return v_res_767_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__7(void){
_start:
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_779_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__4));
v___x_780_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6));
v___x_781_ = l_Lean_Name_append(v___x_780_, v___x_779_);
return v___x_781_;
}
}
static double _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__10(void){
_start:
{
lean_object* v___x_784_; double v___x_785_; 
v___x_784_ = lean_unsigned_to_nat(1000000000u);
v___x_785_ = lean_float_of_nat(v___x_784_);
return v___x_785_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__13(void){
_start:
{
lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_788_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12));
v___x_789_ = l_Lean_stringToMessageData(v___x_788_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load(lean_object* v_lratPath_790_, uint8_t v_trimProofs_791_, lean_object* v_a_792_, lean_object* v_a_793_){
_start:
{
lean_object* v_toCold_795_; lean_object* v_ref_796_; lean_object* v___f_797_; lean_object* v___f_798_; lean_object* v___x_799_; 
v_toCold_795_ = lean_ctor_get(v_a_792_, 0);
v_ref_796_ = lean_ctor_get(v_a_792_, 2);
v___f_797_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__0));
v___f_798_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__1));
v___x_799_ = l_IO_FS_readBinFile(v_lratPath_790_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v_options_800_; lean_object* v_a_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_1234_; 
v_options_800_ = lean_ctor_get(v_toCold_795_, 2);
v_a_801_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_803_ = v___x_799_;
v_isShared_804_ = v_isSharedCheck_1234_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_a_801_);
lean_dec(v___x_799_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_1234_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v_inheritedTraceOptions_805_; uint8_t v_hasTrace_806_; lean_object* v___f_807_; lean_object* v___x_808_; lean_object* v_proof_810_; lean_object* v___y_811_; lean_object* v_options_812_; lean_object* v_inheritedTraceOptions_813_; lean_object* v___y_814_; lean_object* v_proof_846_; lean_object* v___y_847_; lean_object* v___y_848_; lean_object* v___y_855_; lean_object* v___y_856_; lean_object* v___y_857_; uint8_t v___x_859_; lean_object* v___x_860_; uint8_t v___y_862_; lean_object* v___y_863_; lean_object* v___y_864_; lean_object* v___y_865_; lean_object* v___y_866_; lean_object* v___y_867_; lean_object* v_a_868_; uint8_t v___y_878_; lean_object* v___y_879_; lean_object* v___y_880_; lean_object* v___y_881_; lean_object* v___y_882_; lean_object* v___y_883_; lean_object* v_a_884_; uint8_t v___y_887_; lean_object* v___y_888_; lean_object* v___y_889_; lean_object* v___y_890_; lean_object* v___y_891_; lean_object* v___y_892_; lean_object* v_a_893_; uint8_t v___y_906_; lean_object* v___y_907_; lean_object* v___y_908_; lean_object* v___y_909_; lean_object* v___y_910_; lean_object* v___y_911_; lean_object* v_a_912_; uint8_t v___y_915_; lean_object* v___y_916_; lean_object* v___y_917_; lean_object* v___y_918_; lean_object* v___y_919_; lean_object* v___y_920_; lean_object* v___y_994_; lean_object* v___y_995_; lean_object* v___y_996_; lean_object* v___y_997_; lean_object* v_a_1072_; lean_object* v___y_1094_; 
v_inheritedTraceOptions_805_ = lean_ctor_get(v_toCold_795_, 11);
v_hasTrace_806_ = lean_ctor_get_uint8(v_options_800_, sizeof(void*)*1);
v___f_807_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__2), 2, 1);
lean_closure_set(v___f_807_, 0, v_a_801_);
v___x_808_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__4));
v___x_859_ = 1;
v___x_860_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0___closed__0));
if (v_hasTrace_806_ == 0)
{
lean_object* v___x_1096_; 
v___x_1096_ = l_IO_lazyPure___redArg(v___f_807_);
if (lean_obj_tag(v___x_1096_) == 0)
{
lean_object* v_a_1097_; 
v_a_1097_ = lean_ctor_get(v___x_1096_, 0);
lean_inc(v_a_1097_);
lean_dec_ref_known(v___x_1096_, 1);
if (lean_obj_tag(v_a_1097_) == 0)
{
lean_object* v_a_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v_a_1098_ = lean_ctor_get(v_a_1097_, 0);
lean_inc(v_a_1098_);
lean_dec_ref_known(v_a_1097_, 1);
v___x_1099_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__13, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__13);
v___x_1100_ = l_Lean_stringToMessageData(v_a_1098_);
v___x_1101_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1099_);
lean_ctor_set(v___x_1101_, 1, v___x_1100_);
v___x_1102_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5___redArg(v___x_1101_, v_a_792_, v_a_793_);
v___y_1094_ = v___x_1102_;
goto v___jp_1093_;
}
else
{
lean_object* v_a_1103_; 
v_a_1103_ = lean_ctor_get(v_a_1097_, 0);
lean_inc(v_a_1103_);
lean_dec_ref_known(v_a_1097_, 1);
v_a_1072_ = v_a_1103_;
goto v___jp_1071_;
}
}
else
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1115_; 
lean_del_object(v___x_803_);
v_a_1104_ = lean_ctor_get(v___x_1096_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1096_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1106_ = v___x_1096_;
v_isShared_1107_ = v_isSharedCheck_1115_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1096_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1115_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1113_; 
v___x_1108_ = lean_io_error_to_string(v_a_1104_);
v___x_1109_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1108_);
v___x_1110_ = l_Lean_MessageData_ofFormat(v___x_1109_);
lean_inc(v_ref_796_);
v___x_1111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1111_, 0, v_ref_796_);
lean_ctor_set(v___x_1111_, 1, v___x_1110_);
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 0, v___x_1111_);
v___x_1113_ = v___x_1106_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v___x_1111_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
else
{
lean_object* v___x_1116_; uint8_t v___x_1117_; lean_object* v___y_1119_; lean_object* v___y_1120_; lean_object* v_a_1121_; lean_object* v___y_1134_; lean_object* v___y_1135_; lean_object* v_a_1136_; lean_object* v___y_1139_; lean_object* v___y_1140_; lean_object* v_a_1141_; lean_object* v___y_1144_; lean_object* v___y_1145_; lean_object* v_a_1146_; lean_object* v___y_1156_; lean_object* v___y_1157_; lean_object* v_a_1158_; lean_object* v___y_1161_; lean_object* v___y_1162_; lean_object* v_a_1163_; 
v___x_1116_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__7, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__7);
v___x_1117_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_805_, v_options_800_, v___x_1116_);
if (v___x_1117_ == 0)
{
lean_object* v___x_1212_; uint8_t v___x_1213_; 
v___x_1212_ = l_Lean_trace_profiler;
v___x_1213_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_options_800_, v___x_1212_);
if (v___x_1213_ == 0)
{
lean_object* v___x_1214_; 
v___x_1214_ = l_IO_lazyPure___redArg(v___f_807_);
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_object* v_a_1215_; 
v_a_1215_ = lean_ctor_get(v___x_1214_, 0);
lean_inc(v_a_1215_);
lean_dec_ref_known(v___x_1214_, 1);
if (lean_obj_tag(v_a_1215_) == 0)
{
lean_object* v_a_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v_a_1216_ = lean_ctor_get(v_a_1215_, 0);
lean_inc(v_a_1216_);
lean_dec_ref_known(v_a_1215_, 1);
v___x_1217_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__13, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__13);
v___x_1218_ = l_Lean_stringToMessageData(v_a_1216_);
v___x_1219_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1217_);
lean_ctor_set(v___x_1219_, 1, v___x_1218_);
v___x_1220_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5___redArg(v___x_1219_, v_a_792_, v_a_793_);
v___y_1094_ = v___x_1220_;
goto v___jp_1093_;
}
else
{
lean_object* v_a_1221_; 
v_a_1221_ = lean_ctor_get(v_a_1215_, 0);
lean_inc(v_a_1221_);
lean_dec_ref_known(v_a_1215_, 1);
v_a_1072_ = v_a_1221_;
goto v___jp_1071_;
}
}
else
{
lean_object* v_a_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1233_; 
lean_del_object(v___x_803_);
v_a_1222_ = lean_ctor_get(v___x_1214_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1224_ = v___x_1214_;
v_isShared_1225_ = v_isSharedCheck_1233_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_a_1222_);
lean_dec(v___x_1214_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1233_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1231_; 
v___x_1226_ = lean_io_error_to_string(v_a_1222_);
v___x_1227_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1226_);
v___x_1228_ = l_Lean_MessageData_ofFormat(v___x_1227_);
lean_inc(v_ref_796_);
v___x_1229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1229_, 0, v_ref_796_);
lean_ctor_set(v___x_1229_, 1, v___x_1228_);
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 0, v___x_1229_);
v___x_1231_ = v___x_1224_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v___x_1229_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
}
else
{
goto v___jp_1165_;
}
}
else
{
goto v___jp_1165_;
}
v___jp_1118_:
{
lean_object* v___x_1122_; double v___x_1123_; double v___x_1124_; double v___x_1125_; double v___x_1126_; double v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1122_ = lean_io_mono_nanos_now();
v___x_1123_ = lean_float_of_nat(v___y_1120_);
v___x_1124_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__10, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__10);
v___x_1125_ = lean_float_div(v___x_1123_, v___x_1124_);
v___x_1126_ = lean_float_of_nat(v___x_1122_);
v___x_1127_ = lean_float_div(v___x_1126_, v___x_1124_);
v___x_1128_ = lean_box_float(v___x_1125_);
v___x_1129_ = lean_box_float(v___x_1127_);
v___x_1130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1128_);
lean_ctor_set(v___x_1130_, 1, v___x_1129_);
v___x_1131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1131_, 0, v_a_1121_);
lean_ctor_set(v___x_1131_, 1, v___x_1130_);
v___x_1132_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3(v___x_808_, v___x_859_, v___x_860_, v_options_800_, v___x_1117_, v___y_1119_, v___f_798_, v___x_1131_, v_a_792_, v_a_793_);
v___y_1094_ = v___x_1132_;
goto v___jp_1093_;
}
v___jp_1133_:
{
lean_object* v___x_1137_; 
v___x_1137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1137_, 0, v_a_1136_);
v___y_1119_ = v___y_1134_;
v___y_1120_ = v___y_1135_;
v_a_1121_ = v___x_1137_;
goto v___jp_1118_;
}
v___jp_1138_:
{
lean_object* v___x_1142_; 
v___x_1142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1142_, 0, v_a_1141_);
v___y_1119_ = v___y_1139_;
v___y_1120_ = v___y_1140_;
v_a_1121_ = v___x_1142_;
goto v___jp_1118_;
}
v___jp_1143_:
{
lean_object* v___x_1147_; double v___x_1148_; double v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1147_ = lean_io_get_num_heartbeats();
v___x_1148_ = lean_float_of_nat(v___y_1145_);
v___x_1149_ = lean_float_of_nat(v___x_1147_);
v___x_1150_ = lean_box_float(v___x_1148_);
v___x_1151_ = lean_box_float(v___x_1149_);
v___x_1152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1150_);
lean_ctor_set(v___x_1152_, 1, v___x_1151_);
v___x_1153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1153_, 0, v_a_1146_);
lean_ctor_set(v___x_1153_, 1, v___x_1152_);
v___x_1154_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3(v___x_808_, v___x_859_, v___x_860_, v_options_800_, v___x_1117_, v___y_1144_, v___f_798_, v___x_1153_, v_a_792_, v_a_793_);
v___y_1094_ = v___x_1154_;
goto v___jp_1093_;
}
v___jp_1155_:
{
lean_object* v___x_1159_; 
v___x_1159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1159_, 0, v_a_1158_);
v___y_1144_ = v___y_1156_;
v___y_1145_ = v___y_1157_;
v_a_1146_ = v___x_1159_;
goto v___jp_1143_;
}
v___jp_1160_:
{
lean_object* v___x_1164_; 
v___x_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1164_, 0, v_a_1163_);
v___y_1144_ = v___y_1161_;
v___y_1145_ = v___y_1162_;
v_a_1146_ = v___x_1164_;
goto v___jp_1143_;
}
v___jp_1165_:
{
lean_object* v___x_1166_; lean_object* v_a_1167_; lean_object* v___x_1168_; uint8_t v___x_1169_; 
v___x_1166_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg(v_a_793_);
v_a_1167_ = lean_ctor_get(v___x_1166_, 0);
lean_inc(v_a_1167_);
lean_dec_ref(v___x_1166_);
v___x_1168_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1169_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_options_800_, v___x_1168_);
if (v___x_1169_ == 0)
{
lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1170_ = lean_io_mono_nanos_now();
v___x_1171_ = l_IO_lazyPure___redArg(v___f_807_);
if (lean_obj_tag(v___x_1171_) == 0)
{
lean_object* v_a_1172_; 
v_a_1172_ = lean_ctor_get(v___x_1171_, 0);
lean_inc(v_a_1172_);
lean_dec_ref_known(v___x_1171_, 1);
if (lean_obj_tag(v_a_1172_) == 0)
{
lean_object* v_a_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v_a_1178_; 
v_a_1173_ = lean_ctor_get(v_a_1172_, 0);
lean_inc(v_a_1173_);
lean_dec_ref_known(v_a_1172_, 1);
v___x_1174_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__13, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__13);
v___x_1175_ = l_Lean_stringToMessageData(v_a_1173_);
v___x_1176_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1174_);
lean_ctor_set(v___x_1176_, 1, v___x_1175_);
v___x_1177_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5___redArg(v___x_1176_, v_a_792_, v_a_793_);
v_a_1178_ = lean_ctor_get(v___x_1177_, 0);
lean_inc(v_a_1178_);
lean_dec_ref(v___x_1177_);
v___y_1134_ = v_a_1167_;
v___y_1135_ = v___x_1170_;
v_a_1136_ = v_a_1178_;
goto v___jp_1133_;
}
else
{
lean_object* v_a_1179_; 
v_a_1179_ = lean_ctor_get(v_a_1172_, 0);
lean_inc(v_a_1179_);
lean_dec_ref_known(v_a_1172_, 1);
v___y_1139_ = v_a_1167_;
v___y_1140_ = v___x_1170_;
v_a_1141_ = v_a_1179_;
goto v___jp_1138_;
}
}
else
{
lean_object* v_a_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1190_; 
v_a_1180_ = lean_ctor_get(v___x_1171_, 0);
v_isSharedCheck_1190_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1182_ = v___x_1171_;
v_isShared_1183_ = v_isSharedCheck_1190_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_a_1180_);
lean_dec(v___x_1171_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1190_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1184_; lean_object* v___x_1186_; 
v___x_1184_ = lean_io_error_to_string(v_a_1180_);
if (v_isShared_1183_ == 0)
{
lean_ctor_set_tag(v___x_1182_, 3);
lean_ctor_set(v___x_1182_, 0, v___x_1184_);
v___x_1186_ = v___x_1182_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v___x_1184_);
v___x_1186_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1187_ = l_Lean_MessageData_ofFormat(v___x_1186_);
lean_inc(v_ref_796_);
v___x_1188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1188_, 0, v_ref_796_);
lean_ctor_set(v___x_1188_, 1, v___x_1187_);
v___y_1134_ = v_a_1167_;
v___y_1135_ = v___x_1170_;
v_a_1136_ = v___x_1188_;
goto v___jp_1133_;
}
}
}
}
else
{
lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1191_ = lean_io_get_num_heartbeats();
v___x_1192_ = l_IO_lazyPure___redArg(v___f_807_);
if (lean_obj_tag(v___x_1192_) == 0)
{
lean_object* v_a_1193_; 
v_a_1193_ = lean_ctor_get(v___x_1192_, 0);
lean_inc(v_a_1193_);
lean_dec_ref_known(v___x_1192_, 1);
if (lean_obj_tag(v_a_1193_) == 0)
{
lean_object* v_a_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v_a_1199_; 
v_a_1194_ = lean_ctor_get(v_a_1193_, 0);
lean_inc(v_a_1194_);
lean_dec_ref_known(v_a_1193_, 1);
v___x_1195_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__13, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__13);
v___x_1196_ = l_Lean_stringToMessageData(v_a_1194_);
v___x_1197_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1195_);
lean_ctor_set(v___x_1197_, 1, v___x_1196_);
v___x_1198_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5___redArg(v___x_1197_, v_a_792_, v_a_793_);
v_a_1199_ = lean_ctor_get(v___x_1198_, 0);
lean_inc(v_a_1199_);
lean_dec_ref(v___x_1198_);
v___y_1156_ = v_a_1167_;
v___y_1157_ = v___x_1191_;
v_a_1158_ = v_a_1199_;
goto v___jp_1155_;
}
else
{
lean_object* v_a_1200_; 
v_a_1200_ = lean_ctor_get(v_a_1193_, 0);
lean_inc(v_a_1200_);
lean_dec_ref_known(v_a_1193_, 1);
v___y_1161_ = v_a_1167_;
v___y_1162_ = v___x_1191_;
v_a_1163_ = v_a_1200_;
goto v___jp_1160_;
}
}
else
{
lean_object* v_a_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1211_; 
v_a_1201_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1203_ = v___x_1192_;
v_isShared_1204_ = v_isSharedCheck_1211_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_a_1201_);
lean_dec(v___x_1192_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1211_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1205_; lean_object* v___x_1207_; 
v___x_1205_ = lean_io_error_to_string(v_a_1201_);
if (v_isShared_1204_ == 0)
{
lean_ctor_set_tag(v___x_1203_, 3);
lean_ctor_set(v___x_1203_, 0, v___x_1205_);
v___x_1207_ = v___x_1203_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v___x_1205_);
v___x_1207_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1208_ = l_Lean_MessageData_ofFormat(v___x_1207_);
lean_inc(v_ref_796_);
v___x_1209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1209_, 0, v_ref_796_);
lean_ctor_set(v___x_1209_, 1, v___x_1208_);
v___y_1156_ = v_a_1167_;
v___y_1157_ = v___x_1191_;
v_a_1158_ = v___x_1209_;
goto v___jp_1155_;
}
}
}
}
}
}
v___jp_809_:
{
lean_object* v___x_815_; uint8_t v___x_816_; 
v___x_815_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__7, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__7);
v___x_816_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_813_, v_options_812_, v___x_815_);
if (v___x_816_ == 0)
{
lean_object* v___x_818_; 
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 0, v_proof_810_);
v___x_818_ = v___x_803_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_proof_810_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
else
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
lean_del_object(v___x_803_);
v___x_820_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__8));
v___x_821_ = lean_array_get_size(v_proof_810_);
v___x_822_ = l_Nat_reprFast(v___x_821_);
v___x_823_ = lean_string_append(v___x_820_, v___x_822_);
lean_dec_ref(v___x_822_);
v___x_824_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9));
v___x_825_ = lean_string_append(v___x_823_, v___x_824_);
v___x_826_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_826_, 0, v___x_825_);
v___x_827_ = l_Lean_MessageData_ofFormat(v___x_826_);
v___x_828_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0(v___x_808_, v___x_827_, v___y_811_, v___y_814_);
if (lean_obj_tag(v___x_828_) == 0)
{
lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_835_; 
v_isSharedCheck_835_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_835_ == 0)
{
lean_object* v_unused_836_; 
v_unused_836_ = lean_ctor_get(v___x_828_, 0);
lean_dec(v_unused_836_);
v___x_830_ = v___x_828_;
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
else
{
lean_dec(v___x_828_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_833_; 
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 0, v_proof_810_);
v___x_833_ = v___x_830_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_proof_810_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
}
else
{
lean_object* v_a_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_844_; 
lean_dec_ref(v_proof_810_);
v_a_837_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_844_ == 0)
{
v___x_839_ = v___x_828_;
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_a_837_);
lean_dec(v___x_828_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_842_; 
if (v_isShared_840_ == 0)
{
v___x_842_ = v___x_839_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_a_837_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
}
}
v___jp_845_:
{
lean_object* v_toCold_849_; lean_object* v_options_850_; uint8_t v_hasTrace_851_; 
v_toCold_849_ = lean_ctor_get(v___y_847_, 0);
v_options_850_ = lean_ctor_get(v_toCold_849_, 2);
v_hasTrace_851_ = lean_ctor_get_uint8(v_options_850_, sizeof(void*)*1);
if (v_hasTrace_851_ == 0)
{
lean_object* v___x_852_; 
lean_del_object(v___x_803_);
v___x_852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_852_, 0, v_proof_846_);
return v___x_852_;
}
else
{
lean_object* v_inheritedTraceOptions_853_; 
v_inheritedTraceOptions_853_ = lean_ctor_get(v_toCold_849_, 11);
v_proof_810_ = v_proof_846_;
v___y_811_ = v___y_847_;
v_options_812_ = v_options_850_;
v_inheritedTraceOptions_813_ = v_inheritedTraceOptions_853_;
v___y_814_ = v___y_848_;
goto v___jp_809_;
}
}
v___jp_854_:
{
if (lean_obj_tag(v___y_857_) == 0)
{
lean_object* v_a_858_; 
v_a_858_ = lean_ctor_get(v___y_857_, 0);
lean_inc(v_a_858_);
lean_dec_ref_known(v___y_857_, 1);
v_proof_846_ = v_a_858_;
v___y_847_ = v___y_855_;
v___y_848_ = v___y_856_;
goto v___jp_845_;
}
else
{
lean_del_object(v___x_803_);
return v___y_857_;
}
}
v___jp_861_:
{
lean_object* v___x_869_; double v___x_870_; double v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_869_ = lean_io_get_num_heartbeats();
v___x_870_ = lean_float_of_nat(v___y_865_);
v___x_871_ = lean_float_of_nat(v___x_869_);
v___x_872_ = lean_box_float(v___x_870_);
v___x_873_ = lean_box_float(v___x_871_);
v___x_874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_874_, 0, v___x_872_);
lean_ctor_set(v___x_874_, 1, v___x_873_);
v___x_875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_875_, 0, v_a_868_);
lean_ctor_set(v___x_875_, 1, v___x_874_);
v___x_876_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3(v___x_808_, v___x_859_, v___x_860_, v___y_866_, v___y_862_, v___y_867_, v___f_797_, v___x_875_, v___y_863_, v___y_864_);
v___y_855_ = v___y_863_;
v___y_856_ = v___y_864_;
v___y_857_ = v___x_876_;
goto v___jp_854_;
}
v___jp_877_:
{
lean_object* v___x_885_; 
v___x_885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_885_, 0, v_a_884_);
v___y_862_ = v___y_878_;
v___y_863_ = v___y_879_;
v___y_864_ = v___y_881_;
v___y_865_ = v___y_880_;
v___y_866_ = v___y_882_;
v___y_867_ = v___y_883_;
v_a_868_ = v___x_885_;
goto v___jp_861_;
}
v___jp_886_:
{
lean_object* v___x_894_; double v___x_895_; double v___x_896_; double v___x_897_; double v___x_898_; double v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_894_ = lean_io_mono_nanos_now();
v___x_895_ = lean_float_of_nat(v___y_891_);
v___x_896_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__10, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__10);
v___x_897_ = lean_float_div(v___x_895_, v___x_896_);
v___x_898_ = lean_float_of_nat(v___x_894_);
v___x_899_ = lean_float_div(v___x_898_, v___x_896_);
v___x_900_ = lean_box_float(v___x_897_);
v___x_901_ = lean_box_float(v___x_899_);
v___x_902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_900_);
lean_ctor_set(v___x_902_, 1, v___x_901_);
v___x_903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_903_, 0, v_a_893_);
lean_ctor_set(v___x_903_, 1, v___x_902_);
v___x_904_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3(v___x_808_, v___x_859_, v___x_860_, v___y_890_, v___y_887_, v___y_892_, v___f_797_, v___x_903_, v___y_888_, v___y_889_);
v___y_855_ = v___y_888_;
v___y_856_ = v___y_889_;
v___y_857_ = v___x_904_;
goto v___jp_854_;
}
v___jp_905_:
{
lean_object* v___x_913_; 
v___x_913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_913_, 0, v_a_912_);
v___y_887_ = v___y_906_;
v___y_888_ = v___y_907_;
v___y_889_ = v___y_908_;
v___y_890_ = v___y_909_;
v___y_891_ = v___y_910_;
v___y_892_ = v___y_911_;
v_a_893_ = v___x_913_;
goto v___jp_886_;
}
v___jp_914_:
{
lean_object* v___x_921_; lean_object* v_a_922_; lean_object* v___x_923_; uint8_t v___x_924_; 
v___x_921_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg(v___y_918_);
v_a_922_ = lean_ctor_get(v___x_921_, 0);
lean_inc(v_a_922_);
lean_dec_ref(v___x_921_);
v___x_923_ = l_Lean_trace_profiler_useHeartbeats;
v___x_924_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v___y_919_, v___x_923_);
if (v___x_924_ == 0)
{
lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_925_ = lean_io_mono_nanos_now();
v___x_926_ = l_IO_lazyPure___redArg(v___y_916_);
if (lean_obj_tag(v___x_926_) == 0)
{
lean_object* v_a_927_; lean_object* v___x_928_; 
v_a_927_ = lean_ctor_get(v___x_926_, 0);
lean_inc(v_a_927_);
lean_dec_ref_known(v___x_926_, 1);
v___x_928_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__4___redArg(v_a_927_);
if (lean_obj_tag(v___x_928_) == 0)
{
lean_object* v_a_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_936_; 
v_a_929_ = lean_ctor_get(v___x_928_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_936_ == 0)
{
v___x_931_ = v___x_928_;
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_a_929_);
lean_dec(v___x_928_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_934_; 
if (v_isShared_932_ == 0)
{
lean_ctor_set_tag(v___x_931_, 1);
v___x_934_ = v___x_931_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_a_929_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
v___y_887_ = v___y_915_;
v___y_888_ = v___y_917_;
v___y_889_ = v___y_918_;
v___y_890_ = v___y_919_;
v___y_891_ = v___x_925_;
v___y_892_ = v_a_922_;
v_a_893_ = v___x_934_;
goto v___jp_886_;
}
}
}
else
{
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_947_; 
v_a_937_ = lean_ctor_get(v___x_928_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_947_ == 0)
{
v___x_939_ = v___x_928_;
v_isShared_940_ = v_isSharedCheck_947_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v___x_928_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_947_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_941_; lean_object* v___x_943_; 
v___x_941_ = lean_io_error_to_string(v_a_937_);
if (v_isShared_940_ == 0)
{
lean_ctor_set_tag(v___x_939_, 3);
lean_ctor_set(v___x_939_, 0, v___x_941_);
v___x_943_ = v___x_939_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v___x_941_);
v___x_943_ = v_reuseFailAlloc_946_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_944_ = l_Lean_MessageData_ofFormat(v___x_943_);
lean_inc(v___y_920_);
v___x_945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_945_, 0, v___y_920_);
lean_ctor_set(v___x_945_, 1, v___x_944_);
v___y_906_ = v___y_915_;
v___y_907_ = v___y_917_;
v___y_908_ = v___y_918_;
v___y_909_ = v___y_919_;
v___y_910_ = v___x_925_;
v___y_911_ = v_a_922_;
v_a_912_ = v___x_945_;
goto v___jp_905_;
}
}
}
}
else
{
lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_958_; 
v_a_948_ = lean_ctor_get(v___x_926_, 0);
v_isSharedCheck_958_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_958_ == 0)
{
v___x_950_ = v___x_926_;
v_isShared_951_ = v_isSharedCheck_958_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v___x_926_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_958_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_952_; lean_object* v___x_954_; 
v___x_952_ = lean_io_error_to_string(v_a_948_);
if (v_isShared_951_ == 0)
{
lean_ctor_set_tag(v___x_950_, 3);
lean_ctor_set(v___x_950_, 0, v___x_952_);
v___x_954_ = v___x_950_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v___x_952_);
v___x_954_ = v_reuseFailAlloc_957_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_955_ = l_Lean_MessageData_ofFormat(v___x_954_);
lean_inc(v___y_920_);
v___x_956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_956_, 0, v___y_920_);
lean_ctor_set(v___x_956_, 1, v___x_955_);
v___y_906_ = v___y_915_;
v___y_907_ = v___y_917_;
v___y_908_ = v___y_918_;
v___y_909_ = v___y_919_;
v___y_910_ = v___x_925_;
v___y_911_ = v_a_922_;
v_a_912_ = v___x_956_;
goto v___jp_905_;
}
}
}
}
else
{
lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_959_ = lean_io_get_num_heartbeats();
v___x_960_ = l_IO_lazyPure___redArg(v___y_916_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_a_961_; lean_object* v___x_962_; 
v_a_961_ = lean_ctor_get(v___x_960_, 0);
lean_inc(v_a_961_);
lean_dec_ref_known(v___x_960_, 1);
v___x_962_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__4___redArg(v_a_961_);
if (lean_obj_tag(v___x_962_) == 0)
{
lean_object* v_a_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_970_; 
v_a_963_ = lean_ctor_get(v___x_962_, 0);
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_970_ == 0)
{
v___x_965_ = v___x_962_;
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_a_963_);
lean_dec(v___x_962_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_968_; 
if (v_isShared_966_ == 0)
{
lean_ctor_set_tag(v___x_965_, 1);
v___x_968_ = v___x_965_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_a_963_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
v___y_862_ = v___y_915_;
v___y_863_ = v___y_917_;
v___y_864_ = v___y_918_;
v___y_865_ = v___x_959_;
v___y_866_ = v___y_919_;
v___y_867_ = v_a_922_;
v_a_868_ = v___x_968_;
goto v___jp_861_;
}
}
}
else
{
lean_object* v_a_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_981_; 
v_a_971_ = lean_ctor_get(v___x_962_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_981_ == 0)
{
v___x_973_ = v___x_962_;
v_isShared_974_ = v_isSharedCheck_981_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_a_971_);
lean_dec(v___x_962_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_981_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___x_975_; lean_object* v___x_977_; 
v___x_975_ = lean_io_error_to_string(v_a_971_);
if (v_isShared_974_ == 0)
{
lean_ctor_set_tag(v___x_973_, 3);
lean_ctor_set(v___x_973_, 0, v___x_975_);
v___x_977_ = v___x_973_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v___x_975_);
v___x_977_ = v_reuseFailAlloc_980_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_978_ = l_Lean_MessageData_ofFormat(v___x_977_);
lean_inc(v___y_920_);
v___x_979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_979_, 0, v___y_920_);
lean_ctor_set(v___x_979_, 1, v___x_978_);
v___y_878_ = v___y_915_;
v___y_879_ = v___y_917_;
v___y_880_ = v___x_959_;
v___y_881_ = v___y_918_;
v___y_882_ = v___y_919_;
v___y_883_ = v_a_922_;
v_a_884_ = v___x_979_;
goto v___jp_877_;
}
}
}
}
else
{
lean_object* v_a_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_992_; 
v_a_982_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_992_ == 0)
{
v___x_984_ = v___x_960_;
v_isShared_985_ = v_isSharedCheck_992_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_a_982_);
lean_dec(v___x_960_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_992_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v___x_986_; lean_object* v___x_988_; 
v___x_986_ = lean_io_error_to_string(v_a_982_);
if (v_isShared_985_ == 0)
{
lean_ctor_set_tag(v___x_984_, 3);
lean_ctor_set(v___x_984_, 0, v___x_986_);
v___x_988_ = v___x_984_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v___x_986_);
v___x_988_ = v_reuseFailAlloc_991_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_989_ = l_Lean_MessageData_ofFormat(v___x_988_);
lean_inc(v___y_920_);
v___x_990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_990_, 0, v___y_920_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
v___y_878_ = v___y_915_;
v___y_879_ = v___y_917_;
v___y_880_ = v___x_959_;
v___y_881_ = v___y_918_;
v___y_882_ = v___y_919_;
v___y_883_ = v_a_922_;
v_a_884_ = v___x_990_;
goto v___jp_877_;
}
}
}
}
}
v___jp_993_:
{
if (v_trimProofs_791_ == 0)
{
lean_dec_ref(v___y_994_);
v_proof_846_ = v___y_995_;
v___y_847_ = v___y_996_;
v___y_848_ = v___y_997_;
goto v___jp_845_;
}
else
{
lean_object* v_toCold_998_; lean_object* v_options_999_; uint8_t v_hasTrace_1000_; 
lean_dec_ref(v___y_995_);
v_toCold_998_ = lean_ctor_get(v___y_996_, 0);
v_options_999_ = lean_ctor_get(v_toCold_998_, 2);
v_hasTrace_1000_ = lean_ctor_get_uint8(v_options_999_, sizeof(void*)*1);
if (v_hasTrace_1000_ == 0)
{
lean_object* v_ref_1001_; lean_object* v___x_1002_; 
lean_del_object(v___x_803_);
v_ref_1001_ = lean_ctor_get(v___y_996_, 2);
v___x_1002_ = l_IO_lazyPure___redArg(v___y_994_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v_a_1003_; lean_object* v___x_1004_; 
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
lean_inc(v_a_1003_);
lean_dec_ref_known(v___x_1002_, 1);
v___x_1004_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__4___redArg(v_a_1003_);
if (lean_obj_tag(v___x_1004_) == 0)
{
lean_object* v_a_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1012_; 
v_a_1005_ = lean_ctor_get(v___x_1004_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_1007_ = v___x_1004_;
v_isShared_1008_ = v_isSharedCheck_1012_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_a_1005_);
lean_dec(v___x_1004_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1012_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v___x_1010_; 
if (v_isShared_1008_ == 0)
{
v___x_1010_ = v___x_1007_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v_a_1005_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
}
else
{
lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1024_; 
v_a_1013_ = lean_ctor_get(v___x_1004_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1015_ = v___x_1004_;
v_isShared_1016_ = v_isSharedCheck_1024_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v___x_1004_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1024_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1022_; 
v___x_1017_ = lean_io_error_to_string(v_a_1013_);
v___x_1018_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1017_);
v___x_1019_ = l_Lean_MessageData_ofFormat(v___x_1018_);
lean_inc(v_ref_1001_);
v___x_1020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1020_, 0, v_ref_1001_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
if (v_isShared_1016_ == 0)
{
lean_ctor_set(v___x_1015_, 0, v___x_1020_);
v___x_1022_ = v___x_1015_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v___x_1020_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
}
else
{
lean_object* v_a_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1036_; 
v_a_1025_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1027_ = v___x_1002_;
v_isShared_1028_ = v_isSharedCheck_1036_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_dec(v___x_1002_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1036_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1034_; 
v___x_1029_ = lean_io_error_to_string(v_a_1025_);
v___x_1030_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1029_);
v___x_1031_ = l_Lean_MessageData_ofFormat(v___x_1030_);
lean_inc(v_ref_1001_);
v___x_1032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1032_, 0, v_ref_1001_);
lean_ctor_set(v___x_1032_, 1, v___x_1031_);
if (v_isShared_1028_ == 0)
{
lean_ctor_set(v___x_1027_, 0, v___x_1032_);
v___x_1034_ = v___x_1027_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v___x_1032_);
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
else
{
lean_object* v_ref_1037_; lean_object* v_inheritedTraceOptions_1038_; lean_object* v___x_1039_; uint8_t v___x_1040_; 
v_ref_1037_ = lean_ctor_get(v___y_996_, 2);
v_inheritedTraceOptions_1038_ = lean_ctor_get(v_toCold_998_, 11);
v___x_1039_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__7, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__7);
v___x_1040_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1038_, v_options_999_, v___x_1039_);
if (v___x_1040_ == 0)
{
lean_object* v___x_1041_; uint8_t v___x_1042_; 
v___x_1041_ = l_Lean_trace_profiler;
v___x_1042_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_options_999_, v___x_1041_);
if (v___x_1042_ == 0)
{
lean_object* v___x_1043_; 
v___x_1043_ = l_IO_lazyPure___redArg(v___y_994_);
if (lean_obj_tag(v___x_1043_) == 0)
{
lean_object* v_a_1044_; lean_object* v___x_1045_; 
v_a_1044_ = lean_ctor_get(v___x_1043_, 0);
lean_inc(v_a_1044_);
lean_dec_ref_known(v___x_1043_, 1);
v___x_1045_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__4___redArg(v_a_1044_);
if (lean_obj_tag(v___x_1045_) == 0)
{
lean_object* v_a_1046_; 
v_a_1046_ = lean_ctor_get(v___x_1045_, 0);
lean_inc(v_a_1046_);
lean_dec_ref_known(v___x_1045_, 1);
v_proof_810_ = v_a_1046_;
v___y_811_ = v___y_996_;
v_options_812_ = v_options_999_;
v_inheritedTraceOptions_813_ = v_inheritedTraceOptions_1038_;
v___y_814_ = v___y_997_;
goto v___jp_809_;
}
else
{
lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1058_; 
lean_del_object(v___x_803_);
v_a_1047_ = lean_ctor_get(v___x_1045_, 0);
v_isSharedCheck_1058_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1049_ = v___x_1045_;
v_isShared_1050_ = v_isSharedCheck_1058_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v___x_1045_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1058_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1056_; 
v___x_1051_ = lean_io_error_to_string(v_a_1047_);
v___x_1052_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1051_);
v___x_1053_ = l_Lean_MessageData_ofFormat(v___x_1052_);
lean_inc(v_ref_1037_);
v___x_1054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1054_, 0, v_ref_1037_);
lean_ctor_set(v___x_1054_, 1, v___x_1053_);
if (v_isShared_1050_ == 0)
{
lean_ctor_set(v___x_1049_, 0, v___x_1054_);
v___x_1056_ = v___x_1049_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v___x_1054_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
}
else
{
lean_object* v_a_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1070_; 
lean_del_object(v___x_803_);
v_a_1059_ = lean_ctor_get(v___x_1043_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1061_ = v___x_1043_;
v_isShared_1062_ = v_isSharedCheck_1070_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_a_1059_);
lean_dec(v___x_1043_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1070_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1068_; 
v___x_1063_ = lean_io_error_to_string(v_a_1059_);
v___x_1064_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1063_);
v___x_1065_ = l_Lean_MessageData_ofFormat(v___x_1064_);
lean_inc(v_ref_1037_);
v___x_1066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1066_, 0, v_ref_1037_);
lean_ctor_set(v___x_1066_, 1, v___x_1065_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 0, v___x_1066_);
v___x_1068_ = v___x_1061_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v___x_1066_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
}
else
{
v___y_915_ = v___x_1040_;
v___y_916_ = v___y_994_;
v___y_917_ = v___y_996_;
v___y_918_ = v___y_997_;
v___y_919_ = v_options_999_;
v___y_920_ = v_ref_1037_;
goto v___jp_914_;
}
}
else
{
v___y_915_ = v___x_1040_;
v___y_916_ = v___y_994_;
v___y_917_ = v___y_996_;
v___y_918_ = v___y_997_;
v___y_919_ = v_options_999_;
v___y_920_ = v_ref_1037_;
goto v___jp_914_;
}
}
}
}
v___jp_1071_:
{
lean_object* v___f_1073_; 
lean_inc_ref(v_a_1072_);
v___f_1073_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__3___boxed), 2, 1);
lean_closure_set(v___f_1073_, 0, v_a_1072_);
if (v_hasTrace_806_ == 0)
{
v___y_994_ = v___f_1073_;
v___y_995_ = v_a_1072_;
v___y_996_ = v_a_792_;
v___y_997_ = v_a_793_;
goto v___jp_993_;
}
else
{
lean_object* v___x_1074_; uint8_t v___x_1075_; 
v___x_1074_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__7, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__7);
v___x_1075_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_805_, v_options_800_, v___x_1074_);
if (v___x_1075_ == 0)
{
v___y_994_ = v___f_1073_;
v___y_995_ = v_a_1072_;
v___y_996_ = v_a_792_;
v___y_997_ = v_a_793_;
goto v___jp_993_;
}
else
{
lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1076_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__8));
v___x_1077_ = lean_array_get_size(v_a_1072_);
v___x_1078_ = l_Nat_reprFast(v___x_1077_);
v___x_1079_ = lean_string_append(v___x_1076_, v___x_1078_);
lean_dec_ref(v___x_1078_);
v___x_1080_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__11));
v___x_1081_ = lean_string_append(v___x_1079_, v___x_1080_);
v___x_1082_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1081_);
v___x_1083_ = l_Lean_MessageData_ofFormat(v___x_1082_);
v___x_1084_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0(v___x_808_, v___x_1083_, v_a_792_, v_a_793_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_dec_ref_known(v___x_1084_, 1);
v___y_994_ = v___f_1073_;
v___y_995_ = v_a_1072_;
v___y_996_ = v_a_792_;
v___y_997_ = v_a_793_;
goto v___jp_993_;
}
else
{
lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1092_; 
lean_dec_ref(v___f_1073_);
lean_dec_ref(v_a_1072_);
lean_del_object(v___x_803_);
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1087_ = v___x_1084_;
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___x_1084_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1090_; 
if (v_isShared_1088_ == 0)
{
v___x_1090_ = v___x_1087_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_a_1085_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
}
}
}
v___jp_1093_:
{
if (lean_obj_tag(v___y_1094_) == 0)
{
lean_object* v_a_1095_; 
v_a_1095_ = lean_ctor_get(v___y_1094_, 0);
lean_inc(v_a_1095_);
lean_dec_ref_known(v___y_1094_, 1);
v_a_1072_ = v_a_1095_;
goto v___jp_1071_;
}
else
{
lean_del_object(v___x_803_);
return v___y_1094_;
}
}
}
}
else
{
lean_object* v_a_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1246_; 
v_a_1235_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_1246_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1237_ = v___x_799_;
v_isShared_1238_ = v_isSharedCheck_1246_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_a_1235_);
lean_dec(v___x_799_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1246_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1244_; 
v___x_1239_ = lean_io_error_to_string(v_a_1235_);
v___x_1240_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1239_);
v___x_1241_ = l_Lean_MessageData_ofFormat(v___x_1240_);
lean_inc(v_ref_796_);
v___x_1242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1242_, 0, v_ref_796_);
lean_ctor_set(v___x_1242_, 1, v___x_1241_);
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 0, v___x_1242_);
v___x_1244_ = v___x_1237_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v___x_1242_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___boxed(lean_object* v_lratPath_1247_, lean_object* v_trimProofs_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_){
_start:
{
uint8_t v_trimProofs_boxed_1252_; lean_object* v_res_1253_; 
v_trimProofs_boxed_1252_ = lean_unbox(v_trimProofs_1248_);
v_res_1253_ = l_Lean_Meta_Tactic_BVDecide_LratCert_load(v_lratPath_1247_, v_trimProofs_boxed_1252_, v_a_1249_, v_a_1250_);
lean_dec(v_a_1250_);
lean_dec_ref(v_a_1249_);
lean_dec_ref(v_lratPath_1247_);
return v_res_1253_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5(lean_object* v_00_u03b1_1254_, lean_object* v_x_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_){
_start:
{
lean_object* v___x_1259_; 
v___x_1259_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5___redArg(v_x_1255_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1260_, lean_object* v_x_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
lean_object* v_res_1265_; 
v_res_1265_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5(v_00_u03b1_1260_, v_x_1261_, v___y_1262_, v___y_1263_);
lean_dec(v___y_1263_);
lean_dec_ref(v___y_1262_);
return v_res_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5(lean_object* v_00_u03b1_1266_, lean_object* v_msg_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_){
_start:
{
lean_object* v___x_1271_; 
v___x_1271_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5___redArg(v_msg_1267_, v___y_1268_, v___y_1269_);
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5___boxed(lean_object* v_00_u03b1_1272_, lean_object* v_msg_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5(v_00_u03b1_1272_, v_msg_1273_, v___y_1274_, v___y_1275_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(lean_object* v_lratPath_1278_, uint8_t v_trimProofs_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_){
_start:
{
lean_object* v___x_1283_; 
v___x_1283_ = l_Lean_Meta_Tactic_BVDecide_LratCert_load(v_lratPath_1278_, v_trimProofs_1279_, v_a_1280_, v_a_1281_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1292_; 
v_a_1284_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1286_ = v___x_1283_;
v_isShared_1287_ = v_isSharedCheck_1292_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1283_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1292_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1288_; lean_object* v___x_1290_; 
v___x_1288_ = l_Std_Tactic_BVDecide_LRAT_lratProofToString(v_a_1284_);
lean_dec(v_a_1284_);
if (v_isShared_1287_ == 0)
{
lean_ctor_set(v___x_1286_, 0, v___x_1288_);
v___x_1290_ = v___x_1286_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v___x_1288_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
else
{
lean_object* v_a_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1300_; 
v_a_1293_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1300_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1295_ = v___x_1283_;
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_a_1293_);
lean_dec(v___x_1283_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1298_; 
if (v_isShared_1296_ == 0)
{
v___x_1298_ = v___x_1295_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_a_1293_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile___boxed(lean_object* v_lratPath_1301_, lean_object* v_trimProofs_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_){
_start:
{
uint8_t v_trimProofs_boxed_1306_; lean_object* v_res_1307_; 
v_trimProofs_boxed_1306_ = lean_unbox(v_trimProofs_1302_);
v_res_1307_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_1301_, v_trimProofs_boxed_1306_, v_a_1303_, v_a_1304_);
lean_dec(v_a_1304_);
lean_dec_ref(v_a_1303_);
lean_dec_ref(v_lratPath_1301_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg___lam__0(lean_object* v_snd_1308_, lean_object* v_ref_1309_, lean_object* v_a_x3f_1310_){
_start:
{
lean_object* v___x_1312_; 
v___x_1312_ = lean_io_remove_file(v_snd_1308_);
if (lean_obj_tag(v___x_1312_) == 0)
{
lean_object* v_a_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1320_; 
lean_dec(v_ref_1309_);
v_a_1313_ = lean_ctor_get(v___x_1312_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1312_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1315_ = v___x_1312_;
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_a_1313_);
lean_dec(v___x_1312_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1318_; 
if (v_isShared_1316_ == 0)
{
v___x_1318_ = v___x_1315_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_a_1313_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
}
else
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1332_; 
v_a_1321_ = lean_ctor_get(v___x_1312_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1312_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1323_ = v___x_1312_;
v_isShared_1324_ = v_isSharedCheck_1332_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___x_1312_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1332_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1330_; 
v___x_1325_ = lean_io_error_to_string(v_a_1321_);
v___x_1326_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1325_);
v___x_1327_ = l_Lean_MessageData_ofFormat(v___x_1326_);
v___x_1328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1328_, 0, v_ref_1309_);
lean_ctor_set(v___x_1328_, 1, v___x_1327_);
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 0, v___x_1328_);
v___x_1330_ = v___x_1323_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v___x_1328_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg___lam__0___boxed(lean_object* v_snd_1333_, lean_object* v_ref_1334_, lean_object* v_a_x3f_1335_, lean_object* v___y_1336_){
_start:
{
lean_object* v_res_1337_; 
v_res_1337_ = l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg___lam__0(v_snd_1333_, v_ref_1334_, v_a_x3f_1335_);
lean_dec(v_a_x3f_1335_);
lean_dec_ref(v_snd_1333_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg(lean_object* v_f_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
lean_object* v_ref_1342_; lean_object* v___x_1343_; 
v_ref_1342_ = lean_ctor_get(v___y_1339_, 2);
v___x_1343_ = lean_io_create_tempfile();
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_object* v_a_1344_; lean_object* v_fst_1345_; lean_object* v_snd_1346_; lean_object* v_r_1347_; 
v_a_1344_ = lean_ctor_get(v___x_1343_, 0);
lean_inc(v_a_1344_);
lean_dec_ref_known(v___x_1343_, 1);
v_fst_1345_ = lean_ctor_get(v_a_1344_, 0);
lean_inc(v_fst_1345_);
v_snd_1346_ = lean_ctor_get(v_a_1344_, 1);
lean_inc_n(v_snd_1346_, 2);
lean_dec(v_a_1344_);
lean_inc(v___y_1340_);
lean_inc_ref(v___y_1339_);
v_r_1347_ = lean_apply_5(v_f_1338_, v_fst_1345_, v_snd_1346_, v___y_1339_, v___y_1340_, lean_box(0));
if (lean_obj_tag(v_r_1347_) == 0)
{
lean_object* v_a_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1372_; 
v_a_1348_ = lean_ctor_get(v_r_1347_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v_r_1347_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1350_ = v_r_1347_;
v_isShared_1351_ = v_isSharedCheck_1372_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_a_1348_);
lean_dec(v_r_1347_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1372_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v___x_1353_; 
lean_inc(v_a_1348_);
if (v_isShared_1351_ == 0)
{
lean_ctor_set_tag(v___x_1350_, 1);
v___x_1353_ = v___x_1350_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_a_1348_);
v___x_1353_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
lean_object* v___x_1354_; 
lean_inc(v_ref_1342_);
v___x_1354_ = l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg___lam__0(v_snd_1346_, v_ref_1342_, v___x_1353_);
lean_dec_ref(v___x_1353_);
lean_dec(v_snd_1346_);
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1361_; 
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1361_ == 0)
{
lean_object* v_unused_1362_; 
v_unused_1362_ = lean_ctor_get(v___x_1354_, 0);
lean_dec(v_unused_1362_);
v___x_1356_ = v___x_1354_;
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
else
{
lean_dec(v___x_1354_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___x_1359_; 
if (v_isShared_1357_ == 0)
{
lean_ctor_set(v___x_1356_, 0, v_a_1348_);
v___x_1359_ = v___x_1356_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_a_1348_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
else
{
lean_object* v_a_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1370_; 
lean_dec(v_a_1348_);
v_a_1363_ = lean_ctor_get(v___x_1354_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1365_ = v___x_1354_;
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_a_1363_);
lean_dec(v___x_1354_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1368_; 
if (v_isShared_1366_ == 0)
{
v___x_1368_ = v___x_1365_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_a_1363_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
}
}
}
else
{
lean_object* v_a_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
v_a_1373_ = lean_ctor_get(v_r_1347_, 0);
lean_inc(v_a_1373_);
lean_dec_ref_known(v_r_1347_, 1);
v___x_1374_ = lean_box(0);
lean_inc(v_ref_1342_);
v___x_1375_ = l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg___lam__0(v_snd_1346_, v_ref_1342_, v___x_1374_);
lean_dec(v_snd_1346_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1382_; 
v_isSharedCheck_1382_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1382_ == 0)
{
lean_object* v_unused_1383_; 
v_unused_1383_ = lean_ctor_get(v___x_1375_, 0);
lean_dec(v_unused_1383_);
v___x_1377_ = v___x_1375_;
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
else
{
lean_dec(v___x_1375_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v___x_1380_; 
if (v_isShared_1378_ == 0)
{
lean_ctor_set_tag(v___x_1377_, 1);
lean_ctor_set(v___x_1377_, 0, v_a_1373_);
v___x_1380_ = v___x_1377_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v_a_1373_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
}
else
{
lean_object* v_a_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1391_; 
lean_dec(v_a_1373_);
v_a_1384_ = lean_ctor_get(v___x_1375_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1386_ = v___x_1375_;
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_a_1384_);
lean_dec(v___x_1375_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1389_; 
if (v_isShared_1387_ == 0)
{
v___x_1389_ = v___x_1386_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_a_1384_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
}
}
}
else
{
lean_object* v_a_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1403_; 
lean_dec_ref(v_f_1338_);
v_a_1392_ = lean_ctor_get(v___x_1343_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1394_ = v___x_1343_;
v_isShared_1395_ = v_isSharedCheck_1403_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_a_1392_);
lean_dec(v___x_1343_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1403_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1401_; 
v___x_1396_ = lean_io_error_to_string(v_a_1392_);
v___x_1397_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1397_, 0, v___x_1396_);
v___x_1398_ = l_Lean_MessageData_ofFormat(v___x_1397_);
lean_inc(v_ref_1342_);
v___x_1399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1399_, 0, v_ref_1342_);
lean_ctor_set(v___x_1399_, 1, v___x_1398_);
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 0, v___x_1399_);
v___x_1401_ = v___x_1394_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v___x_1399_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg___boxed(lean_object* v_f_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg(v_f_1404_, v___y_1405_, v___y_1406_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3(lean_object* v_00_u03b1_1409_, lean_object* v_f_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
lean_object* v___x_1414_; 
v___x_1414_ = l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg(v_f_1410_, v___y_1411_, v___y_1412_);
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___boxed(lean_object* v_00_u03b1_1415_, lean_object* v_f_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_){
_start:
{
lean_object* v_res_1420_; 
v_res_1420_ = l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3(v_00_u03b1_1415_, v_f_1416_, v___y_1417_, v___y_1418_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
return v_res_1420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__0(lean_object* v_cnf_1421_, lean_object* v_x_1422_){
_start:
{
lean_object* v___x_1423_; 
v___x_1423_ = l_Std_Sat_CNF_dimacs(v_cnf_1421_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__0___boxed(lean_object* v_cnf_1424_, lean_object* v_x_1425_){
_start:
{
lean_object* v_res_1426_; 
v_res_1426_ = l_Lean_Meta_Tactic_BVDecide_runExternal___lam__0(v_cnf_1424_, v_x_1425_);
lean_dec_ref(v_cnf_1424_);
return v_res_1426_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1430_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1___closed__1));
v___x_1431_ = l_Lean_MessageData_ofFormat(v___x_1430_);
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1(lean_object* v_x_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_){
_start:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; 
v___x_1436_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1___closed__2, &l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1___closed__2);
v___x_1437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1437_, 0, v___x_1436_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1___boxed(lean_object* v_x_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1(v_x_1438_, v___y_1439_, v___y_1440_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
lean_dec_ref(v_x_1438_);
return v_res_1442_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2___closed__2(void){
_start:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1446_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2___closed__1));
v___x_1447_ = l_Lean_MessageData_ofFormat(v___x_1446_);
return v___x_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2(lean_object* v_x_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_){
_start:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1452_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2___closed__2, &l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2___closed__2);
v___x_1453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1453_, 0, v___x_1452_);
return v___x_1453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2___boxed(lean_object* v_x_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_){
_start:
{
lean_object* v_res_1458_; 
v_res_1458_ = l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2(v_x_1454_, v___y_1455_, v___y_1456_);
lean_dec(v___y_1456_);
lean_dec_ref(v___y_1455_);
lean_dec_ref(v_x_1454_);
return v_res_1458_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3___closed__2(void){
_start:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1462_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3___closed__1));
v___x_1463_ = l_Lean_MessageData_ofFormat(v___x_1462_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3(lean_object* v_x_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_){
_start:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1468_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3___closed__2, &l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3___closed__2);
v___x_1469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1468_);
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3___boxed(lean_object* v_x_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3(v_x_1470_, v___y_1471_, v___y_1472_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
lean_dec_ref(v_x_1470_);
return v_res_1474_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2_spec__4(lean_object* v_e_1475_){
_start:
{
if (lean_obj_tag(v_e_1475_) == 0)
{
uint8_t v___x_1476_; 
v___x_1476_ = 2;
return v___x_1476_;
}
else
{
uint8_t v___x_1477_; 
v___x_1477_ = 0;
return v___x_1477_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2_spec__4___boxed(lean_object* v_e_1478_){
_start:
{
uint8_t v_res_1479_; lean_object* v_r_1480_; 
v_res_1479_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2_spec__4(v_e_1478_);
lean_dec_ref(v_e_1478_);
v_r_1480_ = lean_box(v_res_1479_);
return v_r_1480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2(lean_object* v_cls_1481_, uint8_t v_collapsed_1482_, lean_object* v_tag_1483_, lean_object* v_opts_1484_, uint8_t v_clsEnabled_1485_, lean_object* v_oldTraces_1486_, lean_object* v_msg_1487_, lean_object* v_resStartStop_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
lean_object* v_fst_1492_; lean_object* v_snd_1493_; lean_object* v___y_1495_; lean_object* v___y_1496_; lean_object* v_data_1497_; lean_object* v_fst_1500_; lean_object* v_snd_1501_; lean_object* v___x_1502_; uint8_t v___x_1503_; lean_object* v___y_1505_; lean_object* v_a_1506_; uint8_t v___y_1521_; double v___y_1553_; 
v_fst_1492_ = lean_ctor_get(v_resStartStop_1488_, 0);
lean_inc(v_fst_1492_);
v_snd_1493_ = lean_ctor_get(v_resStartStop_1488_, 1);
lean_inc(v_snd_1493_);
lean_dec_ref(v_resStartStop_1488_);
v_fst_1500_ = lean_ctor_get(v_snd_1493_, 0);
lean_inc(v_fst_1500_);
v_snd_1501_ = lean_ctor_get(v_snd_1493_, 1);
lean_inc(v_snd_1501_);
lean_dec(v_snd_1493_);
v___x_1502_ = l_Lean_trace_profiler;
v___x_1503_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_opts_1484_, v___x_1502_);
if (v___x_1503_ == 0)
{
v___y_1521_ = v___x_1503_;
goto v___jp_1520_;
}
else
{
lean_object* v___x_1558_; uint8_t v___x_1559_; 
v___x_1558_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1559_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_opts_1484_, v___x_1558_);
if (v___x_1559_ == 0)
{
lean_object* v___x_1560_; lean_object* v___x_1561_; double v___x_1562_; double v___x_1563_; double v___x_1564_; 
v___x_1560_ = l_Lean_trace_profiler_threshold;
v___x_1561_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(v_opts_1484_, v___x_1560_);
v___x_1562_ = lean_float_of_nat(v___x_1561_);
v___x_1563_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3);
v___x_1564_ = lean_float_div(v___x_1562_, v___x_1563_);
v___y_1553_ = v___x_1564_;
goto v___jp_1552_;
}
else
{
lean_object* v___x_1565_; lean_object* v___x_1566_; double v___x_1567_; 
v___x_1565_ = l_Lean_trace_profiler_threshold;
v___x_1566_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(v_opts_1484_, v___x_1565_);
v___x_1567_ = lean_float_of_nat(v___x_1566_);
v___y_1553_ = v___x_1567_;
goto v___jp_1552_;
}
}
v___jp_1494_:
{
lean_object* v___x_1498_; 
lean_inc(v___y_1496_);
v___x_1498_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__4(v_oldTraces_1486_, v_data_1497_, v___y_1496_, v___y_1495_, v___y_1489_, v___y_1490_);
if (lean_obj_tag(v___x_1498_) == 0)
{
lean_object* v___x_1499_; 
lean_dec_ref_known(v___x_1498_, 1);
v___x_1499_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5___redArg(v_fst_1492_);
return v___x_1499_;
}
else
{
lean_dec(v_fst_1492_);
return v___x_1498_;
}
}
v___jp_1504_:
{
uint8_t v_result_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; double v___x_1510_; lean_object* v_data_1511_; 
v_result_1507_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2_spec__4(v_fst_1492_);
v___x_1508_ = lean_box(v_result_1507_);
v___x_1509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1508_);
v___x_1510_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0);
lean_inc_ref(v_tag_1483_);
lean_inc_ref(v___x_1509_);
lean_inc(v_cls_1481_);
v_data_1511_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1511_, 0, v_cls_1481_);
lean_ctor_set(v_data_1511_, 1, v___x_1509_);
lean_ctor_set(v_data_1511_, 2, v_tag_1483_);
lean_ctor_set_float(v_data_1511_, sizeof(void*)*3, v___x_1510_);
lean_ctor_set_float(v_data_1511_, sizeof(void*)*3 + 8, v___x_1510_);
lean_ctor_set_uint8(v_data_1511_, sizeof(void*)*3 + 16, v_collapsed_1482_);
if (v___x_1503_ == 0)
{
lean_dec_ref_known(v___x_1509_, 1);
lean_dec(v_snd_1501_);
lean_dec(v_fst_1500_);
lean_dec_ref(v_tag_1483_);
lean_dec(v_cls_1481_);
v___y_1495_ = v_a_1506_;
v___y_1496_ = v___y_1505_;
v_data_1497_ = v_data_1511_;
goto v___jp_1494_;
}
else
{
lean_object* v_data_1512_; double v___x_1513_; double v___x_1514_; 
lean_dec_ref_known(v_data_1511_, 3);
v_data_1512_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1512_, 0, v_cls_1481_);
lean_ctor_set(v_data_1512_, 1, v___x_1509_);
lean_ctor_set(v_data_1512_, 2, v_tag_1483_);
v___x_1513_ = lean_unbox_float(v_fst_1500_);
lean_dec(v_fst_1500_);
lean_ctor_set_float(v_data_1512_, sizeof(void*)*3, v___x_1513_);
v___x_1514_ = lean_unbox_float(v_snd_1501_);
lean_dec(v_snd_1501_);
lean_ctor_set_float(v_data_1512_, sizeof(void*)*3 + 8, v___x_1514_);
lean_ctor_set_uint8(v_data_1512_, sizeof(void*)*3 + 16, v_collapsed_1482_);
v___y_1495_ = v_a_1506_;
v___y_1496_ = v___y_1505_;
v_data_1497_ = v_data_1512_;
goto v___jp_1494_;
}
}
v___jp_1515_:
{
lean_object* v_ref_1516_; lean_object* v___x_1517_; 
v_ref_1516_ = lean_ctor_get(v___y_1489_, 2);
lean_inc(v___y_1490_);
lean_inc_ref(v___y_1489_);
lean_inc(v_fst_1492_);
v___x_1517_ = lean_apply_4(v_msg_1487_, v_fst_1492_, v___y_1489_, v___y_1490_, lean_box(0));
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v_a_1518_; 
v_a_1518_ = lean_ctor_get(v___x_1517_, 0);
lean_inc(v_a_1518_);
lean_dec_ref_known(v___x_1517_, 1);
v___y_1505_ = v_ref_1516_;
v_a_1506_ = v_a_1518_;
goto v___jp_1504_;
}
else
{
lean_object* v___x_1519_; 
lean_dec_ref_known(v___x_1517_, 1);
v___x_1519_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2);
v___y_1505_ = v_ref_1516_;
v_a_1506_ = v___x_1519_;
goto v___jp_1504_;
}
}
v___jp_1520_:
{
if (v_clsEnabled_1485_ == 0)
{
if (v___y_1521_ == 0)
{
lean_object* v___x_1522_; lean_object* v_traceState_1523_; lean_object* v_env_1524_; lean_object* v_nextMacroScope_1525_; lean_object* v_ngen_1526_; lean_object* v_auxDeclNGen_1527_; lean_object* v_cache_1528_; lean_object* v_recordedDeps_1529_; lean_object* v_messages_1530_; lean_object* v_infoState_1531_; lean_object* v_snapshotTasks_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1551_; 
lean_dec(v_snd_1501_);
lean_dec(v_fst_1500_);
lean_dec_ref(v_msg_1487_);
lean_dec_ref(v_tag_1483_);
lean_dec(v_cls_1481_);
v___x_1522_ = lean_st_ref_take(v___y_1490_);
v_traceState_1523_ = lean_ctor_get(v___x_1522_, 4);
v_env_1524_ = lean_ctor_get(v___x_1522_, 0);
v_nextMacroScope_1525_ = lean_ctor_get(v___x_1522_, 1);
v_ngen_1526_ = lean_ctor_get(v___x_1522_, 2);
v_auxDeclNGen_1527_ = lean_ctor_get(v___x_1522_, 3);
v_cache_1528_ = lean_ctor_get(v___x_1522_, 5);
v_recordedDeps_1529_ = lean_ctor_get(v___x_1522_, 6);
v_messages_1530_ = lean_ctor_get(v___x_1522_, 7);
v_infoState_1531_ = lean_ctor_get(v___x_1522_, 8);
v_snapshotTasks_1532_ = lean_ctor_get(v___x_1522_, 9);
v_isSharedCheck_1551_ = !lean_is_exclusive(v___x_1522_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1534_ = v___x_1522_;
v_isShared_1535_ = v_isSharedCheck_1551_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_snapshotTasks_1532_);
lean_inc(v_infoState_1531_);
lean_inc(v_messages_1530_);
lean_inc(v_recordedDeps_1529_);
lean_inc(v_cache_1528_);
lean_inc(v_traceState_1523_);
lean_inc(v_auxDeclNGen_1527_);
lean_inc(v_ngen_1526_);
lean_inc(v_nextMacroScope_1525_);
lean_inc(v_env_1524_);
lean_dec(v___x_1522_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1551_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
uint64_t v_tid_1536_; lean_object* v_traces_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1550_; 
v_tid_1536_ = lean_ctor_get_uint64(v_traceState_1523_, sizeof(void*)*1);
v_traces_1537_ = lean_ctor_get(v_traceState_1523_, 0);
v_isSharedCheck_1550_ = !lean_is_exclusive(v_traceState_1523_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1539_ = v_traceState_1523_;
v_isShared_1540_ = v_isSharedCheck_1550_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_traces_1537_);
lean_dec(v_traceState_1523_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1550_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1541_; lean_object* v___x_1543_; 
v___x_1541_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1486_, v_traces_1537_);
lean_dec_ref(v_traces_1537_);
if (v_isShared_1540_ == 0)
{
lean_ctor_set(v___x_1539_, 0, v___x_1541_);
v___x_1543_ = v___x_1539_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v___x_1541_);
lean_ctor_set_uint64(v_reuseFailAlloc_1549_, sizeof(void*)*1, v_tid_1536_);
v___x_1543_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
lean_object* v___x_1545_; 
if (v_isShared_1535_ == 0)
{
lean_ctor_set(v___x_1534_, 4, v___x_1543_);
v___x_1545_ = v___x_1534_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_env_1524_);
lean_ctor_set(v_reuseFailAlloc_1548_, 1, v_nextMacroScope_1525_);
lean_ctor_set(v_reuseFailAlloc_1548_, 2, v_ngen_1526_);
lean_ctor_set(v_reuseFailAlloc_1548_, 3, v_auxDeclNGen_1527_);
lean_ctor_set(v_reuseFailAlloc_1548_, 4, v___x_1543_);
lean_ctor_set(v_reuseFailAlloc_1548_, 5, v_cache_1528_);
lean_ctor_set(v_reuseFailAlloc_1548_, 6, v_recordedDeps_1529_);
lean_ctor_set(v_reuseFailAlloc_1548_, 7, v_messages_1530_);
lean_ctor_set(v_reuseFailAlloc_1548_, 8, v_infoState_1531_);
lean_ctor_set(v_reuseFailAlloc_1548_, 9, v_snapshotTasks_1532_);
v___x_1545_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1546_ = lean_st_ref_put(v___y_1490_, v___x_1545_);
v___x_1547_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5___redArg(v_fst_1492_);
return v___x_1547_;
}
}
}
}
}
else
{
goto v___jp_1515_;
}
}
else
{
goto v___jp_1515_;
}
}
v___jp_1552_:
{
double v___x_1554_; double v___x_1555_; double v___x_1556_; uint8_t v___x_1557_; 
v___x_1554_ = lean_unbox_float(v_snd_1501_);
v___x_1555_ = lean_unbox_float(v_fst_1500_);
v___x_1556_ = lean_float_sub(v___x_1554_, v___x_1555_);
v___x_1557_ = lean_float_decLt(v___y_1553_, v___x_1556_);
v___y_1521_ = v___x_1557_;
goto v___jp_1520_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2___boxed(lean_object* v_cls_1568_, lean_object* v_collapsed_1569_, lean_object* v_tag_1570_, lean_object* v_opts_1571_, lean_object* v_clsEnabled_1572_, lean_object* v_oldTraces_1573_, lean_object* v_msg_1574_, lean_object* v_resStartStop_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_){
_start:
{
uint8_t v_collapsed_boxed_1579_; uint8_t v_clsEnabled_boxed_1580_; lean_object* v_res_1581_; 
v_collapsed_boxed_1579_ = lean_unbox(v_collapsed_1569_);
v_clsEnabled_boxed_1580_ = lean_unbox(v_clsEnabled_1572_);
v_res_1581_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2(v_cls_1568_, v_collapsed_boxed_1579_, v_tag_1570_, v_opts_1571_, v_clsEnabled_boxed_1580_, v_oldTraces_1573_, v_msg_1574_, v_resStartStop_1575_, v___y_1576_, v___y_1577_);
lean_dec(v___y_1577_);
lean_dec_ref(v___y_1576_);
lean_dec_ref(v_opts_1571_);
return v_res_1581_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0_spec__0(lean_object* v_e_1582_){
_start:
{
if (lean_obj_tag(v_e_1582_) == 0)
{
uint8_t v___x_1583_; 
v___x_1583_ = 2;
return v___x_1583_;
}
else
{
uint8_t v___x_1584_; 
v___x_1584_ = 0;
return v___x_1584_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0_spec__0___boxed(lean_object* v_e_1585_){
_start:
{
uint8_t v_res_1586_; lean_object* v_r_1587_; 
v_res_1586_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0_spec__0(v_e_1585_);
lean_dec_ref(v_e_1585_);
v_r_1587_ = lean_box(v_res_1586_);
return v_r_1587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0(lean_object* v_cls_1588_, uint8_t v_collapsed_1589_, lean_object* v_tag_1590_, lean_object* v_opts_1591_, uint8_t v_clsEnabled_1592_, lean_object* v_oldTraces_1593_, lean_object* v_msg_1594_, lean_object* v_resStartStop_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_){
_start:
{
lean_object* v_fst_1599_; lean_object* v_snd_1600_; lean_object* v___y_1602_; lean_object* v___y_1603_; lean_object* v_data_1604_; lean_object* v_fst_1615_; lean_object* v_snd_1616_; lean_object* v___x_1617_; uint8_t v___x_1618_; lean_object* v___y_1620_; lean_object* v_a_1621_; uint8_t v___y_1636_; double v___y_1668_; 
v_fst_1599_ = lean_ctor_get(v_resStartStop_1595_, 0);
lean_inc(v_fst_1599_);
v_snd_1600_ = lean_ctor_get(v_resStartStop_1595_, 1);
lean_inc(v_snd_1600_);
lean_dec_ref(v_resStartStop_1595_);
v_fst_1615_ = lean_ctor_get(v_snd_1600_, 0);
lean_inc(v_fst_1615_);
v_snd_1616_ = lean_ctor_get(v_snd_1600_, 1);
lean_inc(v_snd_1616_);
lean_dec(v_snd_1600_);
v___x_1617_ = l_Lean_trace_profiler;
v___x_1618_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_opts_1591_, v___x_1617_);
if (v___x_1618_ == 0)
{
v___y_1636_ = v___x_1618_;
goto v___jp_1635_;
}
else
{
lean_object* v___x_1673_; uint8_t v___x_1674_; 
v___x_1673_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1674_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_opts_1591_, v___x_1673_);
if (v___x_1674_ == 0)
{
lean_object* v___x_1675_; lean_object* v___x_1676_; double v___x_1677_; double v___x_1678_; double v___x_1679_; 
v___x_1675_ = l_Lean_trace_profiler_threshold;
v___x_1676_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(v_opts_1591_, v___x_1675_);
v___x_1677_ = lean_float_of_nat(v___x_1676_);
v___x_1678_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3);
v___x_1679_ = lean_float_div(v___x_1677_, v___x_1678_);
v___y_1668_ = v___x_1679_;
goto v___jp_1667_;
}
else
{
lean_object* v___x_1680_; lean_object* v___x_1681_; double v___x_1682_; 
v___x_1680_ = l_Lean_trace_profiler_threshold;
v___x_1681_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(v_opts_1591_, v___x_1680_);
v___x_1682_ = lean_float_of_nat(v___x_1681_);
v___y_1668_ = v___x_1682_;
goto v___jp_1667_;
}
}
v___jp_1601_:
{
lean_object* v___x_1605_; 
lean_inc(v___y_1602_);
v___x_1605_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__4(v_oldTraces_1593_, v_data_1604_, v___y_1602_, v___y_1603_, v___y_1596_, v___y_1597_);
if (lean_obj_tag(v___x_1605_) == 0)
{
lean_object* v___x_1606_; 
lean_dec_ref_known(v___x_1605_, 1);
v___x_1606_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5___redArg(v_fst_1599_);
return v___x_1606_;
}
else
{
lean_object* v_a_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1614_; 
lean_dec(v_fst_1599_);
v_a_1607_ = lean_ctor_get(v___x_1605_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1605_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1609_ = v___x_1605_;
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_a_1607_);
lean_dec(v___x_1605_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1612_; 
if (v_isShared_1610_ == 0)
{
v___x_1612_ = v___x_1609_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_a_1607_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
}
v___jp_1619_:
{
uint8_t v_result_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; double v___x_1625_; lean_object* v_data_1626_; 
v_result_1622_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0_spec__0(v_fst_1599_);
v___x_1623_ = lean_box(v_result_1622_);
v___x_1624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1623_);
v___x_1625_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0);
lean_inc_ref(v_tag_1590_);
lean_inc_ref(v___x_1624_);
lean_inc(v_cls_1588_);
v_data_1626_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1626_, 0, v_cls_1588_);
lean_ctor_set(v_data_1626_, 1, v___x_1624_);
lean_ctor_set(v_data_1626_, 2, v_tag_1590_);
lean_ctor_set_float(v_data_1626_, sizeof(void*)*3, v___x_1625_);
lean_ctor_set_float(v_data_1626_, sizeof(void*)*3 + 8, v___x_1625_);
lean_ctor_set_uint8(v_data_1626_, sizeof(void*)*3 + 16, v_collapsed_1589_);
if (v___x_1618_ == 0)
{
lean_dec_ref_known(v___x_1624_, 1);
lean_dec(v_snd_1616_);
lean_dec(v_fst_1615_);
lean_dec_ref(v_tag_1590_);
lean_dec(v_cls_1588_);
v___y_1602_ = v___y_1620_;
v___y_1603_ = v_a_1621_;
v_data_1604_ = v_data_1626_;
goto v___jp_1601_;
}
else
{
lean_object* v_data_1627_; double v___x_1628_; double v___x_1629_; 
lean_dec_ref_known(v_data_1626_, 3);
v_data_1627_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1627_, 0, v_cls_1588_);
lean_ctor_set(v_data_1627_, 1, v___x_1624_);
lean_ctor_set(v_data_1627_, 2, v_tag_1590_);
v___x_1628_ = lean_unbox_float(v_fst_1615_);
lean_dec(v_fst_1615_);
lean_ctor_set_float(v_data_1627_, sizeof(void*)*3, v___x_1628_);
v___x_1629_ = lean_unbox_float(v_snd_1616_);
lean_dec(v_snd_1616_);
lean_ctor_set_float(v_data_1627_, sizeof(void*)*3 + 8, v___x_1629_);
lean_ctor_set_uint8(v_data_1627_, sizeof(void*)*3 + 16, v_collapsed_1589_);
v___y_1602_ = v___y_1620_;
v___y_1603_ = v_a_1621_;
v_data_1604_ = v_data_1627_;
goto v___jp_1601_;
}
}
v___jp_1630_:
{
lean_object* v_ref_1631_; lean_object* v___x_1632_; 
v_ref_1631_ = lean_ctor_get(v___y_1596_, 2);
lean_inc(v___y_1597_);
lean_inc_ref(v___y_1596_);
lean_inc(v_fst_1599_);
v___x_1632_ = lean_apply_4(v_msg_1594_, v_fst_1599_, v___y_1596_, v___y_1597_, lean_box(0));
if (lean_obj_tag(v___x_1632_) == 0)
{
lean_object* v_a_1633_; 
v_a_1633_ = lean_ctor_get(v___x_1632_, 0);
lean_inc(v_a_1633_);
lean_dec_ref_known(v___x_1632_, 1);
v___y_1620_ = v_ref_1631_;
v_a_1621_ = v_a_1633_;
goto v___jp_1619_;
}
else
{
lean_object* v___x_1634_; 
lean_dec_ref_known(v___x_1632_, 1);
v___x_1634_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2);
v___y_1620_ = v_ref_1631_;
v_a_1621_ = v___x_1634_;
goto v___jp_1619_;
}
}
v___jp_1635_:
{
if (v_clsEnabled_1592_ == 0)
{
if (v___y_1636_ == 0)
{
lean_object* v___x_1637_; lean_object* v_traceState_1638_; lean_object* v_env_1639_; lean_object* v_nextMacroScope_1640_; lean_object* v_ngen_1641_; lean_object* v_auxDeclNGen_1642_; lean_object* v_cache_1643_; lean_object* v_recordedDeps_1644_; lean_object* v_messages_1645_; lean_object* v_infoState_1646_; lean_object* v_snapshotTasks_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1666_; 
lean_dec(v_snd_1616_);
lean_dec(v_fst_1615_);
lean_dec_ref(v_msg_1594_);
lean_dec_ref(v_tag_1590_);
lean_dec(v_cls_1588_);
v___x_1637_ = lean_st_ref_take(v___y_1597_);
v_traceState_1638_ = lean_ctor_get(v___x_1637_, 4);
v_env_1639_ = lean_ctor_get(v___x_1637_, 0);
v_nextMacroScope_1640_ = lean_ctor_get(v___x_1637_, 1);
v_ngen_1641_ = lean_ctor_get(v___x_1637_, 2);
v_auxDeclNGen_1642_ = lean_ctor_get(v___x_1637_, 3);
v_cache_1643_ = lean_ctor_get(v___x_1637_, 5);
v_recordedDeps_1644_ = lean_ctor_get(v___x_1637_, 6);
v_messages_1645_ = lean_ctor_get(v___x_1637_, 7);
v_infoState_1646_ = lean_ctor_get(v___x_1637_, 8);
v_snapshotTasks_1647_ = lean_ctor_get(v___x_1637_, 9);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1649_ = v___x_1637_;
v_isShared_1650_ = v_isSharedCheck_1666_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_snapshotTasks_1647_);
lean_inc(v_infoState_1646_);
lean_inc(v_messages_1645_);
lean_inc(v_recordedDeps_1644_);
lean_inc(v_cache_1643_);
lean_inc(v_traceState_1638_);
lean_inc(v_auxDeclNGen_1642_);
lean_inc(v_ngen_1641_);
lean_inc(v_nextMacroScope_1640_);
lean_inc(v_env_1639_);
lean_dec(v___x_1637_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1666_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
uint64_t v_tid_1651_; lean_object* v_traces_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1665_; 
v_tid_1651_ = lean_ctor_get_uint64(v_traceState_1638_, sizeof(void*)*1);
v_traces_1652_ = lean_ctor_get(v_traceState_1638_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v_traceState_1638_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1654_ = v_traceState_1638_;
v_isShared_1655_ = v_isSharedCheck_1665_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_traces_1652_);
lean_dec(v_traceState_1638_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1665_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1656_; lean_object* v___x_1658_; 
v___x_1656_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1593_, v_traces_1652_);
lean_dec_ref(v_traces_1652_);
if (v_isShared_1655_ == 0)
{
lean_ctor_set(v___x_1654_, 0, v___x_1656_);
v___x_1658_ = v___x_1654_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v___x_1656_);
lean_ctor_set_uint64(v_reuseFailAlloc_1664_, sizeof(void*)*1, v_tid_1651_);
v___x_1658_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
lean_object* v___x_1660_; 
if (v_isShared_1650_ == 0)
{
lean_ctor_set(v___x_1649_, 4, v___x_1658_);
v___x_1660_ = v___x_1649_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_env_1639_);
lean_ctor_set(v_reuseFailAlloc_1663_, 1, v_nextMacroScope_1640_);
lean_ctor_set(v_reuseFailAlloc_1663_, 2, v_ngen_1641_);
lean_ctor_set(v_reuseFailAlloc_1663_, 3, v_auxDeclNGen_1642_);
lean_ctor_set(v_reuseFailAlloc_1663_, 4, v___x_1658_);
lean_ctor_set(v_reuseFailAlloc_1663_, 5, v_cache_1643_);
lean_ctor_set(v_reuseFailAlloc_1663_, 6, v_recordedDeps_1644_);
lean_ctor_set(v_reuseFailAlloc_1663_, 7, v_messages_1645_);
lean_ctor_set(v_reuseFailAlloc_1663_, 8, v_infoState_1646_);
lean_ctor_set(v_reuseFailAlloc_1663_, 9, v_snapshotTasks_1647_);
v___x_1660_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
lean_object* v___x_1661_; lean_object* v___x_1662_; 
v___x_1661_ = lean_st_ref_put(v___y_1597_, v___x_1660_);
v___x_1662_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5___redArg(v_fst_1599_);
return v___x_1662_;
}
}
}
}
}
else
{
goto v___jp_1630_;
}
}
else
{
goto v___jp_1630_;
}
}
v___jp_1667_:
{
double v___x_1669_; double v___x_1670_; double v___x_1671_; uint8_t v___x_1672_; 
v___x_1669_ = lean_unbox_float(v_snd_1616_);
v___x_1670_ = lean_unbox_float(v_fst_1615_);
v___x_1671_ = lean_float_sub(v___x_1669_, v___x_1670_);
v___x_1672_ = lean_float_decLt(v___y_1668_, v___x_1671_);
v___y_1636_ = v___x_1672_;
goto v___jp_1635_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0___boxed(lean_object* v_cls_1683_, lean_object* v_collapsed_1684_, lean_object* v_tag_1685_, lean_object* v_opts_1686_, lean_object* v_clsEnabled_1687_, lean_object* v_oldTraces_1688_, lean_object* v_msg_1689_, lean_object* v_resStartStop_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_){
_start:
{
uint8_t v_collapsed_boxed_1694_; uint8_t v_clsEnabled_boxed_1695_; lean_object* v_res_1696_; 
v_collapsed_boxed_1694_ = lean_unbox(v_collapsed_1684_);
v_clsEnabled_boxed_1695_ = lean_unbox(v_clsEnabled_1687_);
v_res_1696_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0(v_cls_1683_, v_collapsed_boxed_1694_, v_tag_1685_, v_opts_1686_, v_clsEnabled_boxed_1695_, v_oldTraces_1688_, v_msg_1689_, v_resStartStop_1690_, v___y_1691_, v___y_1692_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
lean_dec_ref(v_opts_1686_);
return v_res_1696_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1_spec__2(lean_object* v_e_1697_){
_start:
{
if (lean_obj_tag(v_e_1697_) == 0)
{
uint8_t v___x_1698_; 
v___x_1698_ = 2;
return v___x_1698_;
}
else
{
uint8_t v___x_1699_; 
v___x_1699_ = 0;
return v___x_1699_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1_spec__2___boxed(lean_object* v_e_1700_){
_start:
{
uint8_t v_res_1701_; lean_object* v_r_1702_; 
v_res_1701_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1_spec__2(v_e_1700_);
lean_dec_ref(v_e_1700_);
v_r_1702_ = lean_box(v_res_1701_);
return v_r_1702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1(lean_object* v_cls_1703_, uint8_t v_collapsed_1704_, lean_object* v_tag_1705_, lean_object* v_opts_1706_, uint8_t v_clsEnabled_1707_, lean_object* v_oldTraces_1708_, lean_object* v_msg_1709_, lean_object* v_resStartStop_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_){
_start:
{
lean_object* v_fst_1714_; lean_object* v_snd_1715_; lean_object* v___y_1717_; lean_object* v___y_1718_; lean_object* v_data_1719_; lean_object* v_fst_1730_; lean_object* v_snd_1731_; lean_object* v___x_1732_; uint8_t v___x_1733_; lean_object* v___y_1735_; lean_object* v_a_1736_; uint8_t v___y_1751_; double v___y_1783_; 
v_fst_1714_ = lean_ctor_get(v_resStartStop_1710_, 0);
lean_inc(v_fst_1714_);
v_snd_1715_ = lean_ctor_get(v_resStartStop_1710_, 1);
lean_inc(v_snd_1715_);
lean_dec_ref(v_resStartStop_1710_);
v_fst_1730_ = lean_ctor_get(v_snd_1715_, 0);
lean_inc(v_fst_1730_);
v_snd_1731_ = lean_ctor_get(v_snd_1715_, 1);
lean_inc(v_snd_1731_);
lean_dec(v_snd_1715_);
v___x_1732_ = l_Lean_trace_profiler;
v___x_1733_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_opts_1706_, v___x_1732_);
if (v___x_1733_ == 0)
{
v___y_1751_ = v___x_1733_;
goto v___jp_1750_;
}
else
{
lean_object* v___x_1788_; uint8_t v___x_1789_; 
v___x_1788_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1789_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_opts_1706_, v___x_1788_);
if (v___x_1789_ == 0)
{
lean_object* v___x_1790_; lean_object* v___x_1791_; double v___x_1792_; double v___x_1793_; double v___x_1794_; 
v___x_1790_ = l_Lean_trace_profiler_threshold;
v___x_1791_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(v_opts_1706_, v___x_1790_);
v___x_1792_ = lean_float_of_nat(v___x_1791_);
v___x_1793_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3);
v___x_1794_ = lean_float_div(v___x_1792_, v___x_1793_);
v___y_1783_ = v___x_1794_;
goto v___jp_1782_;
}
else
{
lean_object* v___x_1795_; lean_object* v___x_1796_; double v___x_1797_; 
v___x_1795_ = l_Lean_trace_profiler_threshold;
v___x_1796_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(v_opts_1706_, v___x_1795_);
v___x_1797_ = lean_float_of_nat(v___x_1796_);
v___y_1783_ = v___x_1797_;
goto v___jp_1782_;
}
}
v___jp_1716_:
{
lean_object* v___x_1720_; 
lean_inc(v___y_1718_);
v___x_1720_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__4(v_oldTraces_1708_, v_data_1719_, v___y_1718_, v___y_1717_, v___y_1711_, v___y_1712_);
if (lean_obj_tag(v___x_1720_) == 0)
{
lean_object* v___x_1721_; 
lean_dec_ref_known(v___x_1720_, 1);
v___x_1721_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5___redArg(v_fst_1714_);
return v___x_1721_;
}
else
{
lean_object* v_a_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1729_; 
lean_dec(v_fst_1714_);
v_a_1722_ = lean_ctor_get(v___x_1720_, 0);
v_isSharedCheck_1729_ = !lean_is_exclusive(v___x_1720_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1724_ = v___x_1720_;
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_a_1722_);
lean_dec(v___x_1720_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1727_; 
if (v_isShared_1725_ == 0)
{
v___x_1727_ = v___x_1724_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v_a_1722_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
return v___x_1727_;
}
}
}
}
v___jp_1734_:
{
uint8_t v_result_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; double v___x_1740_; lean_object* v_data_1741_; 
v_result_1737_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1_spec__2(v_fst_1714_);
v___x_1738_ = lean_box(v_result_1737_);
v___x_1739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1738_);
v___x_1740_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0);
lean_inc_ref(v_tag_1705_);
lean_inc_ref(v___x_1739_);
lean_inc(v_cls_1703_);
v_data_1741_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1741_, 0, v_cls_1703_);
lean_ctor_set(v_data_1741_, 1, v___x_1739_);
lean_ctor_set(v_data_1741_, 2, v_tag_1705_);
lean_ctor_set_float(v_data_1741_, sizeof(void*)*3, v___x_1740_);
lean_ctor_set_float(v_data_1741_, sizeof(void*)*3 + 8, v___x_1740_);
lean_ctor_set_uint8(v_data_1741_, sizeof(void*)*3 + 16, v_collapsed_1704_);
if (v___x_1733_ == 0)
{
lean_dec_ref_known(v___x_1739_, 1);
lean_dec(v_snd_1731_);
lean_dec(v_fst_1730_);
lean_dec_ref(v_tag_1705_);
lean_dec(v_cls_1703_);
v___y_1717_ = v_a_1736_;
v___y_1718_ = v___y_1735_;
v_data_1719_ = v_data_1741_;
goto v___jp_1716_;
}
else
{
lean_object* v_data_1742_; double v___x_1743_; double v___x_1744_; 
lean_dec_ref_known(v_data_1741_, 3);
v_data_1742_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1742_, 0, v_cls_1703_);
lean_ctor_set(v_data_1742_, 1, v___x_1739_);
lean_ctor_set(v_data_1742_, 2, v_tag_1705_);
v___x_1743_ = lean_unbox_float(v_fst_1730_);
lean_dec(v_fst_1730_);
lean_ctor_set_float(v_data_1742_, sizeof(void*)*3, v___x_1743_);
v___x_1744_ = lean_unbox_float(v_snd_1731_);
lean_dec(v_snd_1731_);
lean_ctor_set_float(v_data_1742_, sizeof(void*)*3 + 8, v___x_1744_);
lean_ctor_set_uint8(v_data_1742_, sizeof(void*)*3 + 16, v_collapsed_1704_);
v___y_1717_ = v_a_1736_;
v___y_1718_ = v___y_1735_;
v_data_1719_ = v_data_1742_;
goto v___jp_1716_;
}
}
v___jp_1745_:
{
lean_object* v_ref_1746_; lean_object* v___x_1747_; 
v_ref_1746_ = lean_ctor_get(v___y_1711_, 2);
lean_inc(v___y_1712_);
lean_inc_ref(v___y_1711_);
lean_inc(v_fst_1714_);
v___x_1747_ = lean_apply_4(v_msg_1709_, v_fst_1714_, v___y_1711_, v___y_1712_, lean_box(0));
if (lean_obj_tag(v___x_1747_) == 0)
{
lean_object* v_a_1748_; 
v_a_1748_ = lean_ctor_get(v___x_1747_, 0);
lean_inc(v_a_1748_);
lean_dec_ref_known(v___x_1747_, 1);
v___y_1735_ = v_ref_1746_;
v_a_1736_ = v_a_1748_;
goto v___jp_1734_;
}
else
{
lean_object* v___x_1749_; 
lean_dec_ref_known(v___x_1747_, 1);
v___x_1749_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2);
v___y_1735_ = v_ref_1746_;
v_a_1736_ = v___x_1749_;
goto v___jp_1734_;
}
}
v___jp_1750_:
{
if (v_clsEnabled_1707_ == 0)
{
if (v___y_1751_ == 0)
{
lean_object* v___x_1752_; lean_object* v_traceState_1753_; lean_object* v_env_1754_; lean_object* v_nextMacroScope_1755_; lean_object* v_ngen_1756_; lean_object* v_auxDeclNGen_1757_; lean_object* v_cache_1758_; lean_object* v_recordedDeps_1759_; lean_object* v_messages_1760_; lean_object* v_infoState_1761_; lean_object* v_snapshotTasks_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1781_; 
lean_dec(v_snd_1731_);
lean_dec(v_fst_1730_);
lean_dec_ref(v_msg_1709_);
lean_dec_ref(v_tag_1705_);
lean_dec(v_cls_1703_);
v___x_1752_ = lean_st_ref_take(v___y_1712_);
v_traceState_1753_ = lean_ctor_get(v___x_1752_, 4);
v_env_1754_ = lean_ctor_get(v___x_1752_, 0);
v_nextMacroScope_1755_ = lean_ctor_get(v___x_1752_, 1);
v_ngen_1756_ = lean_ctor_get(v___x_1752_, 2);
v_auxDeclNGen_1757_ = lean_ctor_get(v___x_1752_, 3);
v_cache_1758_ = lean_ctor_get(v___x_1752_, 5);
v_recordedDeps_1759_ = lean_ctor_get(v___x_1752_, 6);
v_messages_1760_ = lean_ctor_get(v___x_1752_, 7);
v_infoState_1761_ = lean_ctor_get(v___x_1752_, 8);
v_snapshotTasks_1762_ = lean_ctor_get(v___x_1752_, 9);
v_isSharedCheck_1781_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1764_ = v___x_1752_;
v_isShared_1765_ = v_isSharedCheck_1781_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_snapshotTasks_1762_);
lean_inc(v_infoState_1761_);
lean_inc(v_messages_1760_);
lean_inc(v_recordedDeps_1759_);
lean_inc(v_cache_1758_);
lean_inc(v_traceState_1753_);
lean_inc(v_auxDeclNGen_1757_);
lean_inc(v_ngen_1756_);
lean_inc(v_nextMacroScope_1755_);
lean_inc(v_env_1754_);
lean_dec(v___x_1752_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1781_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
uint64_t v_tid_1766_; lean_object* v_traces_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1780_; 
v_tid_1766_ = lean_ctor_get_uint64(v_traceState_1753_, sizeof(void*)*1);
v_traces_1767_ = lean_ctor_get(v_traceState_1753_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v_traceState_1753_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1769_ = v_traceState_1753_;
v_isShared_1770_ = v_isSharedCheck_1780_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_traces_1767_);
lean_dec(v_traceState_1753_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1780_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1771_; lean_object* v___x_1773_; 
v___x_1771_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1708_, v_traces_1767_);
lean_dec_ref(v_traces_1767_);
if (v_isShared_1770_ == 0)
{
lean_ctor_set(v___x_1769_, 0, v___x_1771_);
v___x_1773_ = v___x_1769_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v___x_1771_);
lean_ctor_set_uint64(v_reuseFailAlloc_1779_, sizeof(void*)*1, v_tid_1766_);
v___x_1773_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
lean_object* v___x_1775_; 
if (v_isShared_1765_ == 0)
{
lean_ctor_set(v___x_1764_, 4, v___x_1773_);
v___x_1775_ = v___x_1764_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_env_1754_);
lean_ctor_set(v_reuseFailAlloc_1778_, 1, v_nextMacroScope_1755_);
lean_ctor_set(v_reuseFailAlloc_1778_, 2, v_ngen_1756_);
lean_ctor_set(v_reuseFailAlloc_1778_, 3, v_auxDeclNGen_1757_);
lean_ctor_set(v_reuseFailAlloc_1778_, 4, v___x_1773_);
lean_ctor_set(v_reuseFailAlloc_1778_, 5, v_cache_1758_);
lean_ctor_set(v_reuseFailAlloc_1778_, 6, v_recordedDeps_1759_);
lean_ctor_set(v_reuseFailAlloc_1778_, 7, v_messages_1760_);
lean_ctor_set(v_reuseFailAlloc_1778_, 8, v_infoState_1761_);
lean_ctor_set(v_reuseFailAlloc_1778_, 9, v_snapshotTasks_1762_);
v___x_1775_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
lean_object* v___x_1776_; lean_object* v___x_1777_; 
v___x_1776_ = lean_st_ref_put(v___y_1712_, v___x_1775_);
v___x_1777_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5___redArg(v_fst_1714_);
return v___x_1777_;
}
}
}
}
}
else
{
goto v___jp_1745_;
}
}
else
{
goto v___jp_1745_;
}
}
v___jp_1782_:
{
double v___x_1784_; double v___x_1785_; double v___x_1786_; uint8_t v___x_1787_; 
v___x_1784_ = lean_unbox_float(v_snd_1731_);
v___x_1785_ = lean_unbox_float(v_fst_1730_);
v___x_1786_ = lean_float_sub(v___x_1784_, v___x_1785_);
v___x_1787_ = lean_float_decLt(v___y_1783_, v___x_1786_);
v___y_1751_ = v___x_1787_;
goto v___jp_1750_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1___boxed(lean_object* v_cls_1798_, lean_object* v_collapsed_1799_, lean_object* v_tag_1800_, lean_object* v_opts_1801_, lean_object* v_clsEnabled_1802_, lean_object* v_oldTraces_1803_, lean_object* v_msg_1804_, lean_object* v_resStartStop_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_){
_start:
{
uint8_t v_collapsed_boxed_1809_; uint8_t v_clsEnabled_boxed_1810_; lean_object* v_res_1811_; 
v_collapsed_boxed_1809_ = lean_unbox(v_collapsed_1799_);
v_clsEnabled_boxed_1810_ = lean_unbox(v_clsEnabled_1802_);
v_res_1811_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1(v_cls_1798_, v_collapsed_boxed_1809_, v_tag_1800_, v_opts_1801_, v_clsEnabled_boxed_1810_, v_oldTraces_1803_, v_msg_1804_, v_resStartStop_1805_, v___y_1806_, v___y_1807_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
lean_dec_ref(v_opts_1801_);
return v_res_1811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__4(lean_object* v___f_1812_, lean_object* v_lratPath_1813_, uint8_t v_trimProofs_1814_, lean_object* v___f_1815_, lean_object* v_solver_1816_, lean_object* v_timeout_1817_, uint8_t v_binaryProofs_1818_, uint8_t v_solverMode_1819_, lean_object* v___f_1820_, lean_object* v___f_1821_, lean_object* v_cnfHandle_1822_, lean_object* v_cnfPath_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_){
_start:
{
lean_object* v___y_1828_; lean_object* v_toCold_1846_; lean_object* v_options_1847_; lean_object* v_ref_1848_; lean_object* v_inheritedTraceOptions_1849_; uint8_t v_hasTrace_1850_; lean_object* v___x_1851_; uint8_t v___x_1852_; lean_object* v___x_1853_; lean_object* v___y_1855_; lean_object* v___y_1856_; uint8_t v___y_1857_; lean_object* v___y_1858_; lean_object* v_a_1859_; lean_object* v___y_1872_; lean_object* v___y_1873_; lean_object* v___y_1874_; uint8_t v___y_1875_; lean_object* v_a_1876_; lean_object* v___y_1886_; uint8_t v___y_1887_; lean_object* v___y_1929_; lean_object* v___y_1961_; uint8_t v___y_1962_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v_a_1965_; uint8_t v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_1980_; lean_object* v___y_1981_; lean_object* v_a_1982_; uint8_t v___y_1992_; lean_object* v___y_1993_; lean_object* v___y_2042_; 
v_toCold_1846_ = lean_ctor_get(v___y_1824_, 0);
v_options_1847_ = lean_ctor_get(v_toCold_1846_, 2);
v_ref_1848_ = lean_ctor_get(v___y_1824_, 2);
v_inheritedTraceOptions_1849_ = lean_ctor_get(v_toCold_1846_, 11);
v_hasTrace_1850_ = lean_ctor_get_uint8(v_options_1847_, sizeof(void*)*1);
v___x_1851_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__4));
v___x_1852_ = 1;
v___x_1853_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0___closed__0));
if (v_hasTrace_1850_ == 0)
{
lean_object* v___x_2051_; 
lean_dec_ref(v___f_1821_);
v___x_2051_ = l_IO_lazyPure___redArg(v___f_1820_);
if (lean_obj_tag(v___x_2051_) == 0)
{
lean_object* v_a_2052_; lean_object* v___x_2053_; 
v_a_2052_ = lean_ctor_get(v___x_2051_, 0);
lean_inc(v_a_2052_);
lean_dec_ref_known(v___x_2051_, 1);
v___x_2053_ = lean_io_prim_handle_put_str(v_cnfHandle_1822_, v_a_2052_);
lean_dec(v_a_2052_);
if (lean_obj_tag(v___x_2053_) == 0)
{
lean_object* v___x_2054_; 
lean_dec_ref_known(v___x_2053_, 1);
v___x_2054_ = lean_io_prim_handle_flush(v_cnfHandle_1822_);
if (lean_obj_tag(v___x_2054_) == 0)
{
lean_dec_ref_known(v___x_2054_, 1);
goto v___jp_2034_;
}
else
{
lean_object* v_a_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2066_; 
lean_dec_ref(v_cnfPath_1823_);
lean_dec_ref(v_solver_1816_);
lean_dec_ref(v___f_1815_);
lean_dec_ref(v_lratPath_1813_);
lean_dec_ref(v___f_1812_);
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
lean_dec_ref(v_cnfPath_1823_);
lean_dec_ref(v_solver_1816_);
lean_dec_ref(v___f_1815_);
lean_dec_ref(v_lratPath_1813_);
lean_dec_ref(v___f_1812_);
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
lean_dec_ref(v_cnfPath_1823_);
lean_dec_ref(v_solver_1816_);
lean_dec_ref(v___f_1815_);
lean_dec_ref(v_lratPath_1813_);
lean_dec_ref(v___f_1812_);
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
v___x_2091_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__7, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__7);
v___x_2092_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1849_, v_options_1847_, v___x_2091_);
if (v___x_2092_ == 0)
{
lean_object* v___x_2227_; uint8_t v___x_2228_; 
v___x_2227_ = l_Lean_trace_profiler;
v___x_2228_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_options_1847_, v___x_2227_);
if (v___x_2228_ == 0)
{
lean_object* v___x_2229_; 
lean_dec_ref(v___f_1821_);
v___x_2229_ = l_IO_lazyPure___redArg(v___f_1820_);
if (lean_obj_tag(v___x_2229_) == 0)
{
lean_object* v_a_2230_; lean_object* v___x_2231_; 
v_a_2230_ = lean_ctor_get(v___x_2229_, 0);
lean_inc(v_a_2230_);
lean_dec_ref_known(v___x_2229_, 1);
v___x_2231_ = lean_io_prim_handle_put_str(v_cnfHandle_1822_, v_a_2230_);
lean_dec(v_a_2230_);
if (lean_obj_tag(v___x_2231_) == 0)
{
lean_object* v___x_2232_; 
lean_dec_ref_known(v___x_2231_, 1);
v___x_2232_ = lean_io_prim_handle_flush(v_cnfHandle_1822_);
if (lean_obj_tag(v___x_2232_) == 0)
{
lean_dec_ref_known(v___x_2232_, 1);
goto v___jp_2034_;
}
else
{
lean_object* v_a_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2244_; 
lean_dec_ref(v_cnfPath_1823_);
lean_dec_ref(v_solver_1816_);
lean_dec_ref(v___f_1815_);
lean_dec_ref(v_lratPath_1813_);
lean_dec_ref(v___f_1812_);
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
lean_dec_ref(v_cnfPath_1823_);
lean_dec_ref(v_solver_1816_);
lean_dec_ref(v___f_1815_);
lean_dec_ref(v_lratPath_1813_);
lean_dec_ref(v___f_1812_);
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
lean_dec_ref(v_cnfPath_1823_);
lean_dec_ref(v_solver_1816_);
lean_dec_ref(v___f_1815_);
lean_dec_ref(v_lratPath_1813_);
lean_dec_ref(v___f_1812_);
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
v___x_2099_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__10, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__10);
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
v___x_2107_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2(v___x_1851_, v___x_1852_, v___x_1853_, v_options_1847_, v___x_2092_, v___y_2095_, v___f_1821_, v___x_2106_, v___y_1824_, v___y_1825_);
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
v___x_2118_ = lean_float_of_nat(v___y_2114_);
v___x_2119_ = lean_float_of_nat(v___x_2117_);
v___x_2120_ = lean_box_float(v___x_2118_);
v___x_2121_ = lean_box_float(v___x_2119_);
v___x_2122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2120_);
lean_ctor_set(v___x_2122_, 1, v___x_2121_);
v___x_2123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2123_, 0, v_a_2116_);
lean_ctor_set(v___x_2123_, 1, v___x_2122_);
v___x_2124_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2(v___x_1851_, v___x_1852_, v___x_1853_, v_options_1847_, v___x_2092_, v___y_2115_, v___f_1821_, v___x_2123_, v___y_1824_, v___y_1825_);
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
v___x_2131_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg(v___y_1825_);
v_a_2132_ = lean_ctor_get(v___x_2131_, 0);
lean_inc(v_a_2132_);
lean_dec_ref(v___x_2131_);
v___x_2133_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2134_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_options_1847_, v___x_2133_);
if (v___x_2134_ == 0)
{
lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2135_ = lean_io_mono_nanos_now();
v___x_2136_ = l_IO_lazyPure___redArg(v___f_1820_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_object* v_a_2137_; lean_object* v___x_2138_; 
v_a_2137_ = lean_ctor_get(v___x_2136_, 0);
lean_inc(v_a_2137_);
lean_dec_ref_known(v___x_2136_, 1);
v___x_2138_ = lean_io_prim_handle_put_str(v_cnfHandle_1822_, v_a_2137_);
lean_dec(v_a_2137_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v___x_2139_; 
lean_dec_ref_known(v___x_2138_, 1);
v___x_2139_ = lean_io_prim_handle_flush(v_cnfHandle_1822_);
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
v___x_2182_ = l_IO_lazyPure___redArg(v___f_1820_);
if (lean_obj_tag(v___x_2182_) == 0)
{
lean_object* v_a_2183_; lean_object* v___x_2184_; 
v_a_2183_ = lean_ctor_get(v___x_2182_, 0);
lean_inc(v_a_2183_);
lean_dec_ref_known(v___x_2182_, 1);
v___x_2184_ = lean_io_prim_handle_put_str(v_cnfHandle_1822_, v_a_2183_);
lean_dec(v_a_2183_);
if (lean_obj_tag(v___x_2184_) == 0)
{
lean_object* v___x_2185_; 
lean_dec_ref_known(v___x_2184_, 1);
v___x_2185_ = lean_io_prim_handle_flush(v_cnfHandle_1822_);
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
v___y_2114_ = v___x_2181_;
v___y_2115_ = v_a_2132_;
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
v___y_2126_ = v___x_2181_;
v___y_2127_ = v_a_2132_;
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
v___y_2126_ = v___x_2181_;
v___y_2127_ = v_a_2132_;
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
v___y_2126_ = v___x_2181_;
v___y_2127_ = v_a_2132_;
v_a_2128_ = v___x_2224_;
goto v___jp_2125_;
}
}
}
}
}
}
v___jp_1827_:
{
if (lean_obj_tag(v___y_1828_) == 0)
{
lean_object* v_a_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1837_; 
v_a_1829_ = lean_ctor_get(v___y_1828_, 0);
v_isSharedCheck_1837_ = !lean_is_exclusive(v___y_1828_);
if (v_isSharedCheck_1837_ == 0)
{
v___x_1831_ = v___y_1828_;
v_isShared_1832_ = v_isSharedCheck_1837_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_a_1829_);
lean_dec(v___y_1828_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1837_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1833_; lean_object* v___x_1835_; 
v___x_1833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1833_, 0, v_a_1829_);
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 0, v___x_1833_);
v___x_1835_ = v___x_1831_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v___x_1833_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
return v___x_1835_;
}
}
}
else
{
lean_object* v_a_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1845_; 
v_a_1838_ = lean_ctor_get(v___y_1828_, 0);
v_isSharedCheck_1845_ = !lean_is_exclusive(v___y_1828_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1840_ = v___y_1828_;
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_a_1838_);
lean_dec(v___y_1828_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1843_; 
if (v_isShared_1841_ == 0)
{
v___x_1843_ = v___x_1840_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_a_1838_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
}
}
}
}
v___jp_1854_:
{
lean_object* v___x_1860_; double v___x_1861_; double v___x_1862_; double v___x_1863_; double v___x_1864_; double v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; 
v___x_1860_ = lean_io_mono_nanos_now();
v___x_1861_ = lean_float_of_nat(v___y_1858_);
v___x_1862_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__10, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__10);
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
v___x_1870_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0(v___x_1851_, v___x_1852_, v___x_1853_, v___y_1855_, v___y_1857_, v___y_1856_, v___f_1812_, v___x_1869_, v___y_1824_, v___y_1825_);
v___y_1828_ = v___x_1870_;
goto v___jp_1827_;
}
v___jp_1871_:
{
lean_object* v___x_1877_; double v___x_1878_; double v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; 
v___x_1877_ = lean_io_get_num_heartbeats();
v___x_1878_ = lean_float_of_nat(v___y_1874_);
v___x_1879_ = lean_float_of_nat(v___x_1877_);
v___x_1880_ = lean_box_float(v___x_1878_);
v___x_1881_ = lean_box_float(v___x_1879_);
v___x_1882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1880_);
lean_ctor_set(v___x_1882_, 1, v___x_1881_);
v___x_1883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1883_, 0, v_a_1876_);
lean_ctor_set(v___x_1883_, 1, v___x_1882_);
v___x_1884_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0(v___x_1851_, v___x_1852_, v___x_1853_, v___y_1872_, v___y_1875_, v___y_1873_, v___f_1812_, v___x_1883_, v___y_1824_, v___y_1825_);
v___y_1828_ = v___x_1884_;
goto v___jp_1827_;
}
v___jp_1885_:
{
lean_object* v___x_1888_; lean_object* v_a_1889_; lean_object* v___x_1890_; uint8_t v___x_1891_; 
v___x_1888_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg(v___y_1825_);
v_a_1889_ = lean_ctor_get(v___x_1888_, 0);
lean_inc(v_a_1889_);
lean_dec_ref(v___x_1888_);
v___x_1890_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1891_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v___y_1886_, v___x_1890_);
if (v___x_1891_ == 0)
{
lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1892_ = lean_io_mono_nanos_now();
v___x_1893_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_1813_, v_trimProofs_1814_, v___y_1824_, v___y_1825_);
lean_dec_ref(v_lratPath_1813_);
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
v___x_1911_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_1813_, v_trimProofs_1814_, v___y_1824_, v___y_1825_);
lean_dec_ref(v_lratPath_1813_);
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
v___y_1874_ = v___x_1910_;
v___y_1875_ = v___y_1887_;
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
v___y_1874_ = v___x_1910_;
v___y_1875_ = v___y_1887_;
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
lean_dec_ref(v_lratPath_1813_);
lean_dec_ref(v___f_1812_);
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
lean_dec_ref(v___f_1812_);
v___x_1945_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_1813_, v_trimProofs_1814_, v___y_1824_, v___y_1825_);
lean_dec_ref(v_lratPath_1813_);
v___y_1828_ = v___x_1945_;
goto v___jp_1827_;
}
else
{
lean_object* v___x_1946_; uint8_t v___x_1947_; 
v___x_1946_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__7, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__7);
v___x_1947_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1849_, v_options_1847_, v___x_1946_);
if (v___x_1947_ == 0)
{
lean_object* v___x_1948_; uint8_t v___x_1949_; 
v___x_1948_ = l_Lean_trace_profiler;
v___x_1949_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_options_1847_, v___x_1948_);
if (v___x_1949_ == 0)
{
lean_object* v___x_1950_; 
lean_dec_ref(v___f_1812_);
v___x_1950_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_1813_, v_trimProofs_1814_, v___y_1824_, v___y_1825_);
lean_dec_ref(v_lratPath_1813_);
v___y_1828_ = v___x_1950_;
goto v___jp_1827_;
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
lean_dec_ref(v_lratPath_1813_);
lean_dec_ref(v___f_1812_);
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
v___x_1967_ = lean_float_of_nat(v___y_1961_);
v___x_1968_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__10, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__10);
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
v___x_1976_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1(v___x_1851_, v___x_1852_, v___x_1853_, v___y_1964_, v___y_1962_, v___y_1963_, v___f_1815_, v___x_1975_, v___y_1824_, v___y_1825_);
v___y_1929_ = v___x_1976_;
goto v___jp_1928_;
}
v___jp_1977_:
{
lean_object* v___x_1983_; double v___x_1984_; double v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; 
v___x_1983_ = lean_io_get_num_heartbeats();
v___x_1984_ = lean_float_of_nat(v___y_1980_);
v___x_1985_ = lean_float_of_nat(v___x_1983_);
v___x_1986_ = lean_box_float(v___x_1984_);
v___x_1987_ = lean_box_float(v___x_1985_);
v___x_1988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1986_);
lean_ctor_set(v___x_1988_, 1, v___x_1987_);
v___x_1989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1989_, 0, v_a_1982_);
lean_ctor_set(v___x_1989_, 1, v___x_1988_);
v___x_1990_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1(v___x_1851_, v___x_1852_, v___x_1853_, v___y_1981_, v___y_1978_, v___y_1979_, v___f_1815_, v___x_1989_, v___y_1824_, v___y_1825_);
v___y_1929_ = v___x_1990_;
goto v___jp_1928_;
}
v___jp_1991_:
{
lean_object* v___x_1994_; lean_object* v_a_1995_; lean_object* v___x_1996_; uint8_t v___x_1997_; 
v___x_1994_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg(v___y_1825_);
v_a_1995_ = lean_ctor_get(v___x_1994_, 0);
lean_inc(v_a_1995_);
lean_dec_ref(v___x_1994_);
v___x_1996_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1997_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v___y_1993_, v___x_1996_);
if (v___x_1997_ == 0)
{
lean_object* v___x_1998_; lean_object* v___x_1999_; 
v___x_1998_ = lean_io_mono_nanos_now();
lean_inc_ref(v_lratPath_1813_);
v___x_1999_ = l_Lean_Meta_Tactic_BVDecide_External_satQuery(v_solver_1816_, v_cnfPath_1823_, v_lratPath_1813_, v_timeout_1817_, v_binaryProofs_1818_, v_solverMode_1819_, v___y_1824_, v___y_1825_);
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
v___y_1961_ = v___x_1998_;
v___y_1962_ = v___y_1992_;
v___y_1963_ = v_a_1995_;
v___y_1964_ = v___y_1993_;
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
v___y_1961_ = v___x_1998_;
v___y_1962_ = v___y_1992_;
v___y_1963_ = v_a_1995_;
v___y_1964_ = v___y_1993_;
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
lean_inc_ref(v_lratPath_1813_);
v___x_2017_ = l_Lean_Meta_Tactic_BVDecide_External_satQuery(v_solver_1816_, v_cnfPath_1823_, v_lratPath_1813_, v_timeout_1817_, v_binaryProofs_1818_, v_solverMode_1819_, v___y_1824_, v___y_1825_);
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
v___y_1980_ = v___x_2016_;
v___y_1981_ = v___y_1993_;
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
v___y_1980_ = v___x_2016_;
v___y_1981_ = v___y_1993_;
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
lean_dec_ref(v___f_1815_);
lean_inc_ref(v_lratPath_1813_);
v___x_2035_ = l_Lean_Meta_Tactic_BVDecide_External_satQuery(v_solver_1816_, v_cnfPath_1823_, v_lratPath_1813_, v_timeout_1817_, v_binaryProofs_1818_, v_solverMode_1819_, v___y_1824_, v___y_1825_);
v___y_1929_ = v___x_2035_;
goto v___jp_1928_;
}
else
{
lean_object* v___x_2036_; uint8_t v___x_2037_; 
v___x_2036_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__7, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__7);
v___x_2037_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1849_, v_options_1847_, v___x_2036_);
if (v___x_2037_ == 0)
{
lean_object* v___x_2038_; uint8_t v___x_2039_; 
v___x_2038_ = l_Lean_trace_profiler;
v___x_2039_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_options_1847_, v___x_2038_);
if (v___x_2039_ == 0)
{
lean_object* v___x_2040_; 
lean_dec_ref(v___f_1815_);
lean_inc_ref(v_lratPath_1813_);
v___x_2040_ = l_Lean_Meta_Tactic_BVDecide_External_satQuery(v_solver_1816_, v_cnfPath_1823_, v_lratPath_1813_, v_timeout_1817_, v_binaryProofs_1818_, v_solverMode_1819_, v___y_1824_, v___y_1825_);
v___y_1929_ = v___x_2040_;
goto v___jp_1928_;
}
else
{
v___y_1992_ = v___x_2037_;
v___y_1993_ = v_options_1847_;
goto v___jp_1991_;
}
}
else
{
v___y_1992_ = v___x_2037_;
v___y_1993_ = v_options_1847_;
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
lean_dec_ref(v_cnfPath_1823_);
lean_dec_ref(v_solver_1816_);
lean_dec_ref(v___f_1815_);
lean_dec_ref(v_lratPath_1813_);
lean_dec_ref(v___f_1812_);
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
