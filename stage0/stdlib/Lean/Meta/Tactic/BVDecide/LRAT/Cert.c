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
lean_object* l_Lean_stringToMessageData(lean_object*);
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
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
lean_object* l_IO_FS_readBinFile(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
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
uint8_t lean_bool_not(uint8_t);
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
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__3___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
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
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__13(void){
_start:
{
lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_793_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12));
v___x_794_ = l_Lean_stringToMessageData(v___x_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load(lean_object* v_lratPath_795_, uint8_t v_trimProofs_796_, lean_object* v_a_797_, lean_object* v_a_798_){
_start:
{
lean_object* v___x_800_; 
v___x_800_ = l_IO_FS_readBinFile(v_lratPath_795_);
if (lean_obj_tag(v___x_800_) == 0)
{
lean_object* v_options_801_; lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_1249_; 
v_options_801_ = lean_ctor_get(v_a_797_, 2);
v_a_802_ = lean_ctor_get(v___x_800_, 0);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_804_ = v___x_800_;
v_isShared_805_ = v_isSharedCheck_1249_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_dec(v___x_800_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_1249_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v_ref_806_; lean_object* v_inheritedTraceOptions_807_; uint8_t v_hasTrace_808_; lean_object* v___f_809_; lean_object* v___f_810_; lean_object* v___x_811_; lean_object* v_proof_813_; lean_object* v___y_814_; lean_object* v_options_815_; uint8_t v_hasTrace_816_; lean_object* v_inheritedTraceOptions_817_; lean_object* v___y_818_; lean_object* v_proof_853_; lean_object* v___y_854_; lean_object* v___y_855_; lean_object* v___y_860_; lean_object* v___y_861_; lean_object* v___y_862_; uint8_t v___x_864_; lean_object* v___x_865_; lean_object* v___y_867_; lean_object* v___y_868_; lean_object* v___y_869_; lean_object* v___y_870_; uint8_t v___y_871_; lean_object* v___y_872_; lean_object* v_a_873_; lean_object* v___y_883_; lean_object* v___y_884_; lean_object* v___y_885_; lean_object* v___y_886_; uint8_t v___y_887_; lean_object* v___y_888_; lean_object* v_a_889_; lean_object* v___y_892_; lean_object* v___y_893_; lean_object* v___y_894_; lean_object* v___y_895_; uint8_t v___y_896_; lean_object* v___y_897_; lean_object* v_a_898_; lean_object* v___y_911_; lean_object* v___y_912_; lean_object* v___y_913_; lean_object* v___y_914_; uint8_t v___y_915_; lean_object* v___y_916_; lean_object* v_a_917_; lean_object* v___y_920_; lean_object* v___y_921_; lean_object* v___y_922_; uint8_t v___y_923_; lean_object* v___y_924_; lean_object* v___y_925_; lean_object* v___y_999_; lean_object* v___y_1000_; lean_object* v___y_1001_; lean_object* v___y_1002_; lean_object* v___y_1003_; uint8_t v_a_1004_; lean_object* v___y_1036_; lean_object* v___y_1037_; lean_object* v___y_1038_; lean_object* v___y_1039_; lean_object* v_a_1076_; lean_object* v___y_1098_; uint8_t v___x_1100_; 
v_ref_806_ = lean_ctor_get(v_a_797_, 5);
v_inheritedTraceOptions_807_ = lean_ctor_get(v_a_797_, 13);
v_hasTrace_808_ = lean_ctor_get_uint8(v_options_801_, sizeof(void*)*1);
v___f_809_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__0));
v___f_810_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__1), 2, 1);
lean_closure_set(v___f_810_, 0, v_a_802_);
v___x_811_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__3));
v___x_864_ = 1;
v___x_865_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0___closed__0));
v___x_1100_ = lean_bool_not(v_hasTrace_808_);
if (v___x_1100_ == 0)
{
lean_object* v___f_1101_; lean_object* v___y_1103_; uint8_t v___y_1104_; lean_object* v___y_1105_; lean_object* v_a_1106_; lean_object* v___y_1119_; uint8_t v___y_1120_; lean_object* v___y_1121_; lean_object* v_a_1122_; lean_object* v___y_1125_; uint8_t v___y_1126_; lean_object* v___y_1127_; lean_object* v_a_1128_; lean_object* v___y_1131_; uint8_t v___y_1132_; lean_object* v___y_1133_; lean_object* v_a_1134_; lean_object* v___y_1144_; uint8_t v___y_1145_; lean_object* v___y_1146_; lean_object* v_a_1147_; lean_object* v___y_1150_; uint8_t v___y_1151_; lean_object* v___y_1152_; lean_object* v_a_1153_; uint8_t v___y_1156_; uint8_t v_a_1204_; 
v___f_1101_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__11));
if (v_hasTrace_808_ == 0)
{
v_a_1204_ = v_hasTrace_808_;
goto v___jp_1203_;
}
else
{
lean_object* v___x_1227_; uint8_t v___x_1228_; 
v___x_1227_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6);
v___x_1228_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_807_, v_options_801_, v___x_1227_);
if (v___x_1228_ == 0)
{
v_a_1204_ = v___x_1228_;
goto v___jp_1203_;
}
else
{
v___y_1156_ = v___x_1228_;
goto v___jp_1155_;
}
}
v___jp_1102_:
{
lean_object* v___x_1107_; double v___x_1108_; double v___x_1109_; double v___x_1110_; double v___x_1111_; double v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1107_ = lean_io_mono_nanos_now();
v___x_1108_ = lean_float_of_nat(v___y_1105_);
v___x_1109_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9);
v___x_1110_ = lean_float_div(v___x_1108_, v___x_1109_);
v___x_1111_ = lean_float_of_nat(v___x_1107_);
v___x_1112_ = lean_float_div(v___x_1111_, v___x_1109_);
v___x_1113_ = lean_box_float(v___x_1110_);
v___x_1114_ = lean_box_float(v___x_1112_);
v___x_1115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1113_);
lean_ctor_set(v___x_1115_, 1, v___x_1114_);
v___x_1116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1116_, 0, v_a_1106_);
lean_ctor_set(v___x_1116_, 1, v___x_1115_);
v___x_1117_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3(v___x_811_, v___x_864_, v___x_865_, v_options_801_, v___y_1104_, v___y_1103_, v___f_1101_, v___x_1116_, v_a_797_, v_a_798_);
v___y_1098_ = v___x_1117_;
goto v___jp_1097_;
}
v___jp_1118_:
{
lean_object* v___x_1123_; 
v___x_1123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1123_, 0, v_a_1122_);
v___y_1103_ = v___y_1119_;
v___y_1104_ = v___y_1120_;
v___y_1105_ = v___y_1121_;
v_a_1106_ = v___x_1123_;
goto v___jp_1102_;
}
v___jp_1124_:
{
lean_object* v___x_1129_; 
v___x_1129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1129_, 0, v_a_1128_);
v___y_1103_ = v___y_1125_;
v___y_1104_ = v___y_1126_;
v___y_1105_ = v___y_1127_;
v_a_1106_ = v___x_1129_;
goto v___jp_1102_;
}
v___jp_1130_:
{
lean_object* v___x_1135_; double v___x_1136_; double v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1135_ = lean_io_get_num_heartbeats();
v___x_1136_ = lean_float_of_nat(v___y_1133_);
v___x_1137_ = lean_float_of_nat(v___x_1135_);
v___x_1138_ = lean_box_float(v___x_1136_);
v___x_1139_ = lean_box_float(v___x_1137_);
v___x_1140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1138_);
lean_ctor_set(v___x_1140_, 1, v___x_1139_);
v___x_1141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1141_, 0, v_a_1134_);
lean_ctor_set(v___x_1141_, 1, v___x_1140_);
v___x_1142_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3(v___x_811_, v___x_864_, v___x_865_, v_options_801_, v___y_1132_, v___y_1131_, v___f_1101_, v___x_1141_, v_a_797_, v_a_798_);
v___y_1098_ = v___x_1142_;
goto v___jp_1097_;
}
v___jp_1143_:
{
lean_object* v___x_1148_; 
v___x_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1148_, 0, v_a_1147_);
v___y_1131_ = v___y_1144_;
v___y_1132_ = v___y_1145_;
v___y_1133_ = v___y_1146_;
v_a_1134_ = v___x_1148_;
goto v___jp_1130_;
}
v___jp_1149_:
{
lean_object* v___x_1154_; 
v___x_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1154_, 0, v_a_1153_);
v___y_1131_ = v___y_1150_;
v___y_1132_ = v___y_1151_;
v___y_1133_ = v___y_1152_;
v_a_1134_ = v___x_1154_;
goto v___jp_1130_;
}
v___jp_1155_:
{
lean_object* v___x_1157_; lean_object* v_a_1158_; lean_object* v___x_1159_; uint8_t v___x_1160_; 
v___x_1157_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg(v_a_798_);
v_a_1158_ = lean_ctor_get(v___x_1157_, 0);
lean_inc(v_a_1158_);
lean_dec_ref(v___x_1157_);
v___x_1159_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1160_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_options_801_, v___x_1159_);
if (v___x_1160_ == 0)
{
lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1161_ = lean_io_mono_nanos_now();
v___x_1162_ = l_IO_lazyPure___redArg(v___f_810_);
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_object* v_a_1163_; 
v_a_1163_ = lean_ctor_get(v___x_1162_, 0);
lean_inc(v_a_1163_);
lean_dec_ref_known(v___x_1162_, 1);
if (lean_obj_tag(v_a_1163_) == 0)
{
lean_object* v_a_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v_a_1169_; 
v_a_1164_ = lean_ctor_get(v_a_1163_, 0);
lean_inc(v_a_1164_);
lean_dec_ref_known(v_a_1163_, 1);
v___x_1165_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__13, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__13);
v___x_1166_ = l_Lean_stringToMessageData(v_a_1164_);
v___x_1167_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1165_);
lean_ctor_set(v___x_1167_, 1, v___x_1166_);
v___x_1168_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5___redArg(v___x_1167_, v_a_797_, v_a_798_);
v_a_1169_ = lean_ctor_get(v___x_1168_, 0);
lean_inc(v_a_1169_);
lean_dec_ref(v___x_1168_);
v___y_1125_ = v_a_1158_;
v___y_1126_ = v___y_1156_;
v___y_1127_ = v___x_1161_;
v_a_1128_ = v_a_1169_;
goto v___jp_1124_;
}
else
{
lean_object* v_a_1170_; 
v_a_1170_ = lean_ctor_get(v_a_1163_, 0);
lean_inc(v_a_1170_);
lean_dec_ref_known(v_a_1163_, 1);
v___y_1119_ = v_a_1158_;
v___y_1120_ = v___y_1156_;
v___y_1121_ = v___x_1161_;
v_a_1122_ = v_a_1170_;
goto v___jp_1118_;
}
}
else
{
lean_object* v_a_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1181_; 
v_a_1171_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1181_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1173_ = v___x_1162_;
v_isShared_1174_ = v_isSharedCheck_1181_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_a_1171_);
lean_dec(v___x_1162_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1181_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1175_; lean_object* v___x_1177_; 
v___x_1175_ = lean_io_error_to_string(v_a_1171_);
if (v_isShared_1174_ == 0)
{
lean_ctor_set_tag(v___x_1173_, 3);
lean_ctor_set(v___x_1173_, 0, v___x_1175_);
v___x_1177_ = v___x_1173_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v___x_1175_);
v___x_1177_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1178_ = l_Lean_MessageData_ofFormat(v___x_1177_);
lean_inc(v_ref_806_);
v___x_1179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1179_, 0, v_ref_806_);
lean_ctor_set(v___x_1179_, 1, v___x_1178_);
v___y_1125_ = v_a_1158_;
v___y_1126_ = v___y_1156_;
v___y_1127_ = v___x_1161_;
v_a_1128_ = v___x_1179_;
goto v___jp_1124_;
}
}
}
}
else
{
lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1182_ = lean_io_get_num_heartbeats();
v___x_1183_ = l_IO_lazyPure___redArg(v___f_810_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v_a_1184_; 
v_a_1184_ = lean_ctor_get(v___x_1183_, 0);
lean_inc(v_a_1184_);
lean_dec_ref_known(v___x_1183_, 1);
if (lean_obj_tag(v_a_1184_) == 0)
{
lean_object* v_a_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v_a_1190_; 
v_a_1185_ = lean_ctor_get(v_a_1184_, 0);
lean_inc(v_a_1185_);
lean_dec_ref_known(v_a_1184_, 1);
v___x_1186_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__13, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__13);
v___x_1187_ = l_Lean_stringToMessageData(v_a_1185_);
v___x_1188_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1186_);
lean_ctor_set(v___x_1188_, 1, v___x_1187_);
v___x_1189_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5___redArg(v___x_1188_, v_a_797_, v_a_798_);
v_a_1190_ = lean_ctor_get(v___x_1189_, 0);
lean_inc(v_a_1190_);
lean_dec_ref(v___x_1189_);
v___y_1150_ = v_a_1158_;
v___y_1151_ = v___y_1156_;
v___y_1152_ = v___x_1182_;
v_a_1153_ = v_a_1190_;
goto v___jp_1149_;
}
else
{
lean_object* v_a_1191_; 
v_a_1191_ = lean_ctor_get(v_a_1184_, 0);
lean_inc(v_a_1191_);
lean_dec_ref_known(v_a_1184_, 1);
v___y_1144_ = v_a_1158_;
v___y_1145_ = v___y_1156_;
v___y_1146_ = v___x_1182_;
v_a_1147_ = v_a_1191_;
goto v___jp_1143_;
}
}
else
{
lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1202_; 
v_a_1192_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1194_ = v___x_1183_;
v_isShared_1195_ = v_isSharedCheck_1202_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___x_1183_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1202_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1196_; lean_object* v___x_1198_; 
v___x_1196_ = lean_io_error_to_string(v_a_1192_);
if (v_isShared_1195_ == 0)
{
lean_ctor_set_tag(v___x_1194_, 3);
lean_ctor_set(v___x_1194_, 0, v___x_1196_);
v___x_1198_ = v___x_1194_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v___x_1196_);
v___x_1198_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1199_ = l_Lean_MessageData_ofFormat(v___x_1198_);
lean_inc(v_ref_806_);
v___x_1200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1200_, 0, v_ref_806_);
lean_ctor_set(v___x_1200_, 1, v___x_1199_);
v___y_1150_ = v_a_1158_;
v___y_1151_ = v___y_1156_;
v___y_1152_ = v___x_1182_;
v_a_1153_ = v___x_1200_;
goto v___jp_1149_;
}
}
}
}
}
v___jp_1203_:
{
lean_object* v___x_1205_; uint8_t v___x_1206_; 
v___x_1205_ = l_Lean_trace_profiler;
v___x_1206_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_options_801_, v___x_1205_);
if (v___x_1206_ == 0)
{
lean_object* v___x_1207_; 
v___x_1207_ = l_IO_lazyPure___redArg(v___f_810_);
if (lean_obj_tag(v___x_1207_) == 0)
{
lean_object* v_a_1208_; 
v_a_1208_ = lean_ctor_get(v___x_1207_, 0);
lean_inc(v_a_1208_);
lean_dec_ref_known(v___x_1207_, 1);
if (lean_obj_tag(v_a_1208_) == 0)
{
lean_object* v_a_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; 
v_a_1209_ = lean_ctor_get(v_a_1208_, 0);
lean_inc(v_a_1209_);
lean_dec_ref_known(v_a_1208_, 1);
v___x_1210_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__13, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__13);
v___x_1211_ = l_Lean_stringToMessageData(v_a_1209_);
v___x_1212_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1210_);
lean_ctor_set(v___x_1212_, 1, v___x_1211_);
v___x_1213_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5___redArg(v___x_1212_, v_a_797_, v_a_798_);
v___y_1098_ = v___x_1213_;
goto v___jp_1097_;
}
else
{
lean_object* v_a_1214_; 
v_a_1214_ = lean_ctor_get(v_a_1208_, 0);
lean_inc(v_a_1214_);
lean_dec_ref_known(v_a_1208_, 1);
v_a_1076_ = v_a_1214_;
goto v___jp_1075_;
}
}
else
{
lean_object* v_a_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1226_; 
lean_del_object(v___x_804_);
v_a_1215_ = lean_ctor_get(v___x_1207_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1207_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1217_ = v___x_1207_;
v_isShared_1218_ = v_isSharedCheck_1226_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_a_1215_);
lean_dec(v___x_1207_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1226_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1224_; 
v___x_1219_ = lean_io_error_to_string(v_a_1215_);
v___x_1220_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1219_);
v___x_1221_ = l_Lean_MessageData_ofFormat(v___x_1220_);
lean_inc(v_ref_806_);
v___x_1222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1222_, 0, v_ref_806_);
lean_ctor_set(v___x_1222_, 1, v___x_1221_);
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 0, v___x_1222_);
v___x_1224_ = v___x_1217_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___x_1222_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
}
else
{
v___y_1156_ = v_a_1204_;
goto v___jp_1155_;
}
}
}
else
{
lean_object* v___x_1229_; 
v___x_1229_ = l_IO_lazyPure___redArg(v___f_810_);
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_object* v_a_1230_; 
v_a_1230_ = lean_ctor_get(v___x_1229_, 0);
lean_inc(v_a_1230_);
lean_dec_ref_known(v___x_1229_, 1);
if (lean_obj_tag(v_a_1230_) == 0)
{
lean_object* v_a_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
v_a_1231_ = lean_ctor_get(v_a_1230_, 0);
lean_inc(v_a_1231_);
lean_dec_ref_known(v_a_1230_, 1);
v___x_1232_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__13, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__13);
v___x_1233_ = l_Lean_stringToMessageData(v_a_1231_);
v___x_1234_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1232_);
lean_ctor_set(v___x_1234_, 1, v___x_1233_);
v___x_1235_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5___redArg(v___x_1234_, v_a_797_, v_a_798_);
v___y_1098_ = v___x_1235_;
goto v___jp_1097_;
}
else
{
lean_object* v_a_1236_; 
v_a_1236_ = lean_ctor_get(v_a_1230_, 0);
lean_inc(v_a_1236_);
lean_dec_ref_known(v_a_1230_, 1);
v_a_1076_ = v_a_1236_;
goto v___jp_1075_;
}
}
else
{
lean_object* v_a_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1248_; 
lean_del_object(v___x_804_);
v_a_1237_ = lean_ctor_get(v___x_1229_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1229_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1239_ = v___x_1229_;
v_isShared_1240_ = v_isSharedCheck_1248_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_a_1237_);
lean_dec(v___x_1229_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1248_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1246_; 
v___x_1241_ = lean_io_error_to_string(v_a_1237_);
v___x_1242_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1241_);
v___x_1243_ = l_Lean_MessageData_ofFormat(v___x_1242_);
lean_inc(v_ref_806_);
v___x_1244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1244_, 0, v_ref_806_);
lean_ctor_set(v___x_1244_, 1, v___x_1243_);
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 0, v___x_1244_);
v___x_1246_ = v___x_1239_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v___x_1244_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
}
v___jp_812_:
{
if (v_hasTrace_816_ == 0)
{
lean_object* v___x_820_; 
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 0, v_proof_813_);
v___x_820_ = v___x_804_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_proof_813_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
else
{
lean_object* v___x_822_; uint8_t v___x_823_; 
v___x_822_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6);
v___x_823_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_817_, v_options_815_, v___x_822_);
if (v___x_823_ == 0)
{
lean_object* v___x_825_; 
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 0, v_proof_813_);
v___x_825_ = v___x_804_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_proof_813_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
else
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
lean_del_object(v___x_804_);
v___x_827_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__7));
v___x_828_ = lean_array_get_size(v_proof_813_);
v___x_829_ = l_Nat_reprFast(v___x_828_);
v___x_830_ = lean_string_append(v___x_827_, v___x_829_);
lean_dec_ref(v___x_829_);
v___x_831_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__8));
v___x_832_ = lean_string_append(v___x_830_, v___x_831_);
v___x_833_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_833_, 0, v___x_832_);
v___x_834_ = l_Lean_MessageData_ofFormat(v___x_833_);
v___x_835_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0(v___x_811_, v___x_834_, v___y_814_, v___y_818_);
if (lean_obj_tag(v___x_835_) == 0)
{
lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_842_; 
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_842_ == 0)
{
lean_object* v_unused_843_; 
v_unused_843_ = lean_ctor_get(v___x_835_, 0);
lean_dec(v_unused_843_);
v___x_837_ = v___x_835_;
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
else
{
lean_dec(v___x_835_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_840_; 
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 0, v_proof_813_);
v___x_840_ = v___x_837_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_proof_813_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
else
{
lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_851_; 
lean_dec_ref(v_proof_813_);
v_a_844_ = lean_ctor_get(v___x_835_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_851_ == 0)
{
v___x_846_ = v___x_835_;
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_dec(v___x_835_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_849_; 
if (v_isShared_847_ == 0)
{
v___x_849_ = v___x_846_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_a_844_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
}
}
}
v___jp_852_:
{
lean_object* v_options_856_; lean_object* v_inheritedTraceOptions_857_; uint8_t v_hasTrace_858_; 
v_options_856_ = lean_ctor_get(v___y_854_, 2);
v_inheritedTraceOptions_857_ = lean_ctor_get(v___y_854_, 13);
v_hasTrace_858_ = lean_ctor_get_uint8(v_options_856_, sizeof(void*)*1);
v_proof_813_ = v_proof_853_;
v___y_814_ = v___y_854_;
v_options_815_ = v_options_856_;
v_hasTrace_816_ = v_hasTrace_858_;
v_inheritedTraceOptions_817_ = v_inheritedTraceOptions_857_;
v___y_818_ = v___y_855_;
goto v___jp_812_;
}
v___jp_859_:
{
if (lean_obj_tag(v___y_862_) == 0)
{
lean_object* v_a_863_; 
v_a_863_ = lean_ctor_get(v___y_862_, 0);
lean_inc(v_a_863_);
lean_dec_ref_known(v___y_862_, 1);
v_proof_853_ = v_a_863_;
v___y_854_ = v___y_861_;
v___y_855_ = v___y_860_;
goto v___jp_852_;
}
else
{
lean_del_object(v___x_804_);
return v___y_862_;
}
}
v___jp_866_:
{
lean_object* v___x_874_; double v___x_875_; double v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_874_ = lean_io_get_num_heartbeats();
v___x_875_ = lean_float_of_nat(v___y_872_);
v___x_876_ = lean_float_of_nat(v___x_874_);
v___x_877_ = lean_box_float(v___x_875_);
v___x_878_ = lean_box_float(v___x_876_);
v___x_879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_879_, 0, v___x_877_);
lean_ctor_set(v___x_879_, 1, v___x_878_);
v___x_880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_880_, 0, v_a_873_);
lean_ctor_set(v___x_880_, 1, v___x_879_);
v___x_881_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3(v___x_811_, v___x_864_, v___x_865_, v___y_869_, v___y_871_, v___y_867_, v___f_809_, v___x_880_, v___y_870_, v___y_868_);
v___y_860_ = v___y_868_;
v___y_861_ = v___y_870_;
v___y_862_ = v___x_881_;
goto v___jp_859_;
}
v___jp_882_:
{
lean_object* v___x_890_; 
v___x_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_890_, 0, v_a_889_);
v___y_867_ = v___y_883_;
v___y_868_ = v___y_885_;
v___y_869_ = v___y_884_;
v___y_870_ = v___y_886_;
v___y_871_ = v___y_887_;
v___y_872_ = v___y_888_;
v_a_873_ = v___x_890_;
goto v___jp_866_;
}
v___jp_891_:
{
lean_object* v___x_899_; double v___x_900_; double v___x_901_; double v___x_902_; double v___x_903_; double v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_899_ = lean_io_mono_nanos_now();
v___x_900_ = lean_float_of_nat(v___y_897_);
v___x_901_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9);
v___x_902_ = lean_float_div(v___x_900_, v___x_901_);
v___x_903_ = lean_float_of_nat(v___x_899_);
v___x_904_ = lean_float_div(v___x_903_, v___x_901_);
v___x_905_ = lean_box_float(v___x_902_);
v___x_906_ = lean_box_float(v___x_904_);
v___x_907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_907_, 0, v___x_905_);
lean_ctor_set(v___x_907_, 1, v___x_906_);
v___x_908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_908_, 0, v_a_898_);
lean_ctor_set(v___x_908_, 1, v___x_907_);
v___x_909_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3(v___x_811_, v___x_864_, v___x_865_, v___y_894_, v___y_896_, v___y_892_, v___f_809_, v___x_908_, v___y_895_, v___y_893_);
v___y_860_ = v___y_893_;
v___y_861_ = v___y_895_;
v___y_862_ = v___x_909_;
goto v___jp_859_;
}
v___jp_910_:
{
lean_object* v___x_918_; 
v___x_918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_918_, 0, v_a_917_);
v___y_892_ = v___y_911_;
v___y_893_ = v___y_913_;
v___y_894_ = v___y_912_;
v___y_895_ = v___y_914_;
v___y_896_ = v___y_915_;
v___y_897_ = v___y_916_;
v_a_898_ = v___x_918_;
goto v___jp_891_;
}
v___jp_919_:
{
lean_object* v___x_926_; lean_object* v_a_927_; lean_object* v___x_928_; uint8_t v___x_929_; 
v___x_926_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg(v___y_921_);
v_a_927_ = lean_ctor_get(v___x_926_, 0);
lean_inc(v_a_927_);
lean_dec_ref(v___x_926_);
v___x_928_ = l_Lean_trace_profiler_useHeartbeats;
v___x_929_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v___y_920_, v___x_928_);
if (v___x_929_ == 0)
{
lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_930_ = lean_io_mono_nanos_now();
v___x_931_ = l_IO_lazyPure___redArg(v___y_925_);
if (lean_obj_tag(v___x_931_) == 0)
{
lean_object* v_a_932_; lean_object* v___x_933_; 
v_a_932_ = lean_ctor_get(v___x_931_, 0);
lean_inc(v_a_932_);
lean_dec_ref_known(v___x_931_, 1);
v___x_933_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__4___redArg(v_a_932_);
if (lean_obj_tag(v___x_933_) == 0)
{
lean_object* v_a_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_941_; 
v_a_934_ = lean_ctor_get(v___x_933_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_941_ == 0)
{
v___x_936_ = v___x_933_;
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_a_934_);
lean_dec(v___x_933_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_939_; 
if (v_isShared_937_ == 0)
{
lean_ctor_set_tag(v___x_936_, 1);
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
v___y_892_ = v_a_927_;
v___y_893_ = v___y_921_;
v___y_894_ = v___y_920_;
v___y_895_ = v___y_922_;
v___y_896_ = v___y_923_;
v___y_897_ = v___x_930_;
v_a_898_ = v___x_939_;
goto v___jp_891_;
}
}
}
else
{
lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_952_; 
v_a_942_ = lean_ctor_get(v___x_933_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_952_ == 0)
{
v___x_944_ = v___x_933_;
v_isShared_945_ = v_isSharedCheck_952_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_933_);
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
lean_inc(v___y_924_);
v___x_950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_950_, 0, v___y_924_);
lean_ctor_set(v___x_950_, 1, v___x_949_);
v___y_911_ = v_a_927_;
v___y_912_ = v___y_920_;
v___y_913_ = v___y_921_;
v___y_914_ = v___y_922_;
v___y_915_ = v___y_923_;
v___y_916_ = v___x_930_;
v_a_917_ = v___x_950_;
goto v___jp_910_;
}
}
}
}
else
{
lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_963_; 
v_a_953_ = lean_ctor_get(v___x_931_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_931_);
if (v_isSharedCheck_963_ == 0)
{
v___x_955_ = v___x_931_;
v_isShared_956_ = v_isSharedCheck_963_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_dec(v___x_931_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_963_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_957_; lean_object* v___x_959_; 
v___x_957_ = lean_io_error_to_string(v_a_953_);
if (v_isShared_956_ == 0)
{
lean_ctor_set_tag(v___x_955_, 3);
lean_ctor_set(v___x_955_, 0, v___x_957_);
v___x_959_ = v___x_955_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v___x_957_);
v___x_959_ = v_reuseFailAlloc_962_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = l_Lean_MessageData_ofFormat(v___x_959_);
lean_inc(v___y_924_);
v___x_961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_961_, 0, v___y_924_);
lean_ctor_set(v___x_961_, 1, v___x_960_);
v___y_911_ = v_a_927_;
v___y_912_ = v___y_920_;
v___y_913_ = v___y_921_;
v___y_914_ = v___y_922_;
v___y_915_ = v___y_923_;
v___y_916_ = v___x_930_;
v_a_917_ = v___x_961_;
goto v___jp_910_;
}
}
}
}
else
{
lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_964_ = lean_io_get_num_heartbeats();
v___x_965_ = l_IO_lazyPure___redArg(v___y_925_);
if (lean_obj_tag(v___x_965_) == 0)
{
lean_object* v_a_966_; lean_object* v___x_967_; 
v_a_966_ = lean_ctor_get(v___x_965_, 0);
lean_inc(v_a_966_);
lean_dec_ref_known(v___x_965_, 1);
v___x_967_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__4___redArg(v_a_966_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_object* v_a_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_975_; 
v_a_968_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_975_ == 0)
{
v___x_970_ = v___x_967_;
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_a_968_);
lean_dec(v___x_967_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_973_; 
if (v_isShared_971_ == 0)
{
lean_ctor_set_tag(v___x_970_, 1);
v___x_973_ = v___x_970_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_a_968_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
v___y_867_ = v_a_927_;
v___y_868_ = v___y_921_;
v___y_869_ = v___y_920_;
v___y_870_ = v___y_922_;
v___y_871_ = v___y_923_;
v___y_872_ = v___x_964_;
v_a_873_ = v___x_973_;
goto v___jp_866_;
}
}
}
else
{
lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_986_; 
v_a_976_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_986_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_986_ == 0)
{
v___x_978_ = v___x_967_;
v_isShared_979_ = v_isSharedCheck_986_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_dec(v___x_967_);
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
lean_inc(v___y_924_);
v___x_984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_984_, 0, v___y_924_);
lean_ctor_set(v___x_984_, 1, v___x_983_);
v___y_883_ = v_a_927_;
v___y_884_ = v___y_920_;
v___y_885_ = v___y_921_;
v___y_886_ = v___y_922_;
v___y_887_ = v___y_923_;
v___y_888_ = v___x_964_;
v_a_889_ = v___x_984_;
goto v___jp_882_;
}
}
}
}
else
{
lean_object* v_a_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_997_; 
v_a_987_ = lean_ctor_get(v___x_965_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_965_);
if (v_isSharedCheck_997_ == 0)
{
v___x_989_ = v___x_965_;
v_isShared_990_ = v_isSharedCheck_997_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_a_987_);
lean_dec(v___x_965_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_997_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_991_; lean_object* v___x_993_; 
v___x_991_ = lean_io_error_to_string(v_a_987_);
if (v_isShared_990_ == 0)
{
lean_ctor_set_tag(v___x_989_, 3);
lean_ctor_set(v___x_989_, 0, v___x_991_);
v___x_993_ = v___x_989_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v___x_991_);
v___x_993_ = v_reuseFailAlloc_996_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_994_ = l_Lean_MessageData_ofFormat(v___x_993_);
lean_inc(v___y_924_);
v___x_995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_995_, 0, v___y_924_);
lean_ctor_set(v___x_995_, 1, v___x_994_);
v___y_883_ = v_a_927_;
v___y_884_ = v___y_920_;
v___y_885_ = v___y_921_;
v___y_886_ = v___y_922_;
v___y_887_ = v___y_923_;
v___y_888_ = v___x_964_;
v_a_889_ = v___x_995_;
goto v___jp_882_;
}
}
}
}
}
v___jp_998_:
{
lean_object* v___x_1005_; uint8_t v___x_1006_; 
v___x_1005_ = l_Lean_trace_profiler;
v___x_1006_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v___y_1000_, v___x_1005_);
if (v___x_1006_ == 0)
{
lean_object* v___x_1007_; 
v___x_1007_ = l_IO_lazyPure___redArg(v___y_1003_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v_a_1008_; lean_object* v___x_1009_; 
v_a_1008_ = lean_ctor_get(v___x_1007_, 0);
lean_inc(v_a_1008_);
lean_dec_ref_known(v___x_1007_, 1);
v___x_1009_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__4___redArg(v_a_1008_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_object* v_a_1010_; 
v_a_1010_ = lean_ctor_get(v___x_1009_, 0);
lean_inc(v_a_1010_);
lean_dec_ref_known(v___x_1009_, 1);
v_proof_853_ = v_a_1010_;
v___y_854_ = v___y_1001_;
v___y_855_ = v___y_999_;
goto v___jp_852_;
}
else
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1022_; 
lean_del_object(v___x_804_);
v_a_1011_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1013_ = v___x_1009_;
v_isShared_1014_ = v_isSharedCheck_1022_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_1009_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1022_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1020_; 
v___x_1015_ = lean_io_error_to_string(v_a_1011_);
v___x_1016_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1015_);
v___x_1017_ = l_Lean_MessageData_ofFormat(v___x_1016_);
lean_inc(v___y_1002_);
v___x_1018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___y_1002_);
lean_ctor_set(v___x_1018_, 1, v___x_1017_);
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 0, v___x_1018_);
v___x_1020_ = v___x_1013_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v___x_1018_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
}
else
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1034_; 
lean_del_object(v___x_804_);
v_a_1023_ = lean_ctor_get(v___x_1007_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1025_ = v___x_1007_;
v_isShared_1026_ = v_isSharedCheck_1034_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_1007_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1034_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1032_; 
v___x_1027_ = lean_io_error_to_string(v_a_1023_);
v___x_1028_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1027_);
v___x_1029_ = l_Lean_MessageData_ofFormat(v___x_1028_);
lean_inc(v___y_1002_);
v___x_1030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___y_1002_);
lean_ctor_set(v___x_1030_, 1, v___x_1029_);
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 0, v___x_1030_);
v___x_1032_ = v___x_1025_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___x_1030_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
}
else
{
v___y_920_ = v___y_1000_;
v___y_921_ = v___y_999_;
v___y_922_ = v___y_1001_;
v___y_923_ = v_a_1004_;
v___y_924_ = v___y_1002_;
v___y_925_ = v___y_1003_;
goto v___jp_919_;
}
}
v___jp_1035_:
{
if (v_trimProofs_796_ == 0)
{
lean_dec_ref(v___y_1037_);
v_proof_853_ = v___y_1036_;
v___y_854_ = v___y_1038_;
v___y_855_ = v___y_1039_;
goto v___jp_852_;
}
else
{
lean_object* v_options_1040_; lean_object* v_ref_1041_; lean_object* v_inheritedTraceOptions_1042_; uint8_t v_hasTrace_1043_; uint8_t v___x_1044_; 
lean_dec_ref(v___y_1036_);
v_options_1040_ = lean_ctor_get(v___y_1038_, 2);
v_ref_1041_ = lean_ctor_get(v___y_1038_, 5);
v_inheritedTraceOptions_1042_ = lean_ctor_get(v___y_1038_, 13);
v_hasTrace_1043_ = lean_ctor_get_uint8(v_options_1040_, sizeof(void*)*1);
v___x_1044_ = lean_bool_not(v_hasTrace_1043_);
if (v___x_1044_ == 0)
{
if (v_hasTrace_1043_ == 0)
{
v___y_999_ = v___y_1039_;
v___y_1000_ = v_options_1040_;
v___y_1001_ = v___y_1038_;
v___y_1002_ = v_ref_1041_;
v___y_1003_ = v___y_1037_;
v_a_1004_ = v_hasTrace_1043_;
goto v___jp_998_;
}
else
{
lean_object* v___x_1045_; uint8_t v___x_1046_; 
v___x_1045_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6);
v___x_1046_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1042_, v_options_1040_, v___x_1045_);
if (v___x_1046_ == 0)
{
v___y_999_ = v___y_1039_;
v___y_1000_ = v_options_1040_;
v___y_1001_ = v___y_1038_;
v___y_1002_ = v_ref_1041_;
v___y_1003_ = v___y_1037_;
v_a_1004_ = v___x_1046_;
goto v___jp_998_;
}
else
{
v___y_920_ = v_options_1040_;
v___y_921_ = v___y_1039_;
v___y_922_ = v___y_1038_;
v___y_923_ = v___x_1046_;
v___y_924_ = v_ref_1041_;
v___y_925_ = v___y_1037_;
goto v___jp_919_;
}
}
}
else
{
lean_object* v___x_1047_; 
v___x_1047_ = l_IO_lazyPure___redArg(v___y_1037_);
if (lean_obj_tag(v___x_1047_) == 0)
{
lean_object* v_a_1048_; lean_object* v___x_1049_; 
v_a_1048_ = lean_ctor_get(v___x_1047_, 0);
lean_inc(v_a_1048_);
lean_dec_ref_known(v___x_1047_, 1);
v___x_1049_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__4___redArg(v_a_1048_);
if (lean_obj_tag(v___x_1049_) == 0)
{
lean_object* v_a_1050_; 
v_a_1050_ = lean_ctor_get(v___x_1049_, 0);
lean_inc(v_a_1050_);
lean_dec_ref_known(v___x_1049_, 1);
v_proof_813_ = v_a_1050_;
v___y_814_ = v___y_1038_;
v_options_815_ = v_options_1040_;
v_hasTrace_816_ = v_hasTrace_1043_;
v_inheritedTraceOptions_817_ = v_inheritedTraceOptions_1042_;
v___y_818_ = v___y_1039_;
goto v___jp_812_;
}
else
{
lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1062_; 
lean_del_object(v___x_804_);
v_a_1051_ = lean_ctor_get(v___x_1049_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1053_ = v___x_1049_;
v_isShared_1054_ = v_isSharedCheck_1062_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_a_1051_);
lean_dec(v___x_1049_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1062_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1060_; 
v___x_1055_ = lean_io_error_to_string(v_a_1051_);
v___x_1056_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1055_);
v___x_1057_ = l_Lean_MessageData_ofFormat(v___x_1056_);
lean_inc(v_ref_1041_);
v___x_1058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1058_, 0, v_ref_1041_);
lean_ctor_set(v___x_1058_, 1, v___x_1057_);
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 0, v___x_1058_);
v___x_1060_ = v___x_1053_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v___x_1058_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
}
else
{
lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1074_; 
lean_del_object(v___x_804_);
v_a_1063_ = lean_ctor_get(v___x_1047_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1065_ = v___x_1047_;
v_isShared_1066_ = v_isSharedCheck_1074_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v___x_1047_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1074_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1072_; 
v___x_1067_ = lean_io_error_to_string(v_a_1063_);
v___x_1068_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1067_);
v___x_1069_ = l_Lean_MessageData_ofFormat(v___x_1068_);
lean_inc(v_ref_1041_);
v___x_1070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1070_, 0, v_ref_1041_);
lean_ctor_set(v___x_1070_, 1, v___x_1069_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 0, v___x_1070_);
v___x_1072_ = v___x_1065_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1070_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
}
}
}
v___jp_1075_:
{
lean_object* v___f_1077_; 
lean_inc_ref(v_a_1076_);
v___f_1077_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__2___boxed), 2, 1);
lean_closure_set(v___f_1077_, 0, v_a_1076_);
if (v_hasTrace_808_ == 0)
{
v___y_1036_ = v_a_1076_;
v___y_1037_ = v___f_1077_;
v___y_1038_ = v_a_797_;
v___y_1039_ = v_a_798_;
goto v___jp_1035_;
}
else
{
lean_object* v___x_1078_; uint8_t v___x_1079_; 
v___x_1078_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6);
v___x_1079_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_807_, v_options_801_, v___x_1078_);
if (v___x_1079_ == 0)
{
v___y_1036_ = v_a_1076_;
v___y_1037_ = v___f_1077_;
v___y_1038_ = v_a_797_;
v___y_1039_ = v_a_798_;
goto v___jp_1035_;
}
else
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1080_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__7));
v___x_1081_ = lean_array_get_size(v_a_1076_);
v___x_1082_ = l_Nat_reprFast(v___x_1081_);
v___x_1083_ = lean_string_append(v___x_1080_, v___x_1082_);
lean_dec_ref(v___x_1082_);
v___x_1084_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__10));
v___x_1085_ = lean_string_append(v___x_1083_, v___x_1084_);
v___x_1086_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1085_);
v___x_1087_ = l_Lean_MessageData_ofFormat(v___x_1086_);
v___x_1088_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0(v___x_811_, v___x_1087_, v_a_797_, v_a_798_);
if (lean_obj_tag(v___x_1088_) == 0)
{
lean_dec_ref_known(v___x_1088_, 1);
v___y_1036_ = v_a_1076_;
v___y_1037_ = v___f_1077_;
v___y_1038_ = v_a_797_;
v___y_1039_ = v_a_798_;
goto v___jp_1035_;
}
else
{
lean_object* v_a_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1096_; 
lean_dec_ref(v___f_1077_);
lean_dec_ref(v_a_1076_);
lean_del_object(v___x_804_);
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
return v___x_1094_;
}
}
}
}
}
}
v___jp_1097_:
{
if (lean_obj_tag(v___y_1098_) == 0)
{
lean_object* v_a_1099_; 
v_a_1099_ = lean_ctor_get(v___y_1098_, 0);
lean_inc(v_a_1099_);
lean_dec_ref_known(v___y_1098_, 1);
v_a_1076_ = v_a_1099_;
goto v___jp_1075_;
}
else
{
lean_del_object(v___x_804_);
return v___y_1098_;
}
}
}
}
else
{
lean_object* v_a_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1262_; 
v_a_1250_ = lean_ctor_get(v___x_800_, 0);
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1252_ = v___x_800_;
v_isShared_1253_ = v_isSharedCheck_1262_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_a_1250_);
lean_dec(v___x_800_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1262_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v_ref_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1260_; 
v_ref_1254_ = lean_ctor_get(v_a_797_, 5);
v___x_1255_ = lean_io_error_to_string(v_a_1250_);
v___x_1256_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1255_);
v___x_1257_ = l_Lean_MessageData_ofFormat(v___x_1256_);
lean_inc(v_ref_1254_);
v___x_1258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1258_, 0, v_ref_1254_);
lean_ctor_set(v___x_1258_, 1, v___x_1257_);
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 0, v___x_1258_);
v___x_1260_ = v___x_1252_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1258_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_load___boxed(lean_object* v_lratPath_1263_, lean_object* v_trimProofs_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_){
_start:
{
uint8_t v_trimProofs_boxed_1268_; lean_object* v_res_1269_; 
v_trimProofs_boxed_1268_ = lean_unbox(v_trimProofs_1264_);
v_res_1269_ = l_Lean_Meta_Tactic_BVDecide_LratCert_load(v_lratPath_1263_, v_trimProofs_boxed_1268_, v_a_1265_, v_a_1266_);
lean_dec(v_a_1266_);
lean_dec_ref(v_a_1265_);
lean_dec_ref(v_lratPath_1263_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5(lean_object* v_00_u03b1_1270_, lean_object* v_x_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v___x_1275_; 
v___x_1275_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5___redArg(v_x_1271_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1276_, lean_object* v_x_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5(v_00_u03b1_1276_, v_x_1277_, v___y_1278_, v___y_1279_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5(lean_object* v_00_u03b1_1282_, lean_object* v_msg_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_){
_start:
{
lean_object* v___x_1287_; 
v___x_1287_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5___redArg(v_msg_1283_, v___y_1284_, v___y_1285_);
return v___x_1287_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5___boxed(lean_object* v_00_u03b1_1288_, lean_object* v_msg_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_){
_start:
{
lean_object* v_res_1293_; 
v_res_1293_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5(v_00_u03b1_1288_, v_msg_1289_, v___y_1290_, v___y_1291_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
return v_res_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(lean_object* v_lratPath_1294_, uint8_t v_trimProofs_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_){
_start:
{
lean_object* v___x_1299_; 
v___x_1299_ = l_Lean_Meta_Tactic_BVDecide_LratCert_load(v_lratPath_1294_, v_trimProofs_1295_, v_a_1296_, v_a_1297_);
if (lean_obj_tag(v___x_1299_) == 0)
{
lean_object* v_a_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1308_; 
v_a_1300_ = lean_ctor_get(v___x_1299_, 0);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___x_1299_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1302_ = v___x_1299_;
v_isShared_1303_ = v_isSharedCheck_1308_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_a_1300_);
lean_dec(v___x_1299_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1308_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1304_; lean_object* v___x_1306_; 
v___x_1304_ = l_Std_Tactic_BVDecide_LRAT_lratProofToString(v_a_1300_);
lean_dec(v_a_1300_);
if (v_isShared_1303_ == 0)
{
lean_ctor_set(v___x_1302_, 0, v___x_1304_);
v___x_1306_ = v___x_1302_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v___x_1304_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
}
}
}
else
{
lean_object* v_a_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1316_; 
v_a_1309_ = lean_ctor_get(v___x_1299_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1299_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1311_ = v___x_1299_;
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_a_1309_);
lean_dec(v___x_1299_);
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
v_reuseFailAlloc_1315_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile___boxed(lean_object* v_lratPath_1317_, lean_object* v_trimProofs_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_){
_start:
{
uint8_t v_trimProofs_boxed_1322_; lean_object* v_res_1323_; 
v_trimProofs_boxed_1322_ = lean_unbox(v_trimProofs_1318_);
v_res_1323_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_1317_, v_trimProofs_boxed_1322_, v_a_1319_, v_a_1320_);
lean_dec(v_a_1320_);
lean_dec_ref(v_a_1319_);
lean_dec_ref(v_lratPath_1317_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg___lam__0(lean_object* v_snd_1324_, lean_object* v___y_1325_, lean_object* v_a_x3f_1326_){
_start:
{
lean_object* v___x_1328_; 
v___x_1328_ = lean_io_remove_file(v_snd_1324_);
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1336_; 
v_a_1329_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1331_ = v___x_1328_;
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v___x_1328_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1334_; 
if (v_isShared_1332_ == 0)
{
v___x_1334_ = v___x_1331_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_a_1329_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
}
else
{
lean_object* v_a_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1349_; 
v_a_1337_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1339_ = v___x_1328_;
v_isShared_1340_ = v_isSharedCheck_1349_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_a_1337_);
lean_dec(v___x_1328_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1349_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v_ref_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1347_; 
v_ref_1341_ = lean_ctor_get(v___y_1325_, 5);
v___x_1342_ = lean_io_error_to_string(v_a_1337_);
v___x_1343_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1343_, 0, v___x_1342_);
v___x_1344_ = l_Lean_MessageData_ofFormat(v___x_1343_);
lean_inc(v_ref_1341_);
v___x_1345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1345_, 0, v_ref_1341_);
lean_ctor_set(v___x_1345_, 1, v___x_1344_);
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 0, v___x_1345_);
v___x_1347_ = v___x_1339_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v___x_1345_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg___lam__0___boxed(lean_object* v_snd_1350_, lean_object* v___y_1351_, lean_object* v_a_x3f_1352_, lean_object* v___y_1353_){
_start:
{
lean_object* v_res_1354_; 
v_res_1354_ = l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg___lam__0(v_snd_1350_, v___y_1351_, v_a_x3f_1352_);
lean_dec(v_a_x3f_1352_);
lean_dec_ref(v___y_1351_);
lean_dec_ref(v_snd_1350_);
return v_res_1354_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg(lean_object* v_f_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_){
_start:
{
lean_object* v___x_1359_; 
v___x_1359_ = lean_io_create_tempfile();
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_object* v_a_1360_; lean_object* v_fst_1361_; lean_object* v_snd_1362_; lean_object* v_r_1363_; 
v_a_1360_ = lean_ctor_get(v___x_1359_, 0);
lean_inc(v_a_1360_);
lean_dec_ref_known(v___x_1359_, 1);
v_fst_1361_ = lean_ctor_get(v_a_1360_, 0);
lean_inc(v_fst_1361_);
v_snd_1362_ = lean_ctor_get(v_a_1360_, 1);
lean_inc_n(v_snd_1362_, 2);
lean_dec(v_a_1360_);
lean_inc(v___y_1357_);
lean_inc_ref(v___y_1356_);
v_r_1363_ = lean_apply_5(v_f_1355_, v_fst_1361_, v_snd_1362_, v___y_1356_, v___y_1357_, lean_box(0));
if (lean_obj_tag(v_r_1363_) == 0)
{
lean_object* v_a_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1388_; 
v_a_1364_ = lean_ctor_get(v_r_1363_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v_r_1363_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1366_ = v_r_1363_;
v_isShared_1367_ = v_isSharedCheck_1388_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_a_1364_);
lean_dec(v_r_1363_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1388_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1369_; 
lean_inc(v_a_1364_);
if (v_isShared_1367_ == 0)
{
lean_ctor_set_tag(v___x_1366_, 1);
v___x_1369_ = v___x_1366_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_a_1364_);
v___x_1369_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
lean_object* v___x_1370_; 
v___x_1370_ = l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg___lam__0(v_snd_1362_, v___y_1356_, v___x_1369_);
lean_dec_ref(v___x_1369_);
lean_dec(v_snd_1362_);
if (lean_obj_tag(v___x_1370_) == 0)
{
lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1370_);
if (v_isSharedCheck_1377_ == 0)
{
lean_object* v_unused_1378_; 
v_unused_1378_ = lean_ctor_get(v___x_1370_, 0);
lean_dec(v_unused_1378_);
v___x_1372_ = v___x_1370_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_dec(v___x_1370_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1375_; 
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 0, v_a_1364_);
v___x_1375_ = v___x_1372_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_a_1364_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
else
{
lean_object* v_a_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1386_; 
lean_dec(v_a_1364_);
v_a_1379_ = lean_ctor_get(v___x_1370_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1370_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1381_ = v___x_1370_;
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_a_1379_);
lean_dec(v___x_1370_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1384_; 
if (v_isShared_1382_ == 0)
{
v___x_1384_ = v___x_1381_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_a_1379_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
}
}
}
}
else
{
lean_object* v_a_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; 
v_a_1389_ = lean_ctor_get(v_r_1363_, 0);
lean_inc(v_a_1389_);
lean_dec_ref_known(v_r_1363_, 1);
v___x_1390_ = lean_box(0);
v___x_1391_ = l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg___lam__0(v_snd_1362_, v___y_1356_, v___x_1390_);
lean_dec(v_snd_1362_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1398_; 
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1398_ == 0)
{
lean_object* v_unused_1399_; 
v_unused_1399_ = lean_ctor_get(v___x_1391_, 0);
lean_dec(v_unused_1399_);
v___x_1393_ = v___x_1391_;
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
else
{
lean_dec(v___x_1391_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1396_; 
if (v_isShared_1394_ == 0)
{
lean_ctor_set_tag(v___x_1393_, 1);
lean_ctor_set(v___x_1393_, 0, v_a_1389_);
v___x_1396_ = v___x_1393_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_a_1389_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
return v___x_1396_;
}
}
}
else
{
lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1407_; 
lean_dec(v_a_1389_);
v_a_1400_ = lean_ctor_get(v___x_1391_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1402_ = v___x_1391_;
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_dec(v___x_1391_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1405_; 
if (v_isShared_1403_ == 0)
{
v___x_1405_ = v___x_1402_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_a_1400_);
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
else
{
lean_object* v_a_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1420_; 
lean_dec_ref(v_f_1355_);
v_a_1408_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1410_ = v___x_1359_;
v_isShared_1411_ = v_isSharedCheck_1420_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_a_1408_);
lean_dec(v___x_1359_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1420_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v_ref_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1418_; 
v_ref_1412_ = lean_ctor_get(v___y_1356_, 5);
v___x_1413_ = lean_io_error_to_string(v_a_1408_);
v___x_1414_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1413_);
v___x_1415_ = l_Lean_MessageData_ofFormat(v___x_1414_);
lean_inc(v_ref_1412_);
v___x_1416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1416_, 0, v_ref_1412_);
lean_ctor_set(v___x_1416_, 1, v___x_1415_);
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 0, v___x_1416_);
v___x_1418_ = v___x_1410_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v___x_1416_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg___boxed(lean_object* v_f_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg(v_f_1421_, v___y_1422_, v___y_1423_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3(lean_object* v_00_u03b1_1426_, lean_object* v_f_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
lean_object* v___x_1431_; 
v___x_1431_ = l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg(v_f_1427_, v___y_1428_, v___y_1429_);
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___boxed(lean_object* v_00_u03b1_1432_, lean_object* v_f_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_){
_start:
{
lean_object* v_res_1437_; 
v_res_1437_ = l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3(v_00_u03b1_1432_, v_f_1433_, v___y_1434_, v___y_1435_);
lean_dec(v___y_1435_);
lean_dec_ref(v___y_1434_);
return v_res_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__0(lean_object* v_cnf_1438_, lean_object* v_x_1439_){
_start:
{
lean_object* v___x_1440_; 
v___x_1440_ = l_Std_Sat_CNF_dimacs(v_cnf_1438_);
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__0___boxed(lean_object* v_cnf_1441_, lean_object* v_x_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l_Lean_Meta_Tactic_BVDecide_runExternal___lam__0(v_cnf_1441_, v_x_1442_);
lean_dec_ref(v_cnf_1441_);
return v_res_1443_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1447_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1___closed__1));
v___x_1448_ = l_Lean_MessageData_ofFormat(v___x_1447_);
return v___x_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1(lean_object* v_x_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_){
_start:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1453_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1___closed__2, &l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1___closed__2);
v___x_1454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1454_, 0, v___x_1453_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1___boxed(lean_object* v_x_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1(v_x_1455_, v___y_1456_, v___y_1457_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
lean_dec_ref(v_x_1455_);
return v_res_1459_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2___closed__2(void){
_start:
{
lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___x_1463_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2___closed__1));
v___x_1464_ = l_Lean_MessageData_ofFormat(v___x_1463_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2(lean_object* v_x_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1469_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2___closed__2, &l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2___closed__2);
v___x_1470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1470_, 0, v___x_1469_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2___boxed(lean_object* v_x_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
lean_object* v_res_1475_; 
v_res_1475_ = l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2(v_x_1471_, v___y_1472_, v___y_1473_);
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1472_);
lean_dec_ref(v_x_1471_);
return v_res_1475_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3___closed__2(void){
_start:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1479_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3___closed__1));
v___x_1480_ = l_Lean_MessageData_ofFormat(v___x_1479_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3(lean_object* v_x_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1485_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3___closed__2, &l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3___closed__2);
v___x_1486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1485_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3___boxed(lean_object* v_x_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
lean_object* v_res_1491_; 
v_res_1491_ = l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3(v_x_1487_, v___y_1488_, v___y_1489_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
lean_dec_ref(v_x_1487_);
return v_res_1491_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2_spec__4(lean_object* v_e_1492_){
_start:
{
if (lean_obj_tag(v_e_1492_) == 0)
{
uint8_t v___x_1493_; 
v___x_1493_ = 2;
return v___x_1493_;
}
else
{
uint8_t v___x_1494_; 
v___x_1494_ = 0;
return v___x_1494_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2_spec__4___boxed(lean_object* v_e_1495_){
_start:
{
uint8_t v_res_1496_; lean_object* v_r_1497_; 
v_res_1496_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2_spec__4(v_e_1495_);
lean_dec_ref(v_e_1495_);
v_r_1497_ = lean_box(v_res_1496_);
return v_r_1497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2(lean_object* v_cls_1498_, uint8_t v_collapsed_1499_, lean_object* v_tag_1500_, lean_object* v_opts_1501_, uint8_t v_clsEnabled_1502_, lean_object* v_oldTraces_1503_, lean_object* v_msg_1504_, lean_object* v_resStartStop_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_){
_start:
{
lean_object* v_fst_1509_; lean_object* v_snd_1510_; lean_object* v___y_1512_; lean_object* v___y_1513_; lean_object* v_data_1514_; lean_object* v_fst_1517_; lean_object* v_snd_1518_; lean_object* v___x_1519_; uint8_t v___x_1520_; lean_object* v___y_1522_; lean_object* v_a_1523_; uint8_t v___y_1538_; double v___y_1569_; 
v_fst_1509_ = lean_ctor_get(v_resStartStop_1505_, 0);
lean_inc(v_fst_1509_);
v_snd_1510_ = lean_ctor_get(v_resStartStop_1505_, 1);
lean_inc(v_snd_1510_);
lean_dec_ref(v_resStartStop_1505_);
v_fst_1517_ = lean_ctor_get(v_snd_1510_, 0);
lean_inc(v_fst_1517_);
v_snd_1518_ = lean_ctor_get(v_snd_1510_, 1);
lean_inc(v_snd_1518_);
lean_dec(v_snd_1510_);
v___x_1519_ = l_Lean_trace_profiler;
v___x_1520_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_opts_1501_, v___x_1519_);
if (v___x_1520_ == 0)
{
v___y_1538_ = v___x_1520_;
goto v___jp_1537_;
}
else
{
lean_object* v___x_1574_; uint8_t v___x_1575_; 
v___x_1574_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1575_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_opts_1501_, v___x_1574_);
if (v___x_1575_ == 0)
{
lean_object* v___x_1576_; lean_object* v___x_1577_; double v___x_1578_; double v___x_1579_; double v___x_1580_; 
v___x_1576_ = l_Lean_trace_profiler_threshold;
v___x_1577_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(v_opts_1501_, v___x_1576_);
v___x_1578_ = lean_float_of_nat(v___x_1577_);
v___x_1579_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3);
v___x_1580_ = lean_float_div(v___x_1578_, v___x_1579_);
v___y_1569_ = v___x_1580_;
goto v___jp_1568_;
}
else
{
lean_object* v___x_1581_; lean_object* v___x_1582_; double v___x_1583_; 
v___x_1581_ = l_Lean_trace_profiler_threshold;
v___x_1582_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(v_opts_1501_, v___x_1581_);
v___x_1583_ = lean_float_of_nat(v___x_1582_);
v___y_1569_ = v___x_1583_;
goto v___jp_1568_;
}
}
v___jp_1511_:
{
lean_object* v___x_1515_; 
lean_inc(v___y_1513_);
v___x_1515_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__4(v_oldTraces_1503_, v_data_1514_, v___y_1513_, v___y_1512_, v___y_1506_, v___y_1507_);
if (lean_obj_tag(v___x_1515_) == 0)
{
lean_object* v___x_1516_; 
lean_dec_ref_known(v___x_1515_, 1);
v___x_1516_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5___redArg(v_fst_1509_);
return v___x_1516_;
}
else
{
lean_dec(v_fst_1509_);
return v___x_1515_;
}
}
v___jp_1521_:
{
uint8_t v_result_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; double v___x_1527_; lean_object* v_data_1528_; 
v_result_1524_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2_spec__4(v_fst_1509_);
v___x_1525_ = lean_box(v_result_1524_);
v___x_1526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1525_);
v___x_1527_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0);
lean_inc_ref(v_tag_1500_);
lean_inc_ref(v___x_1526_);
lean_inc(v_cls_1498_);
v_data_1528_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1528_, 0, v_cls_1498_);
lean_ctor_set(v_data_1528_, 1, v___x_1526_);
lean_ctor_set(v_data_1528_, 2, v_tag_1500_);
lean_ctor_set_float(v_data_1528_, sizeof(void*)*3, v___x_1527_);
lean_ctor_set_float(v_data_1528_, sizeof(void*)*3 + 8, v___x_1527_);
lean_ctor_set_uint8(v_data_1528_, sizeof(void*)*3 + 16, v_collapsed_1499_);
if (v___x_1520_ == 0)
{
lean_dec_ref_known(v___x_1526_, 1);
lean_dec(v_snd_1518_);
lean_dec(v_fst_1517_);
lean_dec_ref(v_tag_1500_);
lean_dec(v_cls_1498_);
v___y_1512_ = v_a_1523_;
v___y_1513_ = v___y_1522_;
v_data_1514_ = v_data_1528_;
goto v___jp_1511_;
}
else
{
lean_object* v_data_1529_; double v___x_1530_; double v___x_1531_; 
lean_dec_ref_known(v_data_1528_, 3);
v_data_1529_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1529_, 0, v_cls_1498_);
lean_ctor_set(v_data_1529_, 1, v___x_1526_);
lean_ctor_set(v_data_1529_, 2, v_tag_1500_);
v___x_1530_ = lean_unbox_float(v_fst_1517_);
lean_dec(v_fst_1517_);
lean_ctor_set_float(v_data_1529_, sizeof(void*)*3, v___x_1530_);
v___x_1531_ = lean_unbox_float(v_snd_1518_);
lean_dec(v_snd_1518_);
lean_ctor_set_float(v_data_1529_, sizeof(void*)*3 + 8, v___x_1531_);
lean_ctor_set_uint8(v_data_1529_, sizeof(void*)*3 + 16, v_collapsed_1499_);
v___y_1512_ = v_a_1523_;
v___y_1513_ = v___y_1522_;
v_data_1514_ = v_data_1529_;
goto v___jp_1511_;
}
}
v___jp_1532_:
{
lean_object* v_ref_1533_; lean_object* v___x_1534_; 
v_ref_1533_ = lean_ctor_get(v___y_1506_, 5);
lean_inc(v___y_1507_);
lean_inc_ref(v___y_1506_);
lean_inc(v_fst_1509_);
v___x_1534_ = lean_apply_4(v_msg_1504_, v_fst_1509_, v___y_1506_, v___y_1507_, lean_box(0));
if (lean_obj_tag(v___x_1534_) == 0)
{
lean_object* v_a_1535_; 
v_a_1535_ = lean_ctor_get(v___x_1534_, 0);
lean_inc(v_a_1535_);
lean_dec_ref_known(v___x_1534_, 1);
v___y_1522_ = v_ref_1533_;
v_a_1523_ = v_a_1535_;
goto v___jp_1521_;
}
else
{
lean_object* v___x_1536_; 
lean_dec_ref_known(v___x_1534_, 1);
v___x_1536_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2);
v___y_1522_ = v_ref_1533_;
v_a_1523_ = v___x_1536_;
goto v___jp_1521_;
}
}
v___jp_1537_:
{
if (v_clsEnabled_1502_ == 0)
{
if (v___y_1538_ == 0)
{
lean_object* v___x_1539_; lean_object* v_traceState_1540_; lean_object* v_env_1541_; lean_object* v_nextMacroScope_1542_; lean_object* v_ngen_1543_; lean_object* v_auxDeclNGen_1544_; lean_object* v_cache_1545_; lean_object* v_messages_1546_; lean_object* v_infoState_1547_; lean_object* v_snapshotTasks_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1567_; 
lean_dec(v_snd_1518_);
lean_dec(v_fst_1517_);
lean_dec_ref(v_msg_1504_);
lean_dec_ref(v_tag_1500_);
lean_dec(v_cls_1498_);
v___x_1539_ = lean_st_ref_take(v___y_1507_);
v_traceState_1540_ = lean_ctor_get(v___x_1539_, 4);
v_env_1541_ = lean_ctor_get(v___x_1539_, 0);
v_nextMacroScope_1542_ = lean_ctor_get(v___x_1539_, 1);
v_ngen_1543_ = lean_ctor_get(v___x_1539_, 2);
v_auxDeclNGen_1544_ = lean_ctor_get(v___x_1539_, 3);
v_cache_1545_ = lean_ctor_get(v___x_1539_, 5);
v_messages_1546_ = lean_ctor_get(v___x_1539_, 6);
v_infoState_1547_ = lean_ctor_get(v___x_1539_, 7);
v_snapshotTasks_1548_ = lean_ctor_get(v___x_1539_, 8);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1539_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1550_ = v___x_1539_;
v_isShared_1551_ = v_isSharedCheck_1567_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_snapshotTasks_1548_);
lean_inc(v_infoState_1547_);
lean_inc(v_messages_1546_);
lean_inc(v_cache_1545_);
lean_inc(v_traceState_1540_);
lean_inc(v_auxDeclNGen_1544_);
lean_inc(v_ngen_1543_);
lean_inc(v_nextMacroScope_1542_);
lean_inc(v_env_1541_);
lean_dec(v___x_1539_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1567_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
uint64_t v_tid_1552_; lean_object* v_traces_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1566_; 
v_tid_1552_ = lean_ctor_get_uint64(v_traceState_1540_, sizeof(void*)*1);
v_traces_1553_ = lean_ctor_get(v_traceState_1540_, 0);
v_isSharedCheck_1566_ = !lean_is_exclusive(v_traceState_1540_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1555_ = v_traceState_1540_;
v_isShared_1556_ = v_isSharedCheck_1566_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_traces_1553_);
lean_dec(v_traceState_1540_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1566_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1557_; lean_object* v___x_1559_; 
v___x_1557_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1503_, v_traces_1553_);
lean_dec_ref(v_traces_1553_);
if (v_isShared_1556_ == 0)
{
lean_ctor_set(v___x_1555_, 0, v___x_1557_);
v___x_1559_ = v___x_1555_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v___x_1557_);
lean_ctor_set_uint64(v_reuseFailAlloc_1565_, sizeof(void*)*1, v_tid_1552_);
v___x_1559_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
lean_object* v___x_1561_; 
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 4, v___x_1559_);
v___x_1561_ = v___x_1550_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_env_1541_);
lean_ctor_set(v_reuseFailAlloc_1564_, 1, v_nextMacroScope_1542_);
lean_ctor_set(v_reuseFailAlloc_1564_, 2, v_ngen_1543_);
lean_ctor_set(v_reuseFailAlloc_1564_, 3, v_auxDeclNGen_1544_);
lean_ctor_set(v_reuseFailAlloc_1564_, 4, v___x_1559_);
lean_ctor_set(v_reuseFailAlloc_1564_, 5, v_cache_1545_);
lean_ctor_set(v_reuseFailAlloc_1564_, 6, v_messages_1546_);
lean_ctor_set(v_reuseFailAlloc_1564_, 7, v_infoState_1547_);
lean_ctor_set(v_reuseFailAlloc_1564_, 8, v_snapshotTasks_1548_);
v___x_1561_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1562_ = lean_st_ref_set(v___y_1507_, v___x_1561_);
v___x_1563_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5___redArg(v_fst_1509_);
return v___x_1563_;
}
}
}
}
}
else
{
goto v___jp_1532_;
}
}
else
{
goto v___jp_1532_;
}
}
v___jp_1568_:
{
double v___x_1570_; double v___x_1571_; double v___x_1572_; uint8_t v___x_1573_; 
v___x_1570_ = lean_unbox_float(v_snd_1518_);
v___x_1571_ = lean_unbox_float(v_fst_1517_);
v___x_1572_ = lean_float_sub(v___x_1570_, v___x_1571_);
v___x_1573_ = lean_float_decLt(v___y_1569_, v___x_1572_);
v___y_1538_ = v___x_1573_;
goto v___jp_1537_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2___boxed(lean_object* v_cls_1584_, lean_object* v_collapsed_1585_, lean_object* v_tag_1586_, lean_object* v_opts_1587_, lean_object* v_clsEnabled_1588_, lean_object* v_oldTraces_1589_, lean_object* v_msg_1590_, lean_object* v_resStartStop_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_){
_start:
{
uint8_t v_collapsed_boxed_1595_; uint8_t v_clsEnabled_boxed_1596_; lean_object* v_res_1597_; 
v_collapsed_boxed_1595_ = lean_unbox(v_collapsed_1585_);
v_clsEnabled_boxed_1596_ = lean_unbox(v_clsEnabled_1588_);
v_res_1597_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2(v_cls_1584_, v_collapsed_boxed_1595_, v_tag_1586_, v_opts_1587_, v_clsEnabled_boxed_1596_, v_oldTraces_1589_, v_msg_1590_, v_resStartStop_1591_, v___y_1592_, v___y_1593_);
lean_dec(v___y_1593_);
lean_dec_ref(v___y_1592_);
lean_dec_ref(v_opts_1587_);
return v_res_1597_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0_spec__0(lean_object* v_e_1598_){
_start:
{
if (lean_obj_tag(v_e_1598_) == 0)
{
uint8_t v___x_1599_; 
v___x_1599_ = 2;
return v___x_1599_;
}
else
{
uint8_t v___x_1600_; 
v___x_1600_ = 0;
return v___x_1600_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0_spec__0___boxed(lean_object* v_e_1601_){
_start:
{
uint8_t v_res_1602_; lean_object* v_r_1603_; 
v_res_1602_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0_spec__0(v_e_1601_);
lean_dec_ref(v_e_1601_);
v_r_1603_ = lean_box(v_res_1602_);
return v_r_1603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0(lean_object* v_cls_1604_, uint8_t v_collapsed_1605_, lean_object* v_tag_1606_, lean_object* v_opts_1607_, uint8_t v_clsEnabled_1608_, lean_object* v_oldTraces_1609_, lean_object* v_msg_1610_, lean_object* v_resStartStop_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_){
_start:
{
lean_object* v_fst_1615_; lean_object* v_snd_1616_; lean_object* v___y_1618_; lean_object* v___y_1619_; lean_object* v_data_1620_; lean_object* v_fst_1631_; lean_object* v_snd_1632_; lean_object* v___x_1633_; uint8_t v___x_1634_; lean_object* v___y_1636_; lean_object* v_a_1637_; uint8_t v___y_1652_; double v___y_1683_; 
v_fst_1615_ = lean_ctor_get(v_resStartStop_1611_, 0);
lean_inc(v_fst_1615_);
v_snd_1616_ = lean_ctor_get(v_resStartStop_1611_, 1);
lean_inc(v_snd_1616_);
lean_dec_ref(v_resStartStop_1611_);
v_fst_1631_ = lean_ctor_get(v_snd_1616_, 0);
lean_inc(v_fst_1631_);
v_snd_1632_ = lean_ctor_get(v_snd_1616_, 1);
lean_inc(v_snd_1632_);
lean_dec(v_snd_1616_);
v___x_1633_ = l_Lean_trace_profiler;
v___x_1634_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_opts_1607_, v___x_1633_);
if (v___x_1634_ == 0)
{
v___y_1652_ = v___x_1634_;
goto v___jp_1651_;
}
else
{
lean_object* v___x_1688_; uint8_t v___x_1689_; 
v___x_1688_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1689_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_opts_1607_, v___x_1688_);
if (v___x_1689_ == 0)
{
lean_object* v___x_1690_; lean_object* v___x_1691_; double v___x_1692_; double v___x_1693_; double v___x_1694_; 
v___x_1690_ = l_Lean_trace_profiler_threshold;
v___x_1691_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(v_opts_1607_, v___x_1690_);
v___x_1692_ = lean_float_of_nat(v___x_1691_);
v___x_1693_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3);
v___x_1694_ = lean_float_div(v___x_1692_, v___x_1693_);
v___y_1683_ = v___x_1694_;
goto v___jp_1682_;
}
else
{
lean_object* v___x_1695_; lean_object* v___x_1696_; double v___x_1697_; 
v___x_1695_ = l_Lean_trace_profiler_threshold;
v___x_1696_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(v_opts_1607_, v___x_1695_);
v___x_1697_ = lean_float_of_nat(v___x_1696_);
v___y_1683_ = v___x_1697_;
goto v___jp_1682_;
}
}
v___jp_1617_:
{
lean_object* v___x_1621_; 
lean_inc(v___y_1618_);
v___x_1621_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__4(v_oldTraces_1609_, v_data_1620_, v___y_1618_, v___y_1619_, v___y_1612_, v___y_1613_);
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_object* v___x_1622_; 
lean_dec_ref_known(v___x_1621_, 1);
v___x_1622_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5___redArg(v_fst_1615_);
return v___x_1622_;
}
else
{
lean_object* v_a_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1630_; 
lean_dec(v_fst_1615_);
v_a_1623_ = lean_ctor_get(v___x_1621_, 0);
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1625_ = v___x_1621_;
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_a_1623_);
lean_dec(v___x_1621_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1628_; 
if (v_isShared_1626_ == 0)
{
v___x_1628_ = v___x_1625_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_a_1623_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
}
}
v___jp_1635_:
{
uint8_t v_result_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; double v___x_1641_; lean_object* v_data_1642_; 
v_result_1638_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0_spec__0(v_fst_1615_);
v___x_1639_ = lean_box(v_result_1638_);
v___x_1640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1639_);
v___x_1641_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0);
lean_inc_ref(v_tag_1606_);
lean_inc_ref(v___x_1640_);
lean_inc(v_cls_1604_);
v_data_1642_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1642_, 0, v_cls_1604_);
lean_ctor_set(v_data_1642_, 1, v___x_1640_);
lean_ctor_set(v_data_1642_, 2, v_tag_1606_);
lean_ctor_set_float(v_data_1642_, sizeof(void*)*3, v___x_1641_);
lean_ctor_set_float(v_data_1642_, sizeof(void*)*3 + 8, v___x_1641_);
lean_ctor_set_uint8(v_data_1642_, sizeof(void*)*3 + 16, v_collapsed_1605_);
if (v___x_1634_ == 0)
{
lean_dec_ref_known(v___x_1640_, 1);
lean_dec(v_snd_1632_);
lean_dec(v_fst_1631_);
lean_dec_ref(v_tag_1606_);
lean_dec(v_cls_1604_);
v___y_1618_ = v___y_1636_;
v___y_1619_ = v_a_1637_;
v_data_1620_ = v_data_1642_;
goto v___jp_1617_;
}
else
{
lean_object* v_data_1643_; double v___x_1644_; double v___x_1645_; 
lean_dec_ref_known(v_data_1642_, 3);
v_data_1643_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1643_, 0, v_cls_1604_);
lean_ctor_set(v_data_1643_, 1, v___x_1640_);
lean_ctor_set(v_data_1643_, 2, v_tag_1606_);
v___x_1644_ = lean_unbox_float(v_fst_1631_);
lean_dec(v_fst_1631_);
lean_ctor_set_float(v_data_1643_, sizeof(void*)*3, v___x_1644_);
v___x_1645_ = lean_unbox_float(v_snd_1632_);
lean_dec(v_snd_1632_);
lean_ctor_set_float(v_data_1643_, sizeof(void*)*3 + 8, v___x_1645_);
lean_ctor_set_uint8(v_data_1643_, sizeof(void*)*3 + 16, v_collapsed_1605_);
v___y_1618_ = v___y_1636_;
v___y_1619_ = v_a_1637_;
v_data_1620_ = v_data_1643_;
goto v___jp_1617_;
}
}
v___jp_1646_:
{
lean_object* v_ref_1647_; lean_object* v___x_1648_; 
v_ref_1647_ = lean_ctor_get(v___y_1612_, 5);
lean_inc(v___y_1613_);
lean_inc_ref(v___y_1612_);
lean_inc(v_fst_1615_);
v___x_1648_ = lean_apply_4(v_msg_1610_, v_fst_1615_, v___y_1612_, v___y_1613_, lean_box(0));
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_object* v_a_1649_; 
v_a_1649_ = lean_ctor_get(v___x_1648_, 0);
lean_inc(v_a_1649_);
lean_dec_ref_known(v___x_1648_, 1);
v___y_1636_ = v_ref_1647_;
v_a_1637_ = v_a_1649_;
goto v___jp_1635_;
}
else
{
lean_object* v___x_1650_; 
lean_dec_ref_known(v___x_1648_, 1);
v___x_1650_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2);
v___y_1636_ = v_ref_1647_;
v_a_1637_ = v___x_1650_;
goto v___jp_1635_;
}
}
v___jp_1651_:
{
if (v_clsEnabled_1608_ == 0)
{
if (v___y_1652_ == 0)
{
lean_object* v___x_1653_; lean_object* v_traceState_1654_; lean_object* v_env_1655_; lean_object* v_nextMacroScope_1656_; lean_object* v_ngen_1657_; lean_object* v_auxDeclNGen_1658_; lean_object* v_cache_1659_; lean_object* v_messages_1660_; lean_object* v_infoState_1661_; lean_object* v_snapshotTasks_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1681_; 
lean_dec(v_snd_1632_);
lean_dec(v_fst_1631_);
lean_dec_ref(v_msg_1610_);
lean_dec_ref(v_tag_1606_);
lean_dec(v_cls_1604_);
v___x_1653_ = lean_st_ref_take(v___y_1613_);
v_traceState_1654_ = lean_ctor_get(v___x_1653_, 4);
v_env_1655_ = lean_ctor_get(v___x_1653_, 0);
v_nextMacroScope_1656_ = lean_ctor_get(v___x_1653_, 1);
v_ngen_1657_ = lean_ctor_get(v___x_1653_, 2);
v_auxDeclNGen_1658_ = lean_ctor_get(v___x_1653_, 3);
v_cache_1659_ = lean_ctor_get(v___x_1653_, 5);
v_messages_1660_ = lean_ctor_get(v___x_1653_, 6);
v_infoState_1661_ = lean_ctor_get(v___x_1653_, 7);
v_snapshotTasks_1662_ = lean_ctor_get(v___x_1653_, 8);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1653_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1664_ = v___x_1653_;
v_isShared_1665_ = v_isSharedCheck_1681_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_snapshotTasks_1662_);
lean_inc(v_infoState_1661_);
lean_inc(v_messages_1660_);
lean_inc(v_cache_1659_);
lean_inc(v_traceState_1654_);
lean_inc(v_auxDeclNGen_1658_);
lean_inc(v_ngen_1657_);
lean_inc(v_nextMacroScope_1656_);
lean_inc(v_env_1655_);
lean_dec(v___x_1653_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1681_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
uint64_t v_tid_1666_; lean_object* v_traces_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1680_; 
v_tid_1666_ = lean_ctor_get_uint64(v_traceState_1654_, sizeof(void*)*1);
v_traces_1667_ = lean_ctor_get(v_traceState_1654_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v_traceState_1654_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1669_ = v_traceState_1654_;
v_isShared_1670_ = v_isSharedCheck_1680_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_traces_1667_);
lean_dec(v_traceState_1654_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1680_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v___x_1671_; lean_object* v___x_1673_; 
v___x_1671_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1609_, v_traces_1667_);
lean_dec_ref(v_traces_1667_);
if (v_isShared_1670_ == 0)
{
lean_ctor_set(v___x_1669_, 0, v___x_1671_);
v___x_1673_ = v___x_1669_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v___x_1671_);
lean_ctor_set_uint64(v_reuseFailAlloc_1679_, sizeof(void*)*1, v_tid_1666_);
v___x_1673_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
lean_object* v___x_1675_; 
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 4, v___x_1673_);
v___x_1675_ = v___x_1664_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_env_1655_);
lean_ctor_set(v_reuseFailAlloc_1678_, 1, v_nextMacroScope_1656_);
lean_ctor_set(v_reuseFailAlloc_1678_, 2, v_ngen_1657_);
lean_ctor_set(v_reuseFailAlloc_1678_, 3, v_auxDeclNGen_1658_);
lean_ctor_set(v_reuseFailAlloc_1678_, 4, v___x_1673_);
lean_ctor_set(v_reuseFailAlloc_1678_, 5, v_cache_1659_);
lean_ctor_set(v_reuseFailAlloc_1678_, 6, v_messages_1660_);
lean_ctor_set(v_reuseFailAlloc_1678_, 7, v_infoState_1661_);
lean_ctor_set(v_reuseFailAlloc_1678_, 8, v_snapshotTasks_1662_);
v___x_1675_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1676_ = lean_st_ref_set(v___y_1613_, v___x_1675_);
v___x_1677_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5___redArg(v_fst_1615_);
return v___x_1677_;
}
}
}
}
}
else
{
goto v___jp_1646_;
}
}
else
{
goto v___jp_1646_;
}
}
v___jp_1682_:
{
double v___x_1684_; double v___x_1685_; double v___x_1686_; uint8_t v___x_1687_; 
v___x_1684_ = lean_unbox_float(v_snd_1632_);
v___x_1685_ = lean_unbox_float(v_fst_1631_);
v___x_1686_ = lean_float_sub(v___x_1684_, v___x_1685_);
v___x_1687_ = lean_float_decLt(v___y_1683_, v___x_1686_);
v___y_1652_ = v___x_1687_;
goto v___jp_1651_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0___boxed(lean_object* v_cls_1698_, lean_object* v_collapsed_1699_, lean_object* v_tag_1700_, lean_object* v_opts_1701_, lean_object* v_clsEnabled_1702_, lean_object* v_oldTraces_1703_, lean_object* v_msg_1704_, lean_object* v_resStartStop_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_){
_start:
{
uint8_t v_collapsed_boxed_1709_; uint8_t v_clsEnabled_boxed_1710_; lean_object* v_res_1711_; 
v_collapsed_boxed_1709_ = lean_unbox(v_collapsed_1699_);
v_clsEnabled_boxed_1710_ = lean_unbox(v_clsEnabled_1702_);
v_res_1711_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0(v_cls_1698_, v_collapsed_boxed_1709_, v_tag_1700_, v_opts_1701_, v_clsEnabled_boxed_1710_, v_oldTraces_1703_, v_msg_1704_, v_resStartStop_1705_, v___y_1706_, v___y_1707_);
lean_dec(v___y_1707_);
lean_dec_ref(v___y_1706_);
lean_dec_ref(v_opts_1701_);
return v_res_1711_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1_spec__2(lean_object* v_e_1712_){
_start:
{
if (lean_obj_tag(v_e_1712_) == 0)
{
uint8_t v___x_1713_; 
v___x_1713_ = 2;
return v___x_1713_;
}
else
{
uint8_t v___x_1714_; 
v___x_1714_ = 0;
return v___x_1714_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1_spec__2___boxed(lean_object* v_e_1715_){
_start:
{
uint8_t v_res_1716_; lean_object* v_r_1717_; 
v_res_1716_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1_spec__2(v_e_1715_);
lean_dec_ref(v_e_1715_);
v_r_1717_ = lean_box(v_res_1716_);
return v_r_1717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1(lean_object* v_cls_1718_, uint8_t v_collapsed_1719_, lean_object* v_tag_1720_, lean_object* v_opts_1721_, uint8_t v_clsEnabled_1722_, lean_object* v_oldTraces_1723_, lean_object* v_msg_1724_, lean_object* v_resStartStop_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_){
_start:
{
lean_object* v_fst_1729_; lean_object* v_snd_1730_; lean_object* v___y_1732_; lean_object* v___y_1733_; lean_object* v_data_1734_; lean_object* v_fst_1745_; lean_object* v_snd_1746_; lean_object* v___x_1747_; uint8_t v___x_1748_; lean_object* v___y_1750_; lean_object* v_a_1751_; uint8_t v___y_1766_; double v___y_1797_; 
v_fst_1729_ = lean_ctor_get(v_resStartStop_1725_, 0);
lean_inc(v_fst_1729_);
v_snd_1730_ = lean_ctor_get(v_resStartStop_1725_, 1);
lean_inc(v_snd_1730_);
lean_dec_ref(v_resStartStop_1725_);
v_fst_1745_ = lean_ctor_get(v_snd_1730_, 0);
lean_inc(v_fst_1745_);
v_snd_1746_ = lean_ctor_get(v_snd_1730_, 1);
lean_inc(v_snd_1746_);
lean_dec(v_snd_1730_);
v___x_1747_ = l_Lean_trace_profiler;
v___x_1748_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_opts_1721_, v___x_1747_);
if (v___x_1748_ == 0)
{
v___y_1766_ = v___x_1748_;
goto v___jp_1765_;
}
else
{
lean_object* v___x_1802_; uint8_t v___x_1803_; 
v___x_1802_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1803_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_opts_1721_, v___x_1802_);
if (v___x_1803_ == 0)
{
lean_object* v___x_1804_; lean_object* v___x_1805_; double v___x_1806_; double v___x_1807_; double v___x_1808_; 
v___x_1804_ = l_Lean_trace_profiler_threshold;
v___x_1805_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(v_opts_1721_, v___x_1804_);
v___x_1806_ = lean_float_of_nat(v___x_1805_);
v___x_1807_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3);
v___x_1808_ = lean_float_div(v___x_1806_, v___x_1807_);
v___y_1797_ = v___x_1808_;
goto v___jp_1796_;
}
else
{
lean_object* v___x_1809_; lean_object* v___x_1810_; double v___x_1811_; 
v___x_1809_ = l_Lean_trace_profiler_threshold;
v___x_1810_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(v_opts_1721_, v___x_1809_);
v___x_1811_ = lean_float_of_nat(v___x_1810_);
v___y_1797_ = v___x_1811_;
goto v___jp_1796_;
}
}
v___jp_1731_:
{
lean_object* v___x_1735_; 
lean_inc(v___y_1732_);
v___x_1735_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__4(v_oldTraces_1723_, v_data_1734_, v___y_1732_, v___y_1733_, v___y_1726_, v___y_1727_);
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_object* v___x_1736_; 
lean_dec_ref_known(v___x_1735_, 1);
v___x_1736_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5___redArg(v_fst_1729_);
return v___x_1736_;
}
else
{
lean_object* v_a_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1744_; 
lean_dec(v_fst_1729_);
v_a_1737_ = lean_ctor_get(v___x_1735_, 0);
v_isSharedCheck_1744_ = !lean_is_exclusive(v___x_1735_);
if (v_isSharedCheck_1744_ == 0)
{
v___x_1739_ = v___x_1735_;
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_a_1737_);
lean_dec(v___x_1735_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v___x_1742_; 
if (v_isShared_1740_ == 0)
{
v___x_1742_ = v___x_1739_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v_a_1737_);
v___x_1742_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
return v___x_1742_;
}
}
}
}
v___jp_1749_:
{
uint8_t v_result_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; double v___x_1755_; lean_object* v_data_1756_; 
v_result_1752_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1_spec__2(v_fst_1729_);
v___x_1753_ = lean_box(v_result_1752_);
v___x_1754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1753_);
v___x_1755_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0);
lean_inc_ref(v_tag_1720_);
lean_inc_ref(v___x_1754_);
lean_inc(v_cls_1718_);
v_data_1756_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1756_, 0, v_cls_1718_);
lean_ctor_set(v_data_1756_, 1, v___x_1754_);
lean_ctor_set(v_data_1756_, 2, v_tag_1720_);
lean_ctor_set_float(v_data_1756_, sizeof(void*)*3, v___x_1755_);
lean_ctor_set_float(v_data_1756_, sizeof(void*)*3 + 8, v___x_1755_);
lean_ctor_set_uint8(v_data_1756_, sizeof(void*)*3 + 16, v_collapsed_1719_);
if (v___x_1748_ == 0)
{
lean_dec_ref_known(v___x_1754_, 1);
lean_dec(v_snd_1746_);
lean_dec(v_fst_1745_);
lean_dec_ref(v_tag_1720_);
lean_dec(v_cls_1718_);
v___y_1732_ = v___y_1750_;
v___y_1733_ = v_a_1751_;
v_data_1734_ = v_data_1756_;
goto v___jp_1731_;
}
else
{
lean_object* v_data_1757_; double v___x_1758_; double v___x_1759_; 
lean_dec_ref_known(v_data_1756_, 3);
v_data_1757_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1757_, 0, v_cls_1718_);
lean_ctor_set(v_data_1757_, 1, v___x_1754_);
lean_ctor_set(v_data_1757_, 2, v_tag_1720_);
v___x_1758_ = lean_unbox_float(v_fst_1745_);
lean_dec(v_fst_1745_);
lean_ctor_set_float(v_data_1757_, sizeof(void*)*3, v___x_1758_);
v___x_1759_ = lean_unbox_float(v_snd_1746_);
lean_dec(v_snd_1746_);
lean_ctor_set_float(v_data_1757_, sizeof(void*)*3 + 8, v___x_1759_);
lean_ctor_set_uint8(v_data_1757_, sizeof(void*)*3 + 16, v_collapsed_1719_);
v___y_1732_ = v___y_1750_;
v___y_1733_ = v_a_1751_;
v_data_1734_ = v_data_1757_;
goto v___jp_1731_;
}
}
v___jp_1760_:
{
lean_object* v_ref_1761_; lean_object* v___x_1762_; 
v_ref_1761_ = lean_ctor_get(v___y_1726_, 5);
lean_inc(v___y_1727_);
lean_inc_ref(v___y_1726_);
lean_inc(v_fst_1729_);
v___x_1762_ = lean_apply_4(v_msg_1724_, v_fst_1729_, v___y_1726_, v___y_1727_, lean_box(0));
if (lean_obj_tag(v___x_1762_) == 0)
{
lean_object* v_a_1763_; 
v_a_1763_ = lean_ctor_get(v___x_1762_, 0);
lean_inc(v_a_1763_);
lean_dec_ref_known(v___x_1762_, 1);
v___y_1750_ = v_ref_1761_;
v_a_1751_ = v_a_1763_;
goto v___jp_1749_;
}
else
{
lean_object* v___x_1764_; 
lean_dec_ref_known(v___x_1762_, 1);
v___x_1764_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2);
v___y_1750_ = v_ref_1761_;
v_a_1751_ = v___x_1764_;
goto v___jp_1749_;
}
}
v___jp_1765_:
{
if (v_clsEnabled_1722_ == 0)
{
if (v___y_1766_ == 0)
{
lean_object* v___x_1767_; lean_object* v_traceState_1768_; lean_object* v_env_1769_; lean_object* v_nextMacroScope_1770_; lean_object* v_ngen_1771_; lean_object* v_auxDeclNGen_1772_; lean_object* v_cache_1773_; lean_object* v_messages_1774_; lean_object* v_infoState_1775_; lean_object* v_snapshotTasks_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1795_; 
lean_dec(v_snd_1746_);
lean_dec(v_fst_1745_);
lean_dec_ref(v_msg_1724_);
lean_dec_ref(v_tag_1720_);
lean_dec(v_cls_1718_);
v___x_1767_ = lean_st_ref_take(v___y_1727_);
v_traceState_1768_ = lean_ctor_get(v___x_1767_, 4);
v_env_1769_ = lean_ctor_get(v___x_1767_, 0);
v_nextMacroScope_1770_ = lean_ctor_get(v___x_1767_, 1);
v_ngen_1771_ = lean_ctor_get(v___x_1767_, 2);
v_auxDeclNGen_1772_ = lean_ctor_get(v___x_1767_, 3);
v_cache_1773_ = lean_ctor_get(v___x_1767_, 5);
v_messages_1774_ = lean_ctor_get(v___x_1767_, 6);
v_infoState_1775_ = lean_ctor_get(v___x_1767_, 7);
v_snapshotTasks_1776_ = lean_ctor_get(v___x_1767_, 8);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1767_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1778_ = v___x_1767_;
v_isShared_1779_ = v_isSharedCheck_1795_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_snapshotTasks_1776_);
lean_inc(v_infoState_1775_);
lean_inc(v_messages_1774_);
lean_inc(v_cache_1773_);
lean_inc(v_traceState_1768_);
lean_inc(v_auxDeclNGen_1772_);
lean_inc(v_ngen_1771_);
lean_inc(v_nextMacroScope_1770_);
lean_inc(v_env_1769_);
lean_dec(v___x_1767_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1795_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
uint64_t v_tid_1780_; lean_object* v_traces_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1794_; 
v_tid_1780_ = lean_ctor_get_uint64(v_traceState_1768_, sizeof(void*)*1);
v_traces_1781_ = lean_ctor_get(v_traceState_1768_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v_traceState_1768_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1783_ = v_traceState_1768_;
v_isShared_1784_ = v_isSharedCheck_1794_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_traces_1781_);
lean_dec(v_traceState_1768_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1794_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1785_; lean_object* v___x_1787_; 
v___x_1785_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1723_, v_traces_1781_);
lean_dec_ref(v_traces_1781_);
if (v_isShared_1784_ == 0)
{
lean_ctor_set(v___x_1783_, 0, v___x_1785_);
v___x_1787_ = v___x_1783_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v___x_1785_);
lean_ctor_set_uint64(v_reuseFailAlloc_1793_, sizeof(void*)*1, v_tid_1780_);
v___x_1787_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
lean_object* v___x_1789_; 
if (v_isShared_1779_ == 0)
{
lean_ctor_set(v___x_1778_, 4, v___x_1787_);
v___x_1789_ = v___x_1778_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_env_1769_);
lean_ctor_set(v_reuseFailAlloc_1792_, 1, v_nextMacroScope_1770_);
lean_ctor_set(v_reuseFailAlloc_1792_, 2, v_ngen_1771_);
lean_ctor_set(v_reuseFailAlloc_1792_, 3, v_auxDeclNGen_1772_);
lean_ctor_set(v_reuseFailAlloc_1792_, 4, v___x_1787_);
lean_ctor_set(v_reuseFailAlloc_1792_, 5, v_cache_1773_);
lean_ctor_set(v_reuseFailAlloc_1792_, 6, v_messages_1774_);
lean_ctor_set(v_reuseFailAlloc_1792_, 7, v_infoState_1775_);
lean_ctor_set(v_reuseFailAlloc_1792_, 8, v_snapshotTasks_1776_);
v___x_1789_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1790_ = lean_st_ref_set(v___y_1727_, v___x_1789_);
v___x_1791_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5___redArg(v_fst_1729_);
return v___x_1791_;
}
}
}
}
}
else
{
goto v___jp_1760_;
}
}
else
{
goto v___jp_1760_;
}
}
v___jp_1796_:
{
double v___x_1798_; double v___x_1799_; double v___x_1800_; uint8_t v___x_1801_; 
v___x_1798_ = lean_unbox_float(v_snd_1746_);
v___x_1799_ = lean_unbox_float(v_fst_1745_);
v___x_1800_ = lean_float_sub(v___x_1798_, v___x_1799_);
v___x_1801_ = lean_float_decLt(v___y_1797_, v___x_1800_);
v___y_1766_ = v___x_1801_;
goto v___jp_1765_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1___boxed(lean_object* v_cls_1812_, lean_object* v_collapsed_1813_, lean_object* v_tag_1814_, lean_object* v_opts_1815_, lean_object* v_clsEnabled_1816_, lean_object* v_oldTraces_1817_, lean_object* v_msg_1818_, lean_object* v_resStartStop_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_){
_start:
{
uint8_t v_collapsed_boxed_1823_; uint8_t v_clsEnabled_boxed_1824_; lean_object* v_res_1825_; 
v_collapsed_boxed_1823_ = lean_unbox(v_collapsed_1813_);
v_clsEnabled_boxed_1824_ = lean_unbox(v_clsEnabled_1816_);
v_res_1825_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1(v_cls_1812_, v_collapsed_boxed_1823_, v_tag_1814_, v_opts_1815_, v_clsEnabled_boxed_1824_, v_oldTraces_1817_, v_msg_1818_, v_resStartStop_1819_, v___y_1820_, v___y_1821_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
lean_dec_ref(v_opts_1815_);
return v_res_1825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__4(lean_object* v___f_1826_, lean_object* v_lratPath_1827_, uint8_t v_trimProofs_1828_, lean_object* v___f_1829_, lean_object* v_solver_1830_, lean_object* v_timeout_1831_, uint8_t v_binaryProofs_1832_, uint8_t v_solverMode_1833_, lean_object* v___f_1834_, lean_object* v___f_1835_, lean_object* v_cnfHandle_1836_, lean_object* v_cnfPath_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_){
_start:
{
lean_object* v___y_1842_; lean_object* v_options_1860_; lean_object* v_ref_1861_; lean_object* v_inheritedTraceOptions_1862_; uint8_t v_hasTrace_1863_; lean_object* v___x_1864_; uint8_t v___x_1865_; lean_object* v___x_1866_; uint8_t v___y_1868_; lean_object* v___y_1869_; lean_object* v___y_1870_; lean_object* v___y_1871_; lean_object* v_a_1872_; uint8_t v___y_1882_; lean_object* v___y_1883_; lean_object* v___y_1884_; lean_object* v___y_1885_; lean_object* v_a_1886_; uint8_t v___y_1899_; lean_object* v___y_1900_; lean_object* v___y_1942_; uint8_t v_a_1943_; lean_object* v___y_1948_; lean_object* v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_1980_; uint8_t v___y_1981_; lean_object* v_a_1982_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v___y_1994_; uint8_t v___y_1995_; lean_object* v_a_1996_; lean_object* v___y_2009_; uint8_t v___y_2010_; lean_object* v___y_2052_; uint8_t v_a_2053_; lean_object* v___y_2063_; uint8_t v___y_2073_; lean_object* v___y_2074_; lean_object* v___y_2075_; lean_object* v_a_2076_; uint8_t v___y_2089_; lean_object* v___y_2090_; lean_object* v___y_2091_; lean_object* v_a_2092_; uint8_t v___y_2095_; lean_object* v___y_2096_; lean_object* v___y_2097_; lean_object* v_a_2098_; uint8_t v___y_2108_; lean_object* v___y_2109_; lean_object* v___y_2110_; lean_object* v_a_2111_; uint8_t v___y_2114_; uint8_t v_a_2212_; uint8_t v___x_2255_; 
v_options_1860_ = lean_ctor_get(v___y_1838_, 2);
v_ref_1861_ = lean_ctor_get(v___y_1838_, 5);
v_inheritedTraceOptions_1862_ = lean_ctor_get(v___y_1838_, 13);
v_hasTrace_1863_ = lean_ctor_get_uint8(v_options_1860_, sizeof(void*)*1);
v___x_1864_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__3));
v___x_1865_ = 1;
v___x_1866_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0___closed__0));
v___x_2255_ = lean_bool_not(v_hasTrace_1863_);
if (v___x_2255_ == 0)
{
if (v_hasTrace_1863_ == 0)
{
v_a_2212_ = v_hasTrace_1863_;
goto v___jp_2211_;
}
else
{
lean_object* v___x_2256_; uint8_t v___x_2257_; 
v___x_2256_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6);
v___x_2257_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1862_, v_options_1860_, v___x_2256_);
if (v___x_2257_ == 0)
{
v_a_2212_ = v___x_2257_;
goto v___jp_2211_;
}
else
{
v___y_2114_ = v___x_2257_;
goto v___jp_2113_;
}
}
}
else
{
lean_object* v___x_2258_; 
lean_dec_ref(v___f_1834_);
v___x_2258_ = l_IO_lazyPure___redArg(v___f_1835_);
if (lean_obj_tag(v___x_2258_) == 0)
{
lean_object* v_a_2259_; lean_object* v___x_2260_; 
v_a_2259_ = lean_ctor_get(v___x_2258_, 0);
lean_inc(v_a_2259_);
lean_dec_ref_known(v___x_2258_, 1);
v___x_2260_ = lean_io_prim_handle_put_str(v_cnfHandle_1836_, v_a_2259_);
lean_dec(v_a_2259_);
if (lean_obj_tag(v___x_2260_) == 0)
{
lean_object* v___x_2261_; 
lean_dec_ref_known(v___x_2260_, 1);
v___x_2261_ = lean_io_prim_handle_flush(v_cnfHandle_1836_);
if (lean_obj_tag(v___x_2261_) == 0)
{
lean_dec_ref_known(v___x_2261_, 1);
goto v___jp_2057_;
}
else
{
lean_object* v_a_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2273_; 
lean_dec_ref(v_cnfPath_1837_);
lean_dec_ref(v_solver_1830_);
lean_dec_ref(v___f_1829_);
lean_dec_ref(v_lratPath_1827_);
lean_dec_ref(v___f_1826_);
v_a_2262_ = lean_ctor_get(v___x_2261_, 0);
v_isSharedCheck_2273_ = !lean_is_exclusive(v___x_2261_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2264_ = v___x_2261_;
v_isShared_2265_ = v_isSharedCheck_2273_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_a_2262_);
lean_dec(v___x_2261_);
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
lean_inc(v_ref_1861_);
v___x_2269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2269_, 0, v_ref_1861_);
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
lean_object* v_a_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2285_; 
lean_dec_ref(v_cnfPath_1837_);
lean_dec_ref(v_solver_1830_);
lean_dec_ref(v___f_1829_);
lean_dec_ref(v_lratPath_1827_);
lean_dec_ref(v___f_1826_);
v_a_2274_ = lean_ctor_get(v___x_2260_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2260_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2276_ = v___x_2260_;
v_isShared_2277_ = v_isSharedCheck_2285_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_a_2274_);
lean_dec(v___x_2260_);
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
lean_inc(v_ref_1861_);
v___x_2281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2281_, 0, v_ref_1861_);
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
else
{
lean_object* v_a_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2297_; 
lean_dec_ref(v_cnfPath_1837_);
lean_dec_ref(v_solver_1830_);
lean_dec_ref(v___f_1829_);
lean_dec_ref(v_lratPath_1827_);
lean_dec_ref(v___f_1826_);
v_a_2286_ = lean_ctor_get(v___x_2258_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2258_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2288_ = v___x_2258_;
v_isShared_2289_ = v_isSharedCheck_2297_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_a_2286_);
lean_dec(v___x_2258_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2297_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2295_; 
v___x_2290_ = lean_io_error_to_string(v_a_2286_);
v___x_2291_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2291_, 0, v___x_2290_);
v___x_2292_ = l_Lean_MessageData_ofFormat(v___x_2291_);
lean_inc(v_ref_1861_);
v___x_2293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2293_, 0, v_ref_1861_);
lean_ctor_set(v___x_2293_, 1, v___x_2292_);
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 0, v___x_2293_);
v___x_2295_ = v___x_2288_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v___x_2293_);
v___x_2295_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
return v___x_2295_;
}
}
}
}
v___jp_1841_:
{
if (lean_obj_tag(v___y_1842_) == 0)
{
lean_object* v_a_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1851_; 
v_a_1843_ = lean_ctor_get(v___y_1842_, 0);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___y_1842_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1845_ = v___y_1842_;
v_isShared_1846_ = v_isSharedCheck_1851_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_a_1843_);
lean_dec(v___y_1842_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1851_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1847_; lean_object* v___x_1849_; 
v___x_1847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1847_, 0, v_a_1843_);
if (v_isShared_1846_ == 0)
{
lean_ctor_set(v___x_1845_, 0, v___x_1847_);
v___x_1849_ = v___x_1845_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v___x_1847_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
}
else
{
lean_object* v_a_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1859_; 
v_a_1852_ = lean_ctor_get(v___y_1842_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___y_1842_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1854_ = v___y_1842_;
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_a_1852_);
lean_dec(v___y_1842_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___x_1857_; 
if (v_isShared_1855_ == 0)
{
v___x_1857_ = v___x_1854_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_a_1852_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
}
v___jp_1867_:
{
lean_object* v___x_1873_; double v___x_1874_; double v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; 
v___x_1873_ = lean_io_get_num_heartbeats();
v___x_1874_ = lean_float_of_nat(v___y_1869_);
v___x_1875_ = lean_float_of_nat(v___x_1873_);
v___x_1876_ = lean_box_float(v___x_1874_);
v___x_1877_ = lean_box_float(v___x_1875_);
v___x_1878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1876_);
lean_ctor_set(v___x_1878_, 1, v___x_1877_);
v___x_1879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1879_, 0, v_a_1872_);
lean_ctor_set(v___x_1879_, 1, v___x_1878_);
v___x_1880_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0(v___x_1864_, v___x_1865_, v___x_1866_, v___y_1870_, v___y_1868_, v___y_1871_, v___f_1826_, v___x_1879_, v___y_1838_, v___y_1839_);
v___y_1842_ = v___x_1880_;
goto v___jp_1841_;
}
v___jp_1881_:
{
lean_object* v___x_1887_; double v___x_1888_; double v___x_1889_; double v___x_1890_; double v___x_1891_; double v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1887_ = lean_io_mono_nanos_now();
v___x_1888_ = lean_float_of_nat(v___y_1883_);
v___x_1889_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9);
v___x_1890_ = lean_float_div(v___x_1888_, v___x_1889_);
v___x_1891_ = lean_float_of_nat(v___x_1887_);
v___x_1892_ = lean_float_div(v___x_1891_, v___x_1889_);
v___x_1893_ = lean_box_float(v___x_1890_);
v___x_1894_ = lean_box_float(v___x_1892_);
v___x_1895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1893_);
lean_ctor_set(v___x_1895_, 1, v___x_1894_);
v___x_1896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1896_, 0, v_a_1886_);
lean_ctor_set(v___x_1896_, 1, v___x_1895_);
v___x_1897_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0(v___x_1864_, v___x_1865_, v___x_1866_, v___y_1884_, v___y_1882_, v___y_1885_, v___f_1826_, v___x_1896_, v___y_1838_, v___y_1839_);
v___y_1842_ = v___x_1897_;
goto v___jp_1841_;
}
v___jp_1898_:
{
lean_object* v___x_1901_; lean_object* v_a_1902_; lean_object* v___x_1903_; uint8_t v___x_1904_; 
v___x_1901_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg(v___y_1839_);
v_a_1902_ = lean_ctor_get(v___x_1901_, 0);
lean_inc(v_a_1902_);
lean_dec_ref(v___x_1901_);
v___x_1903_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1904_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v___y_1900_, v___x_1903_);
if (v___x_1904_ == 0)
{
lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1905_ = lean_io_mono_nanos_now();
v___x_1906_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_1827_, v_trimProofs_1828_, v___y_1838_, v___y_1839_);
lean_dec_ref(v_lratPath_1827_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v_a_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1914_; 
v_a_1907_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1909_ = v___x_1906_;
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_a_1907_);
lean_dec(v___x_1906_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1912_; 
if (v_isShared_1910_ == 0)
{
lean_ctor_set_tag(v___x_1909_, 1);
v___x_1912_ = v___x_1909_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_a_1907_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
v___y_1882_ = v___y_1899_;
v___y_1883_ = v___x_1905_;
v___y_1884_ = v___y_1900_;
v___y_1885_ = v_a_1902_;
v_a_1886_ = v___x_1912_;
goto v___jp_1881_;
}
}
}
else
{
lean_object* v_a_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1922_; 
v_a_1915_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1917_ = v___x_1906_;
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_a_1915_);
lean_dec(v___x_1906_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1920_; 
if (v_isShared_1918_ == 0)
{
lean_ctor_set_tag(v___x_1917_, 0);
v___x_1920_ = v___x_1917_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v_a_1915_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
v___y_1882_ = v___y_1899_;
v___y_1883_ = v___x_1905_;
v___y_1884_ = v___y_1900_;
v___y_1885_ = v_a_1902_;
v_a_1886_ = v___x_1920_;
goto v___jp_1881_;
}
}
}
}
else
{
lean_object* v___x_1923_; lean_object* v___x_1924_; 
v___x_1923_ = lean_io_get_num_heartbeats();
v___x_1924_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_1827_, v_trimProofs_1828_, v___y_1838_, v___y_1839_);
lean_dec_ref(v_lratPath_1827_);
if (lean_obj_tag(v___x_1924_) == 0)
{
lean_object* v_a_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1932_; 
v_a_1925_ = lean_ctor_get(v___x_1924_, 0);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1927_ = v___x_1924_;
v_isShared_1928_ = v_isSharedCheck_1932_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_a_1925_);
lean_dec(v___x_1924_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1932_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v___x_1930_; 
if (v_isShared_1928_ == 0)
{
lean_ctor_set_tag(v___x_1927_, 1);
v___x_1930_ = v___x_1927_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v_a_1925_);
v___x_1930_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
v___y_1868_ = v___y_1899_;
v___y_1869_ = v___x_1923_;
v___y_1870_ = v___y_1900_;
v___y_1871_ = v_a_1902_;
v_a_1872_ = v___x_1930_;
goto v___jp_1867_;
}
}
}
else
{
lean_object* v_a_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1940_; 
v_a_1933_ = lean_ctor_get(v___x_1924_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1935_ = v___x_1924_;
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_a_1933_);
lean_dec(v___x_1924_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1938_; 
if (v_isShared_1936_ == 0)
{
lean_ctor_set_tag(v___x_1935_, 0);
v___x_1938_ = v___x_1935_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_a_1933_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
v___y_1868_ = v___y_1899_;
v___y_1869_ = v___x_1923_;
v___y_1870_ = v___y_1900_;
v___y_1871_ = v_a_1902_;
v_a_1872_ = v___x_1938_;
goto v___jp_1867_;
}
}
}
}
}
v___jp_1941_:
{
lean_object* v___x_1944_; uint8_t v___x_1945_; 
v___x_1944_ = l_Lean_trace_profiler;
v___x_1945_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v___y_1942_, v___x_1944_);
if (v___x_1945_ == 0)
{
lean_object* v___x_1946_; 
lean_dec_ref(v___f_1826_);
v___x_1946_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_1827_, v_trimProofs_1828_, v___y_1838_, v___y_1839_);
lean_dec_ref(v_lratPath_1827_);
v___y_1842_ = v___x_1946_;
goto v___jp_1841_;
}
else
{
v___y_1899_ = v_a_1943_;
v___y_1900_ = v___y_1942_;
goto v___jp_1898_;
}
}
v___jp_1947_:
{
if (lean_obj_tag(v___y_1948_) == 0)
{
lean_object* v_a_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1968_; 
v_a_1949_ = lean_ctor_get(v___y_1948_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___y_1948_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1951_ = v___y_1948_;
v_isShared_1952_ = v_isSharedCheck_1968_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_dec(v___y_1948_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1968_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
if (lean_obj_tag(v_a_1949_) == 0)
{
lean_object* v_assignment_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1963_; 
lean_dec_ref(v_lratPath_1827_);
lean_dec_ref(v___f_1826_);
v_assignment_1953_ = lean_ctor_get(v_a_1949_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v_a_1949_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1955_ = v_a_1949_;
v_isShared_1956_ = v_isSharedCheck_1963_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_assignment_1953_);
lean_dec(v_a_1949_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1963_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v___x_1958_; 
if (v_isShared_1956_ == 0)
{
v___x_1958_ = v___x_1955_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_assignment_1953_);
v___x_1958_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
lean_object* v___x_1960_; 
if (v_isShared_1952_ == 0)
{
lean_ctor_set(v___x_1951_, 0, v___x_1958_);
v___x_1960_ = v___x_1951_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v___x_1958_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
return v___x_1960_;
}
}
}
}
else
{
uint8_t v___x_1964_; 
lean_del_object(v___x_1951_);
lean_dec(v_a_1949_);
v___x_1964_ = lean_bool_not(v_hasTrace_1863_);
if (v___x_1964_ == 0)
{
if (v_hasTrace_1863_ == 0)
{
v___y_1942_ = v_options_1860_;
v_a_1943_ = v_hasTrace_1863_;
goto v___jp_1941_;
}
else
{
lean_object* v___x_1965_; uint8_t v___x_1966_; 
v___x_1965_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6);
v___x_1966_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1862_, v_options_1860_, v___x_1965_);
if (v___x_1966_ == 0)
{
v___y_1942_ = v_options_1860_;
v_a_1943_ = v___x_1966_;
goto v___jp_1941_;
}
else
{
v___y_1899_ = v___x_1966_;
v___y_1900_ = v_options_1860_;
goto v___jp_1898_;
}
}
}
else
{
lean_object* v___x_1967_; 
lean_dec_ref(v___f_1826_);
v___x_1967_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_1827_, v_trimProofs_1828_, v___y_1838_, v___y_1839_);
lean_dec_ref(v_lratPath_1827_);
v___y_1842_ = v___x_1967_;
goto v___jp_1841_;
}
}
}
}
else
{
lean_object* v_a_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1976_; 
lean_dec_ref(v_lratPath_1827_);
lean_dec_ref(v___f_1826_);
v_a_1969_ = lean_ctor_get(v___y_1948_, 0);
v_isSharedCheck_1976_ = !lean_is_exclusive(v___y_1948_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1971_ = v___y_1948_;
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_a_1969_);
lean_dec(v___y_1948_);
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
lean_object* v___x_1983_; double v___x_1984_; double v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; 
v___x_1983_ = lean_io_get_num_heartbeats();
v___x_1984_ = lean_float_of_nat(v___y_1979_);
v___x_1985_ = lean_float_of_nat(v___x_1983_);
v___x_1986_ = lean_box_float(v___x_1984_);
v___x_1987_ = lean_box_float(v___x_1985_);
v___x_1988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1986_);
lean_ctor_set(v___x_1988_, 1, v___x_1987_);
v___x_1989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1989_, 0, v_a_1982_);
lean_ctor_set(v___x_1989_, 1, v___x_1988_);
v___x_1990_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1(v___x_1864_, v___x_1865_, v___x_1866_, v___y_1978_, v___y_1981_, v___y_1980_, v___f_1829_, v___x_1989_, v___y_1838_, v___y_1839_);
v___y_1948_ = v___x_1990_;
goto v___jp_1947_;
}
v___jp_1991_:
{
lean_object* v___x_1997_; double v___x_1998_; double v___x_1999_; double v___x_2000_; double v___x_2001_; double v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_1997_ = lean_io_mono_nanos_now();
v___x_1998_ = lean_float_of_nat(v___y_1993_);
v___x_1999_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9);
v___x_2000_ = lean_float_div(v___x_1998_, v___x_1999_);
v___x_2001_ = lean_float_of_nat(v___x_1997_);
v___x_2002_ = lean_float_div(v___x_2001_, v___x_1999_);
v___x_2003_ = lean_box_float(v___x_2000_);
v___x_2004_ = lean_box_float(v___x_2002_);
v___x_2005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2005_, 0, v___x_2003_);
lean_ctor_set(v___x_2005_, 1, v___x_2004_);
v___x_2006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2006_, 0, v_a_1996_);
lean_ctor_set(v___x_2006_, 1, v___x_2005_);
v___x_2007_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1(v___x_1864_, v___x_1865_, v___x_1866_, v___y_1992_, v___y_1995_, v___y_1994_, v___f_1829_, v___x_2006_, v___y_1838_, v___y_1839_);
v___y_1948_ = v___x_2007_;
goto v___jp_1947_;
}
v___jp_2008_:
{
lean_object* v___x_2011_; lean_object* v_a_2012_; lean_object* v___x_2013_; uint8_t v___x_2014_; 
v___x_2011_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg(v___y_1839_);
v_a_2012_ = lean_ctor_get(v___x_2011_, 0);
lean_inc(v_a_2012_);
lean_dec_ref(v___x_2011_);
v___x_2013_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2014_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v___y_2009_, v___x_2013_);
if (v___x_2014_ == 0)
{
lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2015_ = lean_io_mono_nanos_now();
lean_inc_ref(v_lratPath_1827_);
v___x_2016_ = l_Lean_Meta_Tactic_BVDecide_External_satQuery(v_solver_1830_, v_cnfPath_1837_, v_lratPath_1827_, v_timeout_1831_, v_binaryProofs_1832_, v_solverMode_1833_, v___y_1838_, v___y_1839_);
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
v___y_1992_ = v___y_2009_;
v___y_1993_ = v___x_2015_;
v___y_1994_ = v_a_2012_;
v___y_1995_ = v___y_2010_;
v_a_1996_ = v___x_2022_;
goto v___jp_1991_;
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
v___y_1992_ = v___y_2009_;
v___y_1993_ = v___x_2015_;
v___y_1994_ = v_a_2012_;
v___y_1995_ = v___y_2010_;
v_a_1996_ = v___x_2030_;
goto v___jp_1991_;
}
}
}
}
else
{
lean_object* v___x_2033_; lean_object* v___x_2034_; 
v___x_2033_ = lean_io_get_num_heartbeats();
lean_inc_ref(v_lratPath_1827_);
v___x_2034_ = l_Lean_Meta_Tactic_BVDecide_External_satQuery(v_solver_1830_, v_cnfPath_1837_, v_lratPath_1827_, v_timeout_1831_, v_binaryProofs_1832_, v_solverMode_1833_, v___y_1838_, v___y_1839_);
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
v___y_1978_ = v___y_2009_;
v___y_1979_ = v___x_2033_;
v___y_1980_ = v_a_2012_;
v___y_1981_ = v___y_2010_;
v_a_1982_ = v___x_2040_;
goto v___jp_1977_;
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
v___y_1978_ = v___y_2009_;
v___y_1979_ = v___x_2033_;
v___y_1980_ = v_a_2012_;
v___y_1981_ = v___y_2010_;
v_a_1982_ = v___x_2048_;
goto v___jp_1977_;
}
}
}
}
}
v___jp_2051_:
{
lean_object* v___x_2054_; uint8_t v___x_2055_; 
v___x_2054_ = l_Lean_trace_profiler;
v___x_2055_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v___y_2052_, v___x_2054_);
if (v___x_2055_ == 0)
{
lean_object* v___x_2056_; 
lean_dec_ref(v___f_1829_);
lean_inc_ref(v_lratPath_1827_);
v___x_2056_ = l_Lean_Meta_Tactic_BVDecide_External_satQuery(v_solver_1830_, v_cnfPath_1837_, v_lratPath_1827_, v_timeout_1831_, v_binaryProofs_1832_, v_solverMode_1833_, v___y_1838_, v___y_1839_);
v___y_1948_ = v___x_2056_;
goto v___jp_1947_;
}
else
{
v___y_2009_ = v___y_2052_;
v___y_2010_ = v_a_2053_;
goto v___jp_2008_;
}
}
v___jp_2057_:
{
uint8_t v___x_2058_; 
v___x_2058_ = lean_bool_not(v_hasTrace_1863_);
if (v___x_2058_ == 0)
{
if (v_hasTrace_1863_ == 0)
{
v___y_2052_ = v_options_1860_;
v_a_2053_ = v_hasTrace_1863_;
goto v___jp_2051_;
}
else
{
lean_object* v___x_2059_; uint8_t v___x_2060_; 
v___x_2059_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6);
v___x_2060_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1862_, v_options_1860_, v___x_2059_);
if (v___x_2060_ == 0)
{
v___y_2052_ = v_options_1860_;
v_a_2053_ = v___x_2060_;
goto v___jp_2051_;
}
else
{
v___y_2009_ = v_options_1860_;
v___y_2010_ = v___x_2060_;
goto v___jp_2008_;
}
}
}
else
{
lean_object* v___x_2061_; 
lean_dec_ref(v___f_1829_);
lean_inc_ref(v_lratPath_1827_);
v___x_2061_ = l_Lean_Meta_Tactic_BVDecide_External_satQuery(v_solver_1830_, v_cnfPath_1837_, v_lratPath_1827_, v_timeout_1831_, v_binaryProofs_1832_, v_solverMode_1833_, v___y_1838_, v___y_1839_);
v___y_1948_ = v___x_2061_;
goto v___jp_1947_;
}
}
v___jp_2062_:
{
if (lean_obj_tag(v___y_2063_) == 0)
{
lean_dec_ref_known(v___y_2063_, 1);
goto v___jp_2057_;
}
else
{
lean_object* v_a_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2071_; 
lean_dec_ref(v_cnfPath_1837_);
lean_dec_ref(v_solver_1830_);
lean_dec_ref(v___f_1829_);
lean_dec_ref(v_lratPath_1827_);
lean_dec_ref(v___f_1826_);
v_a_2064_ = lean_ctor_get(v___y_2063_, 0);
v_isSharedCheck_2071_ = !lean_is_exclusive(v___y_2063_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2066_ = v___y_2063_;
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_a_2064_);
lean_dec(v___y_2063_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2069_; 
if (v_isShared_2067_ == 0)
{
v___x_2069_ = v___x_2066_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_a_2064_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
}
}
v___jp_2072_:
{
lean_object* v___x_2077_; double v___x_2078_; double v___x_2079_; double v___x_2080_; double v___x_2081_; double v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; 
v___x_2077_ = lean_io_mono_nanos_now();
v___x_2078_ = lean_float_of_nat(v___y_2075_);
v___x_2079_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9, &l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9);
v___x_2080_ = lean_float_div(v___x_2078_, v___x_2079_);
v___x_2081_ = lean_float_of_nat(v___x_2077_);
v___x_2082_ = lean_float_div(v___x_2081_, v___x_2079_);
v___x_2083_ = lean_box_float(v___x_2080_);
v___x_2084_ = lean_box_float(v___x_2082_);
v___x_2085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2083_);
lean_ctor_set(v___x_2085_, 1, v___x_2084_);
v___x_2086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2086_, 0, v_a_2076_);
lean_ctor_set(v___x_2086_, 1, v___x_2085_);
v___x_2087_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2(v___x_1864_, v___x_1865_, v___x_1866_, v_options_1860_, v___y_2073_, v___y_2074_, v___f_1834_, v___x_2086_, v___y_1838_, v___y_1839_);
v___y_2063_ = v___x_2087_;
goto v___jp_2062_;
}
v___jp_2088_:
{
lean_object* v___x_2093_; 
v___x_2093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2093_, 0, v_a_2092_);
v___y_2073_ = v___y_2089_;
v___y_2074_ = v___y_2090_;
v___y_2075_ = v___y_2091_;
v_a_2076_ = v___x_2093_;
goto v___jp_2072_;
}
v___jp_2094_:
{
lean_object* v___x_2099_; double v___x_2100_; double v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___x_2099_ = lean_io_get_num_heartbeats();
v___x_2100_ = lean_float_of_nat(v___y_2097_);
v___x_2101_ = lean_float_of_nat(v___x_2099_);
v___x_2102_ = lean_box_float(v___x_2100_);
v___x_2103_ = lean_box_float(v___x_2101_);
v___x_2104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2104_, 0, v___x_2102_);
lean_ctor_set(v___x_2104_, 1, v___x_2103_);
v___x_2105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2105_, 0, v_a_2098_);
lean_ctor_set(v___x_2105_, 1, v___x_2104_);
v___x_2106_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2(v___x_1864_, v___x_1865_, v___x_1866_, v_options_1860_, v___y_2095_, v___y_2096_, v___f_1834_, v___x_2105_, v___y_1838_, v___y_1839_);
v___y_2063_ = v___x_2106_;
goto v___jp_2062_;
}
v___jp_2107_:
{
lean_object* v___x_2112_; 
v___x_2112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2112_, 0, v_a_2111_);
v___y_2095_ = v___y_2108_;
v___y_2096_ = v___y_2109_;
v___y_2097_ = v___y_2110_;
v_a_2098_ = v___x_2112_;
goto v___jp_2094_;
}
v___jp_2113_:
{
lean_object* v___x_2115_; lean_object* v_a_2116_; lean_object* v___x_2117_; uint8_t v___x_2118_; 
v___x_2115_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg(v___y_1839_);
v_a_2116_ = lean_ctor_get(v___x_2115_, 0);
lean_inc(v_a_2116_);
lean_dec_ref(v___x_2115_);
v___x_2117_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2118_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_options_1860_, v___x_2117_);
if (v___x_2118_ == 0)
{
lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2119_ = lean_io_mono_nanos_now();
v___x_2120_ = l_IO_lazyPure___redArg(v___f_1835_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_object* v_a_2121_; lean_object* v___x_2122_; 
v_a_2121_ = lean_ctor_get(v___x_2120_, 0);
lean_inc(v_a_2121_);
lean_dec_ref_known(v___x_2120_, 1);
v___x_2122_ = lean_io_prim_handle_put_str(v_cnfHandle_1836_, v_a_2121_);
lean_dec(v_a_2121_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v___x_2123_; 
lean_dec_ref_known(v___x_2122_, 1);
v___x_2123_ = lean_io_prim_handle_flush(v_cnfHandle_1836_);
if (lean_obj_tag(v___x_2123_) == 0)
{
lean_object* v_a_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2131_; 
v_a_2124_ = lean_ctor_get(v___x_2123_, 0);
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2126_ = v___x_2123_;
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_a_2124_);
lean_dec(v___x_2123_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___x_2129_; 
if (v_isShared_2127_ == 0)
{
lean_ctor_set_tag(v___x_2126_, 1);
v___x_2129_ = v___x_2126_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_a_2124_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
v___y_2073_ = v___y_2114_;
v___y_2074_ = v_a_2116_;
v___y_2075_ = v___x_2119_;
v_a_2076_ = v___x_2129_;
goto v___jp_2072_;
}
}
}
else
{
lean_object* v_a_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2142_; 
v_a_2132_ = lean_ctor_get(v___x_2123_, 0);
v_isSharedCheck_2142_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2134_ = v___x_2123_;
v_isShared_2135_ = v_isSharedCheck_2142_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_a_2132_);
lean_dec(v___x_2123_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2142_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v___x_2136_; lean_object* v___x_2138_; 
v___x_2136_ = lean_io_error_to_string(v_a_2132_);
if (v_isShared_2135_ == 0)
{
lean_ctor_set_tag(v___x_2134_, 3);
lean_ctor_set(v___x_2134_, 0, v___x_2136_);
v___x_2138_ = v___x_2134_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v___x_2136_);
v___x_2138_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
lean_object* v___x_2139_; lean_object* v___x_2140_; 
v___x_2139_ = l_Lean_MessageData_ofFormat(v___x_2138_);
lean_inc(v_ref_1861_);
v___x_2140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2140_, 0, v_ref_1861_);
lean_ctor_set(v___x_2140_, 1, v___x_2139_);
v___y_2089_ = v___y_2114_;
v___y_2090_ = v_a_2116_;
v___y_2091_ = v___x_2119_;
v_a_2092_ = v___x_2140_;
goto v___jp_2088_;
}
}
}
}
else
{
lean_object* v_a_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2153_; 
v_a_2143_ = lean_ctor_get(v___x_2122_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2145_ = v___x_2122_;
v_isShared_2146_ = v_isSharedCheck_2153_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_a_2143_);
lean_dec(v___x_2122_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2153_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v___x_2147_; lean_object* v___x_2149_; 
v___x_2147_ = lean_io_error_to_string(v_a_2143_);
if (v_isShared_2146_ == 0)
{
lean_ctor_set_tag(v___x_2145_, 3);
lean_ctor_set(v___x_2145_, 0, v___x_2147_);
v___x_2149_ = v___x_2145_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v___x_2147_);
v___x_2149_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
lean_object* v___x_2150_; lean_object* v___x_2151_; 
v___x_2150_ = l_Lean_MessageData_ofFormat(v___x_2149_);
lean_inc(v_ref_1861_);
v___x_2151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2151_, 0, v_ref_1861_);
lean_ctor_set(v___x_2151_, 1, v___x_2150_);
v___y_2089_ = v___y_2114_;
v___y_2090_ = v_a_2116_;
v___y_2091_ = v___x_2119_;
v_a_2092_ = v___x_2151_;
goto v___jp_2088_;
}
}
}
}
else
{
lean_object* v_a_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2164_; 
v_a_2154_ = lean_ctor_get(v___x_2120_, 0);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2156_ = v___x_2120_;
v_isShared_2157_ = v_isSharedCheck_2164_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_dec(v___x_2120_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2164_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2158_; lean_object* v___x_2160_; 
v___x_2158_ = lean_io_error_to_string(v_a_2154_);
if (v_isShared_2157_ == 0)
{
lean_ctor_set_tag(v___x_2156_, 3);
lean_ctor_set(v___x_2156_, 0, v___x_2158_);
v___x_2160_ = v___x_2156_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v___x_2158_);
v___x_2160_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; 
v___x_2161_ = l_Lean_MessageData_ofFormat(v___x_2160_);
lean_inc(v_ref_1861_);
v___x_2162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2162_, 0, v_ref_1861_);
lean_ctor_set(v___x_2162_, 1, v___x_2161_);
v___y_2089_ = v___y_2114_;
v___y_2090_ = v_a_2116_;
v___y_2091_ = v___x_2119_;
v_a_2092_ = v___x_2162_;
goto v___jp_2088_;
}
}
}
}
else
{
lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2165_ = lean_io_get_num_heartbeats();
v___x_2166_ = l_IO_lazyPure___redArg(v___f_1835_);
if (lean_obj_tag(v___x_2166_) == 0)
{
lean_object* v_a_2167_; lean_object* v___x_2168_; 
v_a_2167_ = lean_ctor_get(v___x_2166_, 0);
lean_inc(v_a_2167_);
lean_dec_ref_known(v___x_2166_, 1);
v___x_2168_ = lean_io_prim_handle_put_str(v_cnfHandle_1836_, v_a_2167_);
lean_dec(v_a_2167_);
if (lean_obj_tag(v___x_2168_) == 0)
{
lean_object* v___x_2169_; 
lean_dec_ref_known(v___x_2168_, 1);
v___x_2169_ = lean_io_prim_handle_flush(v_cnfHandle_1836_);
if (lean_obj_tag(v___x_2169_) == 0)
{
lean_object* v_a_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2177_; 
v_a_2170_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2177_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2177_ == 0)
{
v___x_2172_ = v___x_2169_;
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_a_2170_);
lean_dec(v___x_2169_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v___x_2175_; 
if (v_isShared_2173_ == 0)
{
lean_ctor_set_tag(v___x_2172_, 1);
v___x_2175_ = v___x_2172_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v_a_2170_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
v___y_2095_ = v___y_2114_;
v___y_2096_ = v_a_2116_;
v___y_2097_ = v___x_2165_;
v_a_2098_ = v___x_2175_;
goto v___jp_2094_;
}
}
}
else
{
lean_object* v_a_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2188_; 
v_a_2178_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2180_ = v___x_2169_;
v_isShared_2181_ = v_isSharedCheck_2188_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_a_2178_);
lean_dec(v___x_2169_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2188_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
lean_object* v___x_2182_; lean_object* v___x_2184_; 
v___x_2182_ = lean_io_error_to_string(v_a_2178_);
if (v_isShared_2181_ == 0)
{
lean_ctor_set_tag(v___x_2180_, 3);
lean_ctor_set(v___x_2180_, 0, v___x_2182_);
v___x_2184_ = v___x_2180_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v___x_2182_);
v___x_2184_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2185_ = l_Lean_MessageData_ofFormat(v___x_2184_);
lean_inc(v_ref_1861_);
v___x_2186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2186_, 0, v_ref_1861_);
lean_ctor_set(v___x_2186_, 1, v___x_2185_);
v___y_2108_ = v___y_2114_;
v___y_2109_ = v_a_2116_;
v___y_2110_ = v___x_2165_;
v_a_2111_ = v___x_2186_;
goto v___jp_2107_;
}
}
}
}
else
{
lean_object* v_a_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2199_; 
v_a_2189_ = lean_ctor_get(v___x_2168_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2168_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2191_ = v___x_2168_;
v_isShared_2192_ = v_isSharedCheck_2199_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_a_2189_);
lean_dec(v___x_2168_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2199_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2193_; lean_object* v___x_2195_; 
v___x_2193_ = lean_io_error_to_string(v_a_2189_);
if (v_isShared_2192_ == 0)
{
lean_ctor_set_tag(v___x_2191_, 3);
lean_ctor_set(v___x_2191_, 0, v___x_2193_);
v___x_2195_ = v___x_2191_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v___x_2193_);
v___x_2195_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2196_ = l_Lean_MessageData_ofFormat(v___x_2195_);
lean_inc(v_ref_1861_);
v___x_2197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2197_, 0, v_ref_1861_);
lean_ctor_set(v___x_2197_, 1, v___x_2196_);
v___y_2108_ = v___y_2114_;
v___y_2109_ = v_a_2116_;
v___y_2110_ = v___x_2165_;
v_a_2111_ = v___x_2197_;
goto v___jp_2107_;
}
}
}
}
else
{
lean_object* v_a_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2210_; 
v_a_2200_ = lean_ctor_get(v___x_2166_, 0);
v_isSharedCheck_2210_ = !lean_is_exclusive(v___x_2166_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_2202_ = v___x_2166_;
v_isShared_2203_ = v_isSharedCheck_2210_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_a_2200_);
lean_dec(v___x_2166_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2210_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2204_; lean_object* v___x_2206_; 
v___x_2204_ = lean_io_error_to_string(v_a_2200_);
if (v_isShared_2203_ == 0)
{
lean_ctor_set_tag(v___x_2202_, 3);
lean_ctor_set(v___x_2202_, 0, v___x_2204_);
v___x_2206_ = v___x_2202_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v___x_2204_);
v___x_2206_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2207_ = l_Lean_MessageData_ofFormat(v___x_2206_);
lean_inc(v_ref_1861_);
v___x_2208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2208_, 0, v_ref_1861_);
lean_ctor_set(v___x_2208_, 1, v___x_2207_);
v___y_2108_ = v___y_2114_;
v___y_2109_ = v_a_2116_;
v___y_2110_ = v___x_2165_;
v_a_2111_ = v___x_2208_;
goto v___jp_2107_;
}
}
}
}
}
v___jp_2211_:
{
lean_object* v___x_2213_; uint8_t v___x_2214_; 
v___x_2213_ = l_Lean_trace_profiler;
v___x_2214_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_options_1860_, v___x_2213_);
if (v___x_2214_ == 0)
{
lean_object* v___x_2215_; 
lean_dec_ref(v___f_1834_);
v___x_2215_ = l_IO_lazyPure___redArg(v___f_1835_);
if (lean_obj_tag(v___x_2215_) == 0)
{
lean_object* v_a_2216_; lean_object* v___x_2217_; 
v_a_2216_ = lean_ctor_get(v___x_2215_, 0);
lean_inc(v_a_2216_);
lean_dec_ref_known(v___x_2215_, 1);
v___x_2217_ = lean_io_prim_handle_put_str(v_cnfHandle_1836_, v_a_2216_);
lean_dec(v_a_2216_);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_object* v___x_2218_; 
lean_dec_ref_known(v___x_2217_, 1);
v___x_2218_ = lean_io_prim_handle_flush(v_cnfHandle_1836_);
if (lean_obj_tag(v___x_2218_) == 0)
{
lean_dec_ref_known(v___x_2218_, 1);
goto v___jp_2057_;
}
else
{
lean_object* v_a_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2230_; 
lean_dec_ref(v_cnfPath_1837_);
lean_dec_ref(v_solver_1830_);
lean_dec_ref(v___f_1829_);
lean_dec_ref(v_lratPath_1827_);
lean_dec_ref(v___f_1826_);
v_a_2219_ = lean_ctor_get(v___x_2218_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2218_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2221_ = v___x_2218_;
v_isShared_2222_ = v_isSharedCheck_2230_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_a_2219_);
lean_dec(v___x_2218_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2230_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2228_; 
v___x_2223_ = lean_io_error_to_string(v_a_2219_);
v___x_2224_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2224_, 0, v___x_2223_);
v___x_2225_ = l_Lean_MessageData_ofFormat(v___x_2224_);
lean_inc(v_ref_1861_);
v___x_2226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2226_, 0, v_ref_1861_);
lean_ctor_set(v___x_2226_, 1, v___x_2225_);
if (v_isShared_2222_ == 0)
{
lean_ctor_set(v___x_2221_, 0, v___x_2226_);
v___x_2228_ = v___x_2221_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v___x_2226_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
}
}
else
{
lean_object* v_a_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2242_; 
lean_dec_ref(v_cnfPath_1837_);
lean_dec_ref(v_solver_1830_);
lean_dec_ref(v___f_1829_);
lean_dec_ref(v_lratPath_1827_);
lean_dec_ref(v___f_1826_);
v_a_2231_ = lean_ctor_get(v___x_2217_, 0);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___x_2217_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2233_ = v___x_2217_;
v_isShared_2234_ = v_isSharedCheck_2242_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_a_2231_);
lean_dec(v___x_2217_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2242_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2240_; 
v___x_2235_ = lean_io_error_to_string(v_a_2231_);
v___x_2236_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2236_, 0, v___x_2235_);
v___x_2237_ = l_Lean_MessageData_ofFormat(v___x_2236_);
lean_inc(v_ref_1861_);
v___x_2238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2238_, 0, v_ref_1861_);
lean_ctor_set(v___x_2238_, 1, v___x_2237_);
if (v_isShared_2234_ == 0)
{
lean_ctor_set(v___x_2233_, 0, v___x_2238_);
v___x_2240_ = v___x_2233_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v___x_2238_);
v___x_2240_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
return v___x_2240_;
}
}
}
}
else
{
lean_object* v_a_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2254_; 
lean_dec_ref(v_cnfPath_1837_);
lean_dec_ref(v_solver_1830_);
lean_dec_ref(v___f_1829_);
lean_dec_ref(v_lratPath_1827_);
lean_dec_ref(v___f_1826_);
v_a_2243_ = lean_ctor_get(v___x_2215_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2215_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2245_ = v___x_2215_;
v_isShared_2246_ = v_isSharedCheck_2254_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_a_2243_);
lean_dec(v___x_2215_);
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
lean_inc(v_ref_1861_);
v___x_2250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2250_, 0, v_ref_1861_);
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
v___y_2114_ = v_a_2212_;
goto v___jp_2113_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___lam__4___boxed(lean_object* v___f_2298_, lean_object* v_lratPath_2299_, lean_object* v_trimProofs_2300_, lean_object* v___f_2301_, lean_object* v_solver_2302_, lean_object* v_timeout_2303_, lean_object* v_binaryProofs_2304_, lean_object* v_solverMode_2305_, lean_object* v___f_2306_, lean_object* v___f_2307_, lean_object* v_cnfHandle_2308_, lean_object* v_cnfPath_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_){
_start:
{
uint8_t v_trimProofs_boxed_2313_; uint8_t v_binaryProofs_boxed_2314_; uint8_t v_solverMode_boxed_2315_; lean_object* v_res_2316_; 
v_trimProofs_boxed_2313_ = lean_unbox(v_trimProofs_2300_);
v_binaryProofs_boxed_2314_ = lean_unbox(v_binaryProofs_2304_);
v_solverMode_boxed_2315_ = lean_unbox(v_solverMode_2305_);
v_res_2316_ = l_Lean_Meta_Tactic_BVDecide_runExternal___lam__4(v___f_2298_, v_lratPath_2299_, v_trimProofs_boxed_2313_, v___f_2301_, v_solver_2302_, v_timeout_2303_, v_binaryProofs_boxed_2314_, v_solverMode_boxed_2315_, v___f_2306_, v___f_2307_, v_cnfHandle_2308_, v_cnfPath_2309_, v___y_2310_, v___y_2311_);
lean_dec(v___y_2311_);
lean_dec_ref(v___y_2310_);
lean_dec(v_cnfHandle_2308_);
lean_dec(v_timeout_2303_);
return v_res_2316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal(lean_object* v_cnf_2320_, lean_object* v_solver_2321_, lean_object* v_lratPath_2322_, uint8_t v_trimProofs_2323_, lean_object* v_timeout_2324_, uint8_t v_binaryProofs_2325_, uint8_t v_solverMode_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_){
_start:
{
lean_object* v___f_2330_; lean_object* v___f_2331_; lean_object* v___f_2332_; lean_object* v___f_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___f_2337_; lean_object* v___x_2338_; 
v___f_2330_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_runExternal___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2330_, 0, v_cnf_2320_);
v___f_2331_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_runExternal___closed__0));
v___f_2332_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_runExternal___closed__1));
v___f_2333_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_runExternal___closed__2));
v___x_2334_ = lean_box(v_trimProofs_2323_);
v___x_2335_ = lean_box(v_binaryProofs_2325_);
v___x_2336_ = lean_box(v_solverMode_2326_);
v___f_2337_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_runExternal___lam__4___boxed), 15, 10);
lean_closure_set(v___f_2337_, 0, v___f_2332_);
lean_closure_set(v___f_2337_, 1, v_lratPath_2322_);
lean_closure_set(v___f_2337_, 2, v___x_2334_);
lean_closure_set(v___f_2337_, 3, v___f_2331_);
lean_closure_set(v___f_2337_, 4, v_solver_2321_);
lean_closure_set(v___f_2337_, 5, v_timeout_2324_);
lean_closure_set(v___f_2337_, 6, v___x_2335_);
lean_closure_set(v___f_2337_, 7, v___x_2336_);
lean_closure_set(v___f_2337_, 8, v___f_2333_);
lean_closure_set(v___f_2337_, 9, v___f_2330_);
v___x_2338_ = l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg(v___f_2337_, v_a_2327_, v_a_2328_);
return v___x_2338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal___boxed(lean_object* v_cnf_2339_, lean_object* v_solver_2340_, lean_object* v_lratPath_2341_, lean_object* v_trimProofs_2342_, lean_object* v_timeout_2343_, lean_object* v_binaryProofs_2344_, lean_object* v_solverMode_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_){
_start:
{
uint8_t v_trimProofs_boxed_2349_; uint8_t v_binaryProofs_boxed_2350_; uint8_t v_solverMode_boxed_2351_; lean_object* v_res_2352_; 
v_trimProofs_boxed_2349_ = lean_unbox(v_trimProofs_2342_);
v_binaryProofs_boxed_2350_ = lean_unbox(v_binaryProofs_2344_);
v_solverMode_boxed_2351_ = lean_unbox(v_solverMode_2345_);
v_res_2352_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_cnf_2339_, v_solver_2340_, v_lratPath_2341_, v_trimProofs_boxed_2349_, v_timeout_2343_, v_binaryProofs_boxed_2350_, v_solverMode_boxed_2351_, v_a_2346_, v_a_2347_);
lean_dec(v_a_2347_);
lean_dec_ref(v_a_2346_);
return v_res_2352_;
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
