// Lean compiler output
// Module: Lean.Meta.Order
// Imports: public import Lean.Meta.PProdN public import Lean.Meta.AppBuilder public import Init.Internal.Order.Basic
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppOptM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Meta_PProdN_genMk___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkInstPiOfInstForall___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_mkInstPiOfInstForall___closed__0 = (const lean_object*)&l_Lean_Meta_mkInstPiOfInstForall___closed__0_value;
static const lean_string_object l_Lean_Meta_mkInstPiOfInstForall___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Order"};
static const lean_object* l_Lean_Meta_mkInstPiOfInstForall___closed__1 = (const lean_object*)&l_Lean_Meta_mkInstPiOfInstForall___closed__1_value;
static const lean_string_object l_Lean_Meta_mkInstPiOfInstForall___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "CCPO"};
static const lean_object* l_Lean_Meta_mkInstPiOfInstForall___closed__2 = (const lean_object*)&l_Lean_Meta_mkInstPiOfInstForall___closed__2_value;
static const lean_ctor_object l_Lean_Meta_mkInstPiOfInstForall___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkInstPiOfInstForall___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_mkInstPiOfInstForall___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkInstPiOfInstForall___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_mkInstPiOfInstForall___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Meta_mkInstPiOfInstForall___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkInstPiOfInstForall___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_mkInstPiOfInstForall___closed__2_value),LEAN_SCALAR_PTR_LITERAL(19, 35, 8, 63, 189, 207, 68, 204)}};
static const lean_object* l_Lean_Meta_mkInstPiOfInstForall___closed__3 = (const lean_object*)&l_Lean_Meta_mkInstPiOfInstForall___closed__3_value;
static const lean_string_object l_Lean_Meta_mkInstPiOfInstForall___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "CompleteLattice"};
static const lean_object* l_Lean_Meta_mkInstPiOfInstForall___closed__4 = (const lean_object*)&l_Lean_Meta_mkInstPiOfInstForall___closed__4_value;
static const lean_ctor_object l_Lean_Meta_mkInstPiOfInstForall___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkInstPiOfInstForall___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_mkInstPiOfInstForall___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkInstPiOfInstForall___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_mkInstPiOfInstForall___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Meta_mkInstPiOfInstForall___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkInstPiOfInstForall___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_mkInstPiOfInstForall___closed__4_value),LEAN_SCALAR_PTR_LITERAL(239, 140, 127, 117, 148, 144, 166, 107)}};
static const lean_object* l_Lean_Meta_mkInstPiOfInstForall___closed__5 = (const lean_object*)&l_Lean_Meta_mkInstPiOfInstForall___closed__5_value;
static const lean_string_object l_Lean_Meta_mkInstPiOfInstForall___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "mkInstPiOfInstForall: unexpected type of "};
static const lean_object* l_Lean_Meta_mkInstPiOfInstForall___closed__6 = (const lean_object*)&l_Lean_Meta_mkInstPiOfInstForall___closed__6_value;
static lean_once_cell_t l_Lean_Meta_mkInstPiOfInstForall___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkInstPiOfInstForall___closed__7;
static const lean_string_object l_Lean_Meta_mkInstPiOfInstForall___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "instCompleteLatticePi"};
static const lean_object* l_Lean_Meta_mkInstPiOfInstForall___closed__8 = (const lean_object*)&l_Lean_Meta_mkInstPiOfInstForall___closed__8_value;
static const lean_ctor_object l_Lean_Meta_mkInstPiOfInstForall___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkInstPiOfInstForall___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_mkInstPiOfInstForall___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkInstPiOfInstForall___closed__9_value_aux_0),((lean_object*)&l_Lean_Meta_mkInstPiOfInstForall___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Meta_mkInstPiOfInstForall___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkInstPiOfInstForall___closed__9_value_aux_1),((lean_object*)&l_Lean_Meta_mkInstPiOfInstForall___closed__8_value),LEAN_SCALAR_PTR_LITERAL(216, 67, 57, 247, 147, 127, 99, 32)}};
static const lean_object* l_Lean_Meta_mkInstPiOfInstForall___closed__9 = (const lean_object*)&l_Lean_Meta_mkInstPiOfInstForall___closed__9_value;
static const lean_string_object l_Lean_Meta_mkInstPiOfInstForall___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instCCPOPi"};
static const lean_object* l_Lean_Meta_mkInstPiOfInstForall___closed__10 = (const lean_object*)&l_Lean_Meta_mkInstPiOfInstForall___closed__10_value;
static const lean_ctor_object l_Lean_Meta_mkInstPiOfInstForall___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkInstPiOfInstForall___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_mkInstPiOfInstForall___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkInstPiOfInstForall___closed__11_value_aux_0),((lean_object*)&l_Lean_Meta_mkInstPiOfInstForall___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Meta_mkInstPiOfInstForall___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkInstPiOfInstForall___closed__11_value_aux_1),((lean_object*)&l_Lean_Meta_mkInstPiOfInstForall___closed__10_value),LEAN_SCALAR_PTR_LITERAL(202, 4, 22, 67, 25, 201, 243, 223)}};
static const lean_object* l_Lean_Meta_mkInstPiOfInstForall___closed__11 = (const lean_object*)&l_Lean_Meta_mkInstPiOfInstForall___closed__11_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkInstPiOfInstForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkInstPiOfInstForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkInstPiOfInstsForall_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkInstPiOfInstsForall_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkInstPiOfInstsForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkInstPiOfInstsForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkFixOfMonFun___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "mkFixOfMonFun: unexpected type of "};
static const lean_object* l_Lean_Meta_mkFixOfMonFun___closed__0 = (const lean_object*)&l_Lean_Meta_mkFixOfMonFun___closed__0_value;
static lean_once_cell_t l_Lean_Meta_mkFixOfMonFun___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkFixOfMonFun___closed__1;
static const lean_string_object l_Lean_Meta_mkFixOfMonFun___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "lfp_monotone"};
static const lean_object* l_Lean_Meta_mkFixOfMonFun___closed__2 = (const lean_object*)&l_Lean_Meta_mkFixOfMonFun___closed__2_value;
static const lean_ctor_object l_Lean_Meta_mkFixOfMonFun___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkInstPiOfInstForall___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_mkFixOfMonFun___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkFixOfMonFun___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_mkInstPiOfInstForall___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Meta_mkFixOfMonFun___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkFixOfMonFun___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_mkFixOfMonFun___closed__2_value),LEAN_SCALAR_PTR_LITERAL(226, 115, 213, 20, 156, 86, 56, 31)}};
static const lean_object* l_Lean_Meta_mkFixOfMonFun___closed__3 = (const lean_object*)&l_Lean_Meta_mkFixOfMonFun___closed__3_value;
static const lean_string_object l_Lean_Meta_mkFixOfMonFun___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fix"};
static const lean_object* l_Lean_Meta_mkFixOfMonFun___closed__4 = (const lean_object*)&l_Lean_Meta_mkFixOfMonFun___closed__4_value;
static const lean_ctor_object l_Lean_Meta_mkFixOfMonFun___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkInstPiOfInstForall___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_mkFixOfMonFun___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkFixOfMonFun___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_mkInstPiOfInstForall___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Meta_mkFixOfMonFun___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkFixOfMonFun___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_mkFixOfMonFun___closed__4_value),LEAN_SCALAR_PTR_LITERAL(18, 104, 23, 57, 110, 104, 99, 16)}};
static const lean_object* l_Lean_Meta_mkFixOfMonFun___closed__5 = (const lean_object*)&l_Lean_Meta_mkFixOfMonFun___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkFixOfMonFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkFixOfMonFun___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_toPartialOrder___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "getUnderlyingOrder: unexpected type of "};
static const lean_object* l_Lean_Meta_toPartialOrder___closed__0 = (const lean_object*)&l_Lean_Meta_toPartialOrder___closed__0_value;
static lean_once_cell_t l_Lean_Meta_toPartialOrder___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_toPartialOrder___closed__1;
static const lean_string_object l_Lean_Meta_toPartialOrder___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "toPartialOrder"};
static const lean_object* l_Lean_Meta_toPartialOrder___closed__2 = (const lean_object*)&l_Lean_Meta_toPartialOrder___closed__2_value;
static const lean_ctor_object l_Lean_Meta_toPartialOrder___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkInstPiOfInstForall___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_toPartialOrder___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_toPartialOrder___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_mkInstPiOfInstForall___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Meta_toPartialOrder___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_toPartialOrder___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_mkInstPiOfInstForall___closed__4_value),LEAN_SCALAR_PTR_LITERAL(239, 140, 127, 117, 148, 144, 166, 107)}};
static const lean_ctor_object l_Lean_Meta_toPartialOrder___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_toPartialOrder___closed__3_value_aux_2),((lean_object*)&l_Lean_Meta_toPartialOrder___closed__2_value),LEAN_SCALAR_PTR_LITERAL(13, 4, 43, 255, 98, 225, 163, 244)}};
static const lean_object* l_Lean_Meta_toPartialOrder___closed__3 = (const lean_object*)&l_Lean_Meta_toPartialOrder___closed__3_value;
static const lean_ctor_object l_Lean_Meta_toPartialOrder___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkInstPiOfInstForall___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_toPartialOrder___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_toPartialOrder___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_mkInstPiOfInstForall___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Meta_toPartialOrder___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_toPartialOrder___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_mkInstPiOfInstForall___closed__2_value),LEAN_SCALAR_PTR_LITERAL(19, 35, 8, 63, 189, 207, 68, 204)}};
static const lean_ctor_object l_Lean_Meta_toPartialOrder___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_toPartialOrder___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_toPartialOrder___closed__2_value),LEAN_SCALAR_PTR_LITERAL(201, 24, 213, 158, 62, 23, 165, 45)}};
static const lean_object* l_Lean_Meta_toPartialOrder___closed__4 = (const lean_object*)&l_Lean_Meta_toPartialOrder___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Meta_toPartialOrder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_toPartialOrder___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkInstCCPOPProd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "instCCPOPProd"};
static const lean_object* l_Lean_Meta_mkInstCCPOPProd___closed__0 = (const lean_object*)&l_Lean_Meta_mkInstCCPOPProd___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkInstCCPOPProd___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkInstPiOfInstForall___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_mkInstCCPOPProd___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkInstCCPOPProd___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_mkInstPiOfInstForall___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Meta_mkInstCCPOPProd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkInstCCPOPProd___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_mkInstCCPOPProd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(193, 223, 146, 139, 208, 109, 106, 240)}};
static const lean_object* l_Lean_Meta_mkInstCCPOPProd___closed__1 = (const lean_object*)&l_Lean_Meta_mkInstCCPOPProd___closed__1_value;
static lean_once_cell_t l_Lean_Meta_mkInstCCPOPProd___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkInstCCPOPProd___closed__2;
static lean_once_cell_t l_Lean_Meta_mkInstCCPOPProd___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkInstCCPOPProd___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_mkInstCCPOPProd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkInstCCPOPProd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkInstCompleteLatticePProd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "instCompleteLatticePProd"};
static const lean_object* l_Lean_Meta_mkInstCompleteLatticePProd___closed__0 = (const lean_object*)&l_Lean_Meta_mkInstCompleteLatticePProd___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkInstCompleteLatticePProd___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkInstPiOfInstForall___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_mkInstCompleteLatticePProd___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkInstCompleteLatticePProd___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_mkInstPiOfInstForall___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Meta_mkInstCompleteLatticePProd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkInstCompleteLatticePProd___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_mkInstCompleteLatticePProd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(244, 129, 138, 58, 147, 185, 15, 195)}};
static const lean_object* l_Lean_Meta_mkInstCompleteLatticePProd___closed__1 = (const lean_object*)&l_Lean_Meta_mkInstCompleteLatticePProd___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkInstCompleteLatticePProd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkInstCompleteLatticePProd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_mkPackedPPRodInstance_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkPackedPPRodInstance_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkPackedPPRodInstance_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkPackedPPRodInstance_spec__1(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkPackedPPRodInstance_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkPackedPPRodInstance_spec__2(uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkPackedPPRodInstance_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_mkPackedPPRodInstance___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_mkInstCompleteLatticePProd___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_mkPackedPPRodInstance___closed__0 = (const lean_object*)&l_Lean_Meta_mkPackedPPRodInstance___closed__0_value;
static const lean_closure_object l_Lean_Meta_mkPackedPPRodInstance___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_mkInstCCPOPProd___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_mkPackedPPRodInstance___closed__1 = (const lean_object*)&l_Lean_Meta_mkPackedPPRodInstance___closed__1_value;
static const lean_string_object l_Lean_Meta_mkPackedPPRodInstance___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "mkPackedPPRoodInstance: unexpected types "};
static const lean_object* l_Lean_Meta_mkPackedPPRodInstance___closed__2 = (const lean_object*)&l_Lean_Meta_mkPackedPPRodInstance___closed__2_value;
static lean_once_cell_t l_Lean_Meta_mkPackedPPRodInstance___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkPackedPPRodInstance___closed__3;
static const lean_string_object l_Lean_Meta_mkPackedPPRodInstance___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l_Lean_Meta_mkPackedPPRodInstance___closed__4 = (const lean_object*)&l_Lean_Meta_mkPackedPPRodInstance___closed__4_value;
static lean_once_cell_t l_Lean_Meta_mkPackedPPRodInstance___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkPackedPPRodInstance___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_mkPackedPPRodInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkPackedPPRodInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0_spec__0(lean_object* v_msgData_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_){
_start:
{
lean_object* v___x_7_; lean_object* v_env_8_; lean_object* v___x_9_; lean_object* v_mctx_10_; lean_object* v_lctx_11_; lean_object* v_options_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_7_ = lean_st_ref_get(v___y_5_);
v_env_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc_ref(v_env_8_);
lean_dec(v___x_7_);
v___x_9_ = lean_st_ref_get(v___y_3_);
v_mctx_10_ = lean_ctor_get(v___x_9_, 0);
lean_inc_ref(v_mctx_10_);
lean_dec(v___x_9_);
v_lctx_11_ = lean_ctor_get(v___y_2_, 2);
v_options_12_ = lean_ctor_get(v___y_4_, 2);
lean_inc_ref(v_options_12_);
lean_inc_ref(v_lctx_11_);
v___x_13_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_13_, 0, v_env_8_);
lean_ctor_set(v___x_13_, 1, v_mctx_10_);
lean_ctor_set(v___x_13_, 2, v_lctx_11_);
lean_ctor_set(v___x_13_, 3, v_options_12_);
v___x_14_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_14_, 0, v___x_13_);
lean_ctor_set(v___x_14_, 1, v_msgData_1_);
v___x_15_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0_spec__0___boxed(lean_object* v_msgData_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0_spec__0(v_msgData_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_);
lean_dec(v___y_20_);
lean_dec_ref(v___y_19_);
lean_dec(v___y_18_);
lean_dec_ref(v___y_17_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0___redArg(lean_object* v_msg_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_){
_start:
{
lean_object* v_ref_29_; lean_object* v___x_30_; lean_object* v_a_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_39_; 
v_ref_29_ = lean_ctor_get(v___y_26_, 5);
v___x_30_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0_spec__0(v_msg_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_);
v_a_31_ = lean_ctor_get(v___x_30_, 0);
v_isSharedCheck_39_ = !lean_is_exclusive(v___x_30_);
if (v_isSharedCheck_39_ == 0)
{
v___x_33_ = v___x_30_;
v_isShared_34_ = v_isSharedCheck_39_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_a_31_);
lean_dec(v___x_30_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_39_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v___x_35_; lean_object* v___x_37_; 
lean_inc(v_ref_29_);
v___x_35_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_35_, 0, v_ref_29_);
lean_ctor_set(v___x_35_, 1, v_a_31_);
if (v_isShared_34_ == 0)
{
lean_ctor_set_tag(v___x_33_, 1);
lean_ctor_set(v___x_33_, 0, v___x_35_);
v___x_37_ = v___x_33_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v___x_35_);
v___x_37_ = v_reuseFailAlloc_38_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
return v___x_37_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0___redArg___boxed(lean_object* v_msg_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0___redArg(v_msg_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_);
lean_dec(v___y_44_);
lean_dec_ref(v___y_43_);
lean_dec(v___y_42_);
lean_dec_ref(v___y_41_);
return v_res_46_;
}
}
static lean_object* _init_l_Lean_Meta_mkInstPiOfInstForall___closed__7(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_60_ = ((lean_object*)(l_Lean_Meta_mkInstPiOfInstForall___closed__6));
v___x_61_ = l_Lean_stringToMessageData(v___x_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInstPiOfInstForall(lean_object* v_x_72_, lean_object* v_inst_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_){
_start:
{
lean_object* v___x_79_; 
lean_inc(v_a_77_);
lean_inc_ref(v_a_76_);
lean_inc(v_a_75_);
lean_inc_ref(v_a_74_);
lean_inc_ref(v_inst_73_);
v___x_79_ = lean_infer_type(v_inst_73_, v_a_74_, v_a_75_, v_a_76_, v_a_77_);
if (lean_obj_tag(v___x_79_) == 0)
{
lean_object* v_a_80_; lean_object* v___x_81_; uint8_t v___x_82_; uint8_t v___x_83_; 
v_a_80_ = lean_ctor_get(v___x_79_, 0);
lean_inc(v_a_80_);
lean_dec_ref(v___x_79_);
v___x_81_ = ((lean_object*)(l_Lean_Meta_mkInstPiOfInstForall___closed__3));
v___x_82_ = l_Lean_Expr_isAppOf(v_a_80_, v___x_81_);
lean_dec(v_a_80_);
v___x_83_ = 1;
if (v___x_82_ == 0)
{
lean_object* v___x_84_; 
lean_inc(v_a_77_);
lean_inc_ref(v_a_76_);
lean_inc(v_a_75_);
lean_inc_ref(v_a_74_);
lean_inc_ref(v_inst_73_);
v___x_84_ = lean_infer_type(v_inst_73_, v_a_74_, v_a_75_, v_a_76_, v_a_77_);
if (lean_obj_tag(v___x_84_) == 0)
{
lean_object* v_a_85_; lean_object* v___x_86_; uint8_t v___x_87_; 
v_a_85_ = lean_ctor_get(v___x_84_, 0);
lean_inc(v_a_85_);
lean_dec_ref(v___x_84_);
v___x_86_ = ((lean_object*)(l_Lean_Meta_mkInstPiOfInstForall___closed__5));
v___x_87_ = l_Lean_Expr_isAppOf(v_a_85_, v___x_86_);
lean_dec(v_a_85_);
if (v___x_87_ == 0)
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
lean_dec_ref(v_x_72_);
v___x_88_ = lean_obj_once(&l_Lean_Meta_mkInstPiOfInstForall___closed__7, &l_Lean_Meta_mkInstPiOfInstForall___closed__7_once, _init_l_Lean_Meta_mkInstPiOfInstForall___closed__7);
v___x_89_ = l_Lean_MessageData_ofExpr(v_inst_73_);
v___x_90_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_90_, 0, v___x_88_);
lean_ctor_set(v___x_90_, 1, v___x_89_);
v___x_91_ = l_Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0___redArg(v___x_90_, v_a_74_, v_a_75_, v_a_76_, v_a_77_);
lean_dec(v_a_77_);
lean_dec_ref(v_a_76_);
lean_dec(v_a_75_);
lean_dec_ref(v_a_74_);
return v___x_91_;
}
else
{
lean_object* v___x_92_; 
lean_inc(v_a_77_);
lean_inc_ref(v_a_76_);
lean_inc(v_a_75_);
lean_inc_ref(v_a_74_);
lean_inc_ref(v_x_72_);
v___x_92_ = lean_infer_type(v_x_72_, v_a_74_, v_a_75_, v_a_76_, v_a_77_);
if (lean_obj_tag(v___x_92_) == 0)
{
lean_object* v_a_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_121_; 
v_a_93_ = lean_ctor_get(v___x_92_, 0);
v_isSharedCheck_121_ = !lean_is_exclusive(v___x_92_);
if (v_isSharedCheck_121_ == 0)
{
v___x_95_ = v___x_92_;
v_isShared_96_ = v_isSharedCheck_121_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_a_93_);
lean_dec(v___x_92_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_121_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; uint8_t v___x_100_; lean_object* v___x_101_; 
v___x_97_ = lean_unsigned_to_nat(1u);
v___x_98_ = lean_mk_empty_array_with_capacity(v___x_97_);
v___x_99_ = lean_array_push(v___x_98_, v_x_72_);
v___x_100_ = 1;
v___x_101_ = l_Lean_Meta_mkLambdaFVars(v___x_99_, v_inst_73_, v___x_82_, v___x_83_, v___x_82_, v___x_83_, v___x_100_, v_a_74_, v_a_75_, v_a_76_, v_a_77_);
lean_dec_ref(v___x_99_);
if (lean_obj_tag(v___x_101_) == 0)
{
lean_object* v_a_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_120_; 
v_a_102_ = lean_ctor_get(v___x_101_, 0);
v_isSharedCheck_120_ = !lean_is_exclusive(v___x_101_);
if (v_isSharedCheck_120_ == 0)
{
v___x_104_ = v___x_101_;
v_isShared_105_ = v_isSharedCheck_120_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_a_102_);
lean_dec(v___x_101_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_120_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_106_; lean_object* v___x_108_; 
v___x_106_ = ((lean_object*)(l_Lean_Meta_mkInstPiOfInstForall___closed__9));
if (v_isShared_105_ == 0)
{
lean_ctor_set_tag(v___x_104_, 1);
lean_ctor_set(v___x_104_, 0, v_a_93_);
v___x_108_ = v___x_104_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v_a_93_);
v___x_108_ = v_reuseFailAlloc_119_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
lean_object* v___x_109_; lean_object* v___x_111_; 
v___x_109_ = lean_box(0);
if (v_isShared_96_ == 0)
{
lean_ctor_set_tag(v___x_95_, 1);
lean_ctor_set(v___x_95_, 0, v_a_102_);
v___x_111_ = v___x_95_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v_a_102_);
v___x_111_ = v_reuseFailAlloc_118_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_112_ = lean_unsigned_to_nat(3u);
v___x_113_ = lean_mk_empty_array_with_capacity(v___x_112_);
v___x_114_ = lean_array_push(v___x_113_, v___x_108_);
v___x_115_ = lean_array_push(v___x_114_, v___x_109_);
v___x_116_ = lean_array_push(v___x_115_, v___x_111_);
v___x_117_ = l_Lean_Meta_mkAppOptM(v___x_106_, v___x_116_, v_a_74_, v_a_75_, v_a_76_, v_a_77_);
return v___x_117_;
}
}
}
}
else
{
lean_del_object(v___x_95_);
lean_dec(v_a_93_);
lean_dec(v_a_77_);
lean_dec_ref(v_a_76_);
lean_dec(v_a_75_);
lean_dec_ref(v_a_74_);
return v___x_101_;
}
}
}
else
{
lean_dec(v_a_77_);
lean_dec_ref(v_a_76_);
lean_dec(v_a_75_);
lean_dec_ref(v_a_74_);
lean_dec_ref(v_inst_73_);
lean_dec_ref(v_x_72_);
return v___x_92_;
}
}
}
else
{
lean_dec(v_a_77_);
lean_dec_ref(v_a_76_);
lean_dec(v_a_75_);
lean_dec_ref(v_a_74_);
lean_dec_ref(v_inst_73_);
lean_dec_ref(v_x_72_);
return v___x_84_;
}
}
else
{
lean_object* v___x_122_; 
lean_inc(v_a_77_);
lean_inc_ref(v_a_76_);
lean_inc(v_a_75_);
lean_inc_ref(v_a_74_);
lean_inc_ref(v_x_72_);
v___x_122_ = lean_infer_type(v_x_72_, v_a_74_, v_a_75_, v_a_76_, v_a_77_);
if (lean_obj_tag(v___x_122_) == 0)
{
lean_object* v_a_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_152_; 
v_a_123_ = lean_ctor_get(v___x_122_, 0);
v_isSharedCheck_152_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_152_ == 0)
{
v___x_125_ = v___x_122_;
v_isShared_126_ = v_isSharedCheck_152_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_a_123_);
lean_dec(v___x_122_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_152_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; uint8_t v___x_130_; uint8_t v___x_131_; lean_object* v___x_132_; 
v___x_127_ = lean_unsigned_to_nat(1u);
v___x_128_ = lean_mk_empty_array_with_capacity(v___x_127_);
v___x_129_ = lean_array_push(v___x_128_, v_x_72_);
v___x_130_ = 0;
v___x_131_ = 1;
v___x_132_ = l_Lean_Meta_mkLambdaFVars(v___x_129_, v_inst_73_, v___x_130_, v___x_83_, v___x_130_, v___x_83_, v___x_131_, v_a_74_, v_a_75_, v_a_76_, v_a_77_);
lean_dec_ref(v___x_129_);
if (lean_obj_tag(v___x_132_) == 0)
{
lean_object* v_a_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_151_; 
v_a_133_ = lean_ctor_get(v___x_132_, 0);
v_isSharedCheck_151_ = !lean_is_exclusive(v___x_132_);
if (v_isSharedCheck_151_ == 0)
{
v___x_135_ = v___x_132_;
v_isShared_136_ = v_isSharedCheck_151_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_a_133_);
lean_dec(v___x_132_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_151_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v___x_137_; lean_object* v___x_139_; 
v___x_137_ = ((lean_object*)(l_Lean_Meta_mkInstPiOfInstForall___closed__11));
if (v_isShared_136_ == 0)
{
lean_ctor_set_tag(v___x_135_, 1);
lean_ctor_set(v___x_135_, 0, v_a_123_);
v___x_139_ = v___x_135_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v_a_123_);
v___x_139_ = v_reuseFailAlloc_150_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
lean_object* v___x_140_; lean_object* v___x_142_; 
v___x_140_ = lean_box(0);
if (v_isShared_126_ == 0)
{
lean_ctor_set_tag(v___x_125_, 1);
lean_ctor_set(v___x_125_, 0, v_a_133_);
v___x_142_ = v___x_125_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v_a_133_);
v___x_142_ = v_reuseFailAlloc_149_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_143_ = lean_unsigned_to_nat(3u);
v___x_144_ = lean_mk_empty_array_with_capacity(v___x_143_);
v___x_145_ = lean_array_push(v___x_144_, v___x_139_);
v___x_146_ = lean_array_push(v___x_145_, v___x_140_);
v___x_147_ = lean_array_push(v___x_146_, v___x_142_);
v___x_148_ = l_Lean_Meta_mkAppOptM(v___x_137_, v___x_147_, v_a_74_, v_a_75_, v_a_76_, v_a_77_);
return v___x_148_;
}
}
}
}
else
{
lean_del_object(v___x_125_);
lean_dec(v_a_123_);
lean_dec(v_a_77_);
lean_dec_ref(v_a_76_);
lean_dec(v_a_75_);
lean_dec_ref(v_a_74_);
return v___x_132_;
}
}
}
else
{
lean_dec(v_a_77_);
lean_dec_ref(v_a_76_);
lean_dec(v_a_75_);
lean_dec_ref(v_a_74_);
lean_dec_ref(v_inst_73_);
lean_dec_ref(v_x_72_);
return v___x_122_;
}
}
}
else
{
lean_dec(v_a_77_);
lean_dec_ref(v_a_76_);
lean_dec(v_a_75_);
lean_dec_ref(v_a_74_);
lean_dec_ref(v_inst_73_);
lean_dec_ref(v_x_72_);
return v___x_79_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInstPiOfInstForall___boxed(lean_object* v_x_153_, lean_object* v_inst_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_Lean_Meta_mkInstPiOfInstForall(v_x_153_, v_inst_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0(lean_object* v_00_u03b1_161_, lean_object* v_msg_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = l_Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0___redArg(v_msg_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0___boxed(lean_object* v_00_u03b1_169_, lean_object* v_msg_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0(v_00_u03b1_169_, v_msg_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkInstPiOfInstsForall_spec__0(lean_object* v_as_177_, size_t v_sz_178_, size_t v_i_179_, lean_object* v_b_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_){
_start:
{
uint8_t v___x_186_; 
v___x_186_ = lean_usize_dec_lt(v_i_179_, v_sz_178_);
if (v___x_186_ == 0)
{
lean_object* v___x_187_; 
lean_dec(v___y_184_);
lean_dec_ref(v___y_183_);
lean_dec(v___y_182_);
lean_dec_ref(v___y_181_);
v___x_187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_187_, 0, v_b_180_);
return v___x_187_;
}
else
{
lean_object* v_a_188_; lean_object* v___x_189_; 
v_a_188_ = lean_array_uget_borrowed(v_as_177_, v_i_179_);
lean_inc(v___y_184_);
lean_inc_ref(v___y_183_);
lean_inc(v___y_182_);
lean_inc_ref(v___y_181_);
lean_inc(v_a_188_);
v___x_189_ = l_Lean_Meta_mkInstPiOfInstForall(v_a_188_, v_b_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_);
if (lean_obj_tag(v___x_189_) == 0)
{
lean_object* v_a_190_; size_t v___x_191_; size_t v___x_192_; 
v_a_190_ = lean_ctor_get(v___x_189_, 0);
lean_inc(v_a_190_);
lean_dec_ref(v___x_189_);
v___x_191_ = ((size_t)1ULL);
v___x_192_ = lean_usize_add(v_i_179_, v___x_191_);
v_i_179_ = v___x_192_;
v_b_180_ = v_a_190_;
goto _start;
}
else
{
lean_dec(v___y_184_);
lean_dec_ref(v___y_183_);
lean_dec(v___y_182_);
lean_dec_ref(v___y_181_);
return v___x_189_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkInstPiOfInstsForall_spec__0___boxed(lean_object* v_as_194_, lean_object* v_sz_195_, lean_object* v_i_196_, lean_object* v_b_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_){
_start:
{
size_t v_sz_boxed_203_; size_t v_i_boxed_204_; lean_object* v_res_205_; 
v_sz_boxed_203_ = lean_unbox_usize(v_sz_195_);
lean_dec(v_sz_195_);
v_i_boxed_204_ = lean_unbox_usize(v_i_196_);
lean_dec(v_i_196_);
v_res_205_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkInstPiOfInstsForall_spec__0(v_as_194_, v_sz_boxed_203_, v_i_boxed_204_, v_b_197_, v___y_198_, v___y_199_, v___y_200_, v___y_201_);
lean_dec_ref(v_as_194_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInstPiOfInstsForall(lean_object* v_xs_206_, lean_object* v_inst_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_){
_start:
{
lean_object* v___x_213_; size_t v_sz_214_; size_t v___x_215_; lean_object* v___x_216_; 
v___x_213_ = l_Array_reverse___redArg(v_xs_206_);
v_sz_214_ = lean_array_size(v___x_213_);
v___x_215_ = ((size_t)0ULL);
v___x_216_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkInstPiOfInstsForall_spec__0(v___x_213_, v_sz_214_, v___x_215_, v_inst_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_);
lean_dec_ref(v___x_213_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInstPiOfInstsForall___boxed(lean_object* v_xs_217_, lean_object* v_inst_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l_Lean_Meta_mkInstPiOfInstsForall(v_xs_217_, v_inst_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_);
return v_res_224_;
}
}
static lean_object* _init_l_Lean_Meta_mkFixOfMonFun___closed__1(void){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_226_ = ((lean_object*)(l_Lean_Meta_mkFixOfMonFun___closed__0));
v___x_227_ = l_Lean_stringToMessageData(v___x_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFixOfMonFun(lean_object* v_packedType_238_, lean_object* v_packedInst_239_, lean_object* v_hmono_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_){
_start:
{
lean_object* v___x_246_; 
lean_inc(v_a_244_);
lean_inc_ref(v_a_243_);
lean_inc(v_a_242_);
lean_inc_ref(v_a_241_);
lean_inc_ref(v_packedInst_239_);
v___x_246_ = lean_infer_type(v_packedInst_239_, v_a_241_, v_a_242_, v_a_243_, v_a_244_);
if (lean_obj_tag(v___x_246_) == 0)
{
lean_object* v_a_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_295_; 
v_a_247_ = lean_ctor_get(v___x_246_, 0);
v_isSharedCheck_295_ = !lean_is_exclusive(v___x_246_);
if (v_isSharedCheck_295_ == 0)
{
v___x_249_ = v___x_246_;
v_isShared_250_ = v_isSharedCheck_295_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_a_247_);
lean_dec(v___x_246_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_295_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_251_; uint8_t v___x_252_; 
v___x_251_ = ((lean_object*)(l_Lean_Meta_mkInstPiOfInstForall___closed__3));
v___x_252_ = l_Lean_Expr_isAppOf(v_a_247_, v___x_251_);
lean_dec(v_a_247_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; 
lean_inc(v_a_244_);
lean_inc_ref(v_a_243_);
lean_inc(v_a_242_);
lean_inc_ref(v_a_241_);
lean_inc_ref(v_packedInst_239_);
v___x_253_ = lean_infer_type(v_packedInst_239_, v_a_241_, v_a_242_, v_a_243_, v_a_244_);
if (lean_obj_tag(v___x_253_) == 0)
{
lean_object* v_a_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_280_; 
v_a_254_ = lean_ctor_get(v___x_253_, 0);
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_253_);
if (v_isSharedCheck_280_ == 0)
{
v___x_256_ = v___x_253_;
v_isShared_257_ = v_isSharedCheck_280_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_a_254_);
lean_dec(v___x_253_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_280_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___x_258_; uint8_t v___x_259_; 
v___x_258_ = ((lean_object*)(l_Lean_Meta_mkInstPiOfInstForall___closed__5));
v___x_259_ = l_Lean_Expr_isAppOf(v_a_254_, v___x_258_);
lean_dec(v_a_254_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
lean_del_object(v___x_256_);
lean_del_object(v___x_249_);
lean_dec_ref(v_hmono_240_);
lean_dec_ref(v_packedType_238_);
v___x_260_ = lean_obj_once(&l_Lean_Meta_mkFixOfMonFun___closed__1, &l_Lean_Meta_mkFixOfMonFun___closed__1_once, _init_l_Lean_Meta_mkFixOfMonFun___closed__1);
v___x_261_ = l_Lean_MessageData_ofExpr(v_packedInst_239_);
v___x_262_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_262_, 0, v___x_260_);
lean_ctor_set(v___x_262_, 1, v___x_261_);
v___x_263_ = l_Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0___redArg(v___x_262_, v_a_241_, v_a_242_, v_a_243_, v_a_244_);
lean_dec(v_a_244_);
lean_dec_ref(v_a_243_);
lean_dec(v_a_242_);
lean_dec_ref(v_a_241_);
return v___x_263_;
}
else
{
lean_object* v___x_264_; lean_object* v___x_266_; 
v___x_264_ = ((lean_object*)(l_Lean_Meta_mkFixOfMonFun___closed__3));
if (v_isShared_257_ == 0)
{
lean_ctor_set_tag(v___x_256_, 1);
lean_ctor_set(v___x_256_, 0, v_packedType_238_);
v___x_266_ = v___x_256_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_packedType_238_);
v___x_266_ = v_reuseFailAlloc_279_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
lean_object* v___x_268_; 
if (v_isShared_250_ == 0)
{
lean_ctor_set_tag(v___x_249_, 1);
lean_ctor_set(v___x_249_, 0, v_packedInst_239_);
v___x_268_ = v___x_249_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_packedInst_239_);
v___x_268_ = v_reuseFailAlloc_278_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_269_ = lean_box(0);
v___x_270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_270_, 0, v_hmono_240_);
v___x_271_ = lean_unsigned_to_nat(4u);
v___x_272_ = lean_mk_empty_array_with_capacity(v___x_271_);
v___x_273_ = lean_array_push(v___x_272_, v___x_266_);
v___x_274_ = lean_array_push(v___x_273_, v___x_268_);
v___x_275_ = lean_array_push(v___x_274_, v___x_269_);
v___x_276_ = lean_array_push(v___x_275_, v___x_270_);
v___x_277_ = l_Lean_Meta_mkAppOptM(v___x_264_, v___x_276_, v_a_241_, v_a_242_, v_a_243_, v_a_244_);
return v___x_277_;
}
}
}
}
}
else
{
lean_del_object(v___x_249_);
lean_dec(v_a_244_);
lean_dec_ref(v_a_243_);
lean_dec(v_a_242_);
lean_dec_ref(v_a_241_);
lean_dec_ref(v_hmono_240_);
lean_dec_ref(v_packedInst_239_);
lean_dec_ref(v_packedType_238_);
return v___x_253_;
}
}
else
{
lean_object* v___x_281_; lean_object* v___x_283_; 
v___x_281_ = ((lean_object*)(l_Lean_Meta_mkFixOfMonFun___closed__5));
if (v_isShared_250_ == 0)
{
lean_ctor_set_tag(v___x_249_, 1);
lean_ctor_set(v___x_249_, 0, v_packedType_238_);
v___x_283_ = v___x_249_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v_packedType_238_);
v___x_283_ = v_reuseFailAlloc_294_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_284_, 0, v_packedInst_239_);
v___x_285_ = lean_box(0);
v___x_286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_286_, 0, v_hmono_240_);
v___x_287_ = lean_unsigned_to_nat(4u);
v___x_288_ = lean_mk_empty_array_with_capacity(v___x_287_);
v___x_289_ = lean_array_push(v___x_288_, v___x_283_);
v___x_290_ = lean_array_push(v___x_289_, v___x_284_);
v___x_291_ = lean_array_push(v___x_290_, v___x_285_);
v___x_292_ = lean_array_push(v___x_291_, v___x_286_);
v___x_293_ = l_Lean_Meta_mkAppOptM(v___x_281_, v___x_292_, v_a_241_, v_a_242_, v_a_243_, v_a_244_);
return v___x_293_;
}
}
}
}
else
{
lean_dec(v_a_244_);
lean_dec_ref(v_a_243_);
lean_dec(v_a_242_);
lean_dec_ref(v_a_241_);
lean_dec_ref(v_hmono_240_);
lean_dec_ref(v_packedInst_239_);
lean_dec_ref(v_packedType_238_);
return v___x_246_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFixOfMonFun___boxed(lean_object* v_packedType_296_, lean_object* v_packedInst_297_, lean_object* v_hmono_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean_Meta_mkFixOfMonFun(v_packedType_296_, v_packedInst_297_, v_hmono_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
return v_res_304_;
}
}
static lean_object* _init_l_Lean_Meta_toPartialOrder___closed__1(void){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_306_ = ((lean_object*)(l_Lean_Meta_toPartialOrder___closed__0));
v___x_307_ = l_Lean_stringToMessageData(v___x_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_toPartialOrder(lean_object* v_packedInst_319_, lean_object* v_type_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_){
_start:
{
lean_object* v___x_326_; 
lean_inc(v_a_324_);
lean_inc_ref(v_a_323_);
lean_inc(v_a_322_);
lean_inc_ref(v_a_321_);
lean_inc_ref(v_packedInst_319_);
v___x_326_ = lean_infer_type(v_packedInst_319_, v_a_321_, v_a_322_, v_a_323_, v_a_324_);
if (lean_obj_tag(v___x_326_) == 0)
{
lean_object* v_a_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_363_; 
v_a_327_ = lean_ctor_get(v___x_326_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v___x_326_);
if (v_isSharedCheck_363_ == 0)
{
v___x_329_ = v___x_326_;
v_isShared_330_ = v_isSharedCheck_363_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_a_327_);
lean_dec(v___x_326_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_363_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_331_; uint8_t v___x_332_; 
v___x_331_ = ((lean_object*)(l_Lean_Meta_mkInstPiOfInstForall___closed__3));
v___x_332_ = l_Lean_Expr_isAppOf(v_a_327_, v___x_331_);
lean_dec(v_a_327_);
if (v___x_332_ == 0)
{
lean_object* v___x_333_; 
lean_del_object(v___x_329_);
lean_inc(v_a_324_);
lean_inc_ref(v_a_323_);
lean_inc(v_a_322_);
lean_inc_ref(v_a_321_);
lean_inc_ref(v_packedInst_319_);
v___x_333_ = lean_infer_type(v_packedInst_319_, v_a_321_, v_a_322_, v_a_323_, v_a_324_);
if (lean_obj_tag(v___x_333_) == 0)
{
lean_object* v_a_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_353_; 
v_a_334_ = lean_ctor_get(v___x_333_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_353_ == 0)
{
v___x_336_ = v___x_333_;
v_isShared_337_ = v_isSharedCheck_353_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_a_334_);
lean_dec(v___x_333_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_353_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_338_; uint8_t v___x_339_; 
v___x_338_ = ((lean_object*)(l_Lean_Meta_mkInstPiOfInstForall___closed__5));
v___x_339_ = l_Lean_Expr_isAppOf(v_a_334_, v___x_338_);
lean_dec(v_a_334_);
if (v___x_339_ == 0)
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
lean_del_object(v___x_336_);
lean_dec(v_type_320_);
v___x_340_ = lean_obj_once(&l_Lean_Meta_toPartialOrder___closed__1, &l_Lean_Meta_toPartialOrder___closed__1_once, _init_l_Lean_Meta_toPartialOrder___closed__1);
v___x_341_ = l_Lean_MessageData_ofExpr(v_packedInst_319_);
v___x_342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_340_);
lean_ctor_set(v___x_342_, 1, v___x_341_);
v___x_343_ = l_Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0___redArg(v___x_342_, v_a_321_, v_a_322_, v_a_323_, v_a_324_);
lean_dec(v_a_324_);
lean_dec_ref(v_a_323_);
lean_dec(v_a_322_);
lean_dec_ref(v_a_321_);
return v___x_343_;
}
else
{
lean_object* v___x_344_; lean_object* v___x_346_; 
v___x_344_ = ((lean_object*)(l_Lean_Meta_toPartialOrder___closed__3));
if (v_isShared_337_ == 0)
{
lean_ctor_set_tag(v___x_336_, 1);
lean_ctor_set(v___x_336_, 0, v_packedInst_319_);
v___x_346_ = v___x_336_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_packedInst_319_);
v___x_346_ = v_reuseFailAlloc_352_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_347_ = lean_unsigned_to_nat(2u);
v___x_348_ = lean_mk_empty_array_with_capacity(v___x_347_);
v___x_349_ = lean_array_push(v___x_348_, v_type_320_);
v___x_350_ = lean_array_push(v___x_349_, v___x_346_);
v___x_351_ = l_Lean_Meta_mkAppOptM(v___x_344_, v___x_350_, v_a_321_, v_a_322_, v_a_323_, v_a_324_);
return v___x_351_;
}
}
}
}
else
{
lean_dec(v_a_324_);
lean_dec_ref(v_a_323_);
lean_dec(v_a_322_);
lean_dec_ref(v_a_321_);
lean_dec(v_type_320_);
lean_dec_ref(v_packedInst_319_);
return v___x_333_;
}
}
else
{
lean_object* v___x_354_; lean_object* v___x_356_; 
v___x_354_ = ((lean_object*)(l_Lean_Meta_toPartialOrder___closed__4));
if (v_isShared_330_ == 0)
{
lean_ctor_set_tag(v___x_329_, 1);
lean_ctor_set(v___x_329_, 0, v_packedInst_319_);
v___x_356_ = v___x_329_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_packedInst_319_);
v___x_356_ = v_reuseFailAlloc_362_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_357_ = lean_unsigned_to_nat(2u);
v___x_358_ = lean_mk_empty_array_with_capacity(v___x_357_);
v___x_359_ = lean_array_push(v___x_358_, v_type_320_);
v___x_360_ = lean_array_push(v___x_359_, v___x_356_);
v___x_361_ = l_Lean_Meta_mkAppOptM(v___x_354_, v___x_360_, v_a_321_, v_a_322_, v_a_323_, v_a_324_);
return v___x_361_;
}
}
}
}
else
{
lean_dec(v_a_324_);
lean_dec_ref(v_a_323_);
lean_dec(v_a_322_);
lean_dec_ref(v_a_321_);
lean_dec(v_type_320_);
lean_dec_ref(v_packedInst_319_);
return v___x_326_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_toPartialOrder___boxed(lean_object* v_packedInst_364_, lean_object* v_type_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_Meta_toPartialOrder(v_packedInst_364_, v_type_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_);
return v_res_371_;
}
}
static lean_object* _init_l_Lean_Meta_mkInstCCPOPProd___closed__2(void){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_377_ = lean_box(0);
v___x_378_ = lean_unsigned_to_nat(4u);
v___x_379_ = lean_mk_empty_array_with_capacity(v___x_378_);
v___x_380_ = lean_array_push(v___x_379_, v___x_377_);
return v___x_380_;
}
}
static lean_object* _init_l_Lean_Meta_mkInstCCPOPProd___closed__3(void){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_381_ = lean_box(0);
v___x_382_ = lean_obj_once(&l_Lean_Meta_mkInstCCPOPProd___closed__2, &l_Lean_Meta_mkInstCCPOPProd___closed__2_once, _init_l_Lean_Meta_mkInstCCPOPProd___closed__2);
v___x_383_ = lean_array_push(v___x_382_, v___x_381_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInstCCPOPProd(lean_object* v_inst_u2081_384_, lean_object* v_inst_u2082_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_391_ = ((lean_object*)(l_Lean_Meta_mkInstCCPOPProd___closed__1));
v___x_392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_392_, 0, v_inst_u2081_384_);
v___x_393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_393_, 0, v_inst_u2082_385_);
v___x_394_ = lean_obj_once(&l_Lean_Meta_mkInstCCPOPProd___closed__3, &l_Lean_Meta_mkInstCCPOPProd___closed__3_once, _init_l_Lean_Meta_mkInstCCPOPProd___closed__3);
v___x_395_ = lean_array_push(v___x_394_, v___x_392_);
v___x_396_ = lean_array_push(v___x_395_, v___x_393_);
v___x_397_ = l_Lean_Meta_mkAppOptM(v___x_391_, v___x_396_, v_a_386_, v_a_387_, v_a_388_, v_a_389_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInstCCPOPProd___boxed(lean_object* v_inst_u2081_398_, lean_object* v_inst_u2082_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Lean_Meta_mkInstCCPOPProd(v_inst_u2081_398_, v_inst_u2082_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInstCompleteLatticePProd(lean_object* v_inst_u2081_411_, lean_object* v_inst_u2082_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_418_ = ((lean_object*)(l_Lean_Meta_mkInstCompleteLatticePProd___closed__1));
v___x_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_419_, 0, v_inst_u2081_411_);
v___x_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_420_, 0, v_inst_u2082_412_);
v___x_421_ = lean_obj_once(&l_Lean_Meta_mkInstCCPOPProd___closed__3, &l_Lean_Meta_mkInstCCPOPProd___closed__3_once, _init_l_Lean_Meta_mkInstCCPOPProd___closed__3);
v___x_422_ = lean_array_push(v___x_421_, v___x_419_);
v___x_423_ = lean_array_push(v___x_422_, v___x_420_);
v___x_424_ = l_Lean_Meta_mkAppOptM(v___x_418_, v___x_423_, v_a_413_, v_a_414_, v_a_415_, v_a_416_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInstCompleteLatticePProd___boxed(lean_object* v_inst_u2081_425_, lean_object* v_inst_u2082_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_Lean_Meta_mkInstCompleteLatticePProd(v_inst_u2081_425_, v_inst_u2082_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_mkPackedPPRodInstance_spec__3(lean_object* v_a_433_, lean_object* v_a_434_){
_start:
{
if (lean_obj_tag(v_a_433_) == 0)
{
lean_object* v___x_435_; 
v___x_435_ = l_List_reverse___redArg(v_a_434_);
return v___x_435_;
}
else
{
lean_object* v_head_436_; lean_object* v_tail_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_446_; 
v_head_436_ = lean_ctor_get(v_a_433_, 0);
v_tail_437_ = lean_ctor_get(v_a_433_, 1);
v_isSharedCheck_446_ = !lean_is_exclusive(v_a_433_);
if (v_isSharedCheck_446_ == 0)
{
v___x_439_ = v_a_433_;
v_isShared_440_ = v_isSharedCheck_446_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_tail_437_);
lean_inc(v_head_436_);
lean_dec(v_a_433_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_446_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_441_; lean_object* v___x_443_; 
v___x_441_ = l_Lean_MessageData_ofExpr(v_head_436_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 1, v_a_434_);
lean_ctor_set(v___x_439_, 0, v___x_441_);
v___x_443_ = v___x_439_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v___x_441_);
lean_ctor_set(v_reuseFailAlloc_445_, 1, v_a_434_);
v___x_443_ = v_reuseFailAlloc_445_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
v_a_433_ = v_tail_437_;
v_a_434_ = v___x_443_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkPackedPPRodInstance_spec__0(size_t v_sz_447_, size_t v_i_448_, lean_object* v_bs_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_){
_start:
{
uint8_t v___x_455_; 
v___x_455_ = lean_usize_dec_lt(v_i_448_, v_sz_447_);
if (v___x_455_ == 0)
{
lean_object* v___x_456_; 
lean_dec(v___y_453_);
lean_dec_ref(v___y_452_);
lean_dec(v___y_451_);
lean_dec_ref(v___y_450_);
v___x_456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_456_, 0, v_bs_449_);
return v___x_456_;
}
else
{
lean_object* v_v_457_; lean_object* v___x_458_; 
v_v_457_ = lean_array_uget_borrowed(v_bs_449_, v_i_448_);
lean_inc(v___y_453_);
lean_inc_ref(v___y_452_);
lean_inc(v___y_451_);
lean_inc_ref(v___y_450_);
lean_inc(v_v_457_);
v___x_458_ = lean_infer_type(v_v_457_, v___y_450_, v___y_451_, v___y_452_, v___y_453_);
if (lean_obj_tag(v___x_458_) == 0)
{
lean_object* v_a_459_; lean_object* v___x_460_; lean_object* v_bs_x27_461_; size_t v___x_462_; size_t v___x_463_; lean_object* v___x_464_; 
v_a_459_ = lean_ctor_get(v___x_458_, 0);
lean_inc(v_a_459_);
lean_dec_ref(v___x_458_);
v___x_460_ = lean_unsigned_to_nat(0u);
v_bs_x27_461_ = lean_array_uset(v_bs_449_, v_i_448_, v___x_460_);
v___x_462_ = ((size_t)1ULL);
v___x_463_ = lean_usize_add(v_i_448_, v___x_462_);
v___x_464_ = lean_array_uset(v_bs_x27_461_, v_i_448_, v_a_459_);
v_i_448_ = v___x_463_;
v_bs_449_ = v___x_464_;
goto _start;
}
else
{
lean_object* v_a_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_473_; 
lean_dec(v___y_453_);
lean_dec_ref(v___y_452_);
lean_dec(v___y_451_);
lean_dec_ref(v___y_450_);
lean_dec_ref(v_bs_449_);
v_a_466_ = lean_ctor_get(v___x_458_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_473_ == 0)
{
v___x_468_ = v___x_458_;
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_a_466_);
lean_dec(v___x_458_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_471_; 
if (v_isShared_469_ == 0)
{
v___x_471_ = v___x_468_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_a_466_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
return v___x_471_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkPackedPPRodInstance_spec__0___boxed(lean_object* v_sz_474_, lean_object* v_i_475_, lean_object* v_bs_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
size_t v_sz_boxed_482_; size_t v_i_boxed_483_; lean_object* v_res_484_; 
v_sz_boxed_482_ = lean_unbox_usize(v_sz_474_);
lean_dec(v_sz_474_);
v_i_boxed_483_ = lean_unbox_usize(v_i_475_);
lean_dec(v_i_475_);
v_res_484_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkPackedPPRodInstance_spec__0(v_sz_boxed_482_, v_i_boxed_483_, v_bs_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_);
return v_res_484_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkPackedPPRodInstance_spec__1(lean_object* v_as_485_, size_t v_i_486_, size_t v_stop_487_){
_start:
{
uint8_t v___x_488_; 
v___x_488_ = lean_usize_dec_eq(v_i_486_, v_stop_487_);
if (v___x_488_ == 0)
{
uint8_t v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; uint8_t v___x_492_; 
v___x_489_ = 1;
v___x_490_ = lean_array_uget_borrowed(v_as_485_, v_i_486_);
v___x_491_ = ((lean_object*)(l_Lean_Meta_mkInstPiOfInstForall___closed__3));
v___x_492_ = l_Lean_Expr_isAppOf(v___x_490_, v___x_491_);
if (v___x_492_ == 0)
{
return v___x_489_;
}
else
{
if (v___x_488_ == 0)
{
size_t v___x_493_; size_t v___x_494_; 
v___x_493_ = ((size_t)1ULL);
v___x_494_ = lean_usize_add(v_i_486_, v___x_493_);
v_i_486_ = v___x_494_;
goto _start;
}
else
{
return v___x_489_;
}
}
}
else
{
uint8_t v___x_496_; 
v___x_496_ = 0;
return v___x_496_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkPackedPPRodInstance_spec__1___boxed(lean_object* v_as_497_, lean_object* v_i_498_, lean_object* v_stop_499_){
_start:
{
size_t v_i_boxed_500_; size_t v_stop_boxed_501_; uint8_t v_res_502_; lean_object* v_r_503_; 
v_i_boxed_500_ = lean_unbox_usize(v_i_498_);
lean_dec(v_i_498_);
v_stop_boxed_501_ = lean_unbox_usize(v_stop_499_);
lean_dec(v_stop_499_);
v_res_502_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkPackedPPRodInstance_spec__1(v_as_497_, v_i_boxed_500_, v_stop_boxed_501_);
lean_dec_ref(v_as_497_);
v_r_503_ = lean_box(v_res_502_);
return v_r_503_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkPackedPPRodInstance_spec__2(uint8_t v___x_504_, lean_object* v_as_505_, size_t v_i_506_, size_t v_stop_507_){
_start:
{
uint8_t v___x_512_; 
v___x_512_ = lean_usize_dec_eq(v_i_506_, v_stop_507_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; lean_object* v___x_514_; uint8_t v___x_515_; 
v___x_513_ = lean_array_uget_borrowed(v_as_505_, v_i_506_);
v___x_514_ = ((lean_object*)(l_Lean_Meta_mkInstPiOfInstForall___closed__5));
v___x_515_ = l_Lean_Expr_isAppOf(v___x_513_, v___x_514_);
if (v___x_515_ == 0)
{
if (v___x_504_ == 0)
{
goto v___jp_508_;
}
else
{
return v___x_504_;
}
}
else
{
goto v___jp_508_;
}
}
else
{
uint8_t v___x_516_; 
v___x_516_ = 0;
return v___x_516_;
}
v___jp_508_:
{
size_t v___x_509_; size_t v___x_510_; 
v___x_509_ = ((size_t)1ULL);
v___x_510_ = lean_usize_add(v_i_506_, v___x_509_);
v_i_506_ = v___x_510_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkPackedPPRodInstance_spec__2___boxed(lean_object* v___x_517_, lean_object* v_as_518_, lean_object* v_i_519_, lean_object* v_stop_520_){
_start:
{
uint8_t v___x_1497__boxed_521_; size_t v_i_boxed_522_; size_t v_stop_boxed_523_; uint8_t v_res_524_; lean_object* v_r_525_; 
v___x_1497__boxed_521_ = lean_unbox(v___x_517_);
v_i_boxed_522_ = lean_unbox_usize(v_i_519_);
lean_dec(v_i_519_);
v_stop_boxed_523_ = lean_unbox_usize(v_stop_520_);
lean_dec(v_stop_520_);
v_res_524_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkPackedPPRodInstance_spec__2(v___x_1497__boxed_521_, v_as_518_, v_i_boxed_522_, v_stop_boxed_523_);
lean_dec_ref(v_as_518_);
v_r_525_ = lean_box(v_res_524_);
return v_r_525_;
}
}
static lean_object* _init_l_Lean_Meta_mkPackedPPRodInstance___closed__3(void){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = ((lean_object*)(l_Lean_Meta_mkPackedPPRodInstance___closed__2));
v___x_530_ = l_Lean_stringToMessageData(v___x_529_);
return v___x_530_;
}
}
static lean_object* _init_l_Lean_Meta_mkPackedPPRodInstance___closed__5(void){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = ((lean_object*)(l_Lean_Meta_mkPackedPPRodInstance___closed__4));
v___x_533_ = l_Lean_stringToMessageData(v___x_532_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPackedPPRodInstance(lean_object* v_insts_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_){
_start:
{
size_t v_sz_540_; size_t v___x_541_; lean_object* v___x_542_; 
v_sz_540_ = lean_array_size(v_insts_534_);
v___x_541_ = ((size_t)0ULL);
lean_inc(v_a_538_);
lean_inc_ref(v_a_537_);
lean_inc(v_a_536_);
lean_inc_ref(v_a_535_);
lean_inc_ref(v_insts_534_);
v___x_542_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkPackedPPRodInstance_spec__0(v_sz_540_, v___x_541_, v_insts_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_);
if (lean_obj_tag(v___x_542_) == 0)
{
lean_object* v_a_543_; lean_object* v___x_552_; lean_object* v___x_553_; uint8_t v___x_554_; 
v_a_543_ = lean_ctor_get(v___x_542_, 0);
lean_inc(v_a_543_);
lean_dec_ref(v___x_542_);
v___x_552_ = lean_unsigned_to_nat(0u);
v___x_553_ = lean_array_get_size(v_a_543_);
v___x_554_ = lean_nat_dec_lt(v___x_552_, v___x_553_);
if (v___x_554_ == 0)
{
lean_dec(v_a_543_);
goto v___jp_548_;
}
else
{
if (v___x_554_ == 0)
{
lean_dec(v_a_543_);
goto v___jp_548_;
}
else
{
size_t v___x_555_; uint8_t v___x_556_; 
v___x_555_ = lean_usize_of_nat(v___x_553_);
v___x_556_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkPackedPPRodInstance_spec__1(v_a_543_, v___x_541_, v___x_555_);
if (v___x_556_ == 0)
{
lean_dec(v_a_543_);
goto v___jp_548_;
}
else
{
if (v___x_554_ == 0)
{
lean_dec(v_a_543_);
goto v___jp_544_;
}
else
{
if (v___x_554_ == 0)
{
lean_dec(v_a_543_);
goto v___jp_544_;
}
else
{
uint8_t v___x_557_; 
v___x_557_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkPackedPPRodInstance_spec__2(v___x_556_, v_a_543_, v___x_541_, v___x_555_);
if (v___x_557_ == 0)
{
lean_dec(v_a_543_);
goto v___jp_544_;
}
else
{
lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_558_ = lean_obj_once(&l_Lean_Meta_mkPackedPPRodInstance___closed__3, &l_Lean_Meta_mkPackedPPRodInstance___closed__3_once, _init_l_Lean_Meta_mkPackedPPRodInstance___closed__3);
v___x_559_ = lean_array_to_list(v_a_543_);
v___x_560_ = lean_box(0);
v___x_561_ = l_List_mapTR_loop___at___00Lean_Meta_mkPackedPPRodInstance_spec__3(v___x_559_, v___x_560_);
v___x_562_ = l_Lean_MessageData_ofList(v___x_561_);
v___x_563_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_563_, 0, v___x_558_);
lean_ctor_set(v___x_563_, 1, v___x_562_);
v___x_564_ = lean_obj_once(&l_Lean_Meta_mkPackedPPRodInstance___closed__5, &l_Lean_Meta_mkPackedPPRodInstance___closed__5_once, _init_l_Lean_Meta_mkPackedPPRodInstance___closed__5);
v___x_565_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_565_, 0, v___x_563_);
lean_ctor_set(v___x_565_, 1, v___x_564_);
v___x_566_ = lean_array_to_list(v_insts_534_);
v___x_567_ = l_List_mapTR_loop___at___00Lean_Meta_mkPackedPPRodInstance_spec__3(v___x_566_, v___x_560_);
v___x_568_ = l_Lean_MessageData_ofList(v___x_567_);
v___x_569_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_569_, 0, v___x_565_);
lean_ctor_set(v___x_569_, 1, v___x_568_);
v___x_570_ = l_Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0___redArg(v___x_569_, v_a_535_, v_a_536_, v_a_537_, v_a_538_);
lean_dec(v_a_538_);
lean_dec_ref(v_a_537_);
lean_dec(v_a_536_);
lean_dec_ref(v_a_535_);
return v___x_570_;
}
}
}
}
}
}
v___jp_544_:
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_545_ = l_Lean_instInhabitedExpr;
v___x_546_ = ((lean_object*)(l_Lean_Meta_mkPackedPPRodInstance___closed__0));
v___x_547_ = l_Lean_Meta_PProdN_genMk___redArg(v___x_545_, v___x_546_, v_insts_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_);
return v___x_547_;
}
v___jp_548_:
{
lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_549_ = l_Lean_instInhabitedExpr;
v___x_550_ = ((lean_object*)(l_Lean_Meta_mkPackedPPRodInstance___closed__1));
v___x_551_ = l_Lean_Meta_PProdN_genMk___redArg(v___x_549_, v___x_550_, v_insts_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_);
return v___x_551_;
}
}
else
{
lean_object* v_a_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_578_; 
lean_dec(v_a_538_);
lean_dec_ref(v_a_537_);
lean_dec(v_a_536_);
lean_dec_ref(v_a_535_);
lean_dec_ref(v_insts_534_);
v_a_571_ = lean_ctor_get(v___x_542_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_578_ == 0)
{
v___x_573_ = v___x_542_;
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_a_571_);
lean_dec(v___x_542_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_576_; 
if (v_isShared_574_ == 0)
{
v___x_576_ = v___x_573_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_a_571_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPackedPPRodInstance___boxed(lean_object* v_insts_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Lean_Meta_mkPackedPPRodInstance(v_insts_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_);
return v_res_585_;
}
}
lean_object* runtime_initialize_Lean_Meta_PProdN(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Init_Internal_Order_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Order(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_PProdN(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Internal_Order_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Order(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_PProdN(uint8_t builtin);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* initialize_Init_Internal_Order_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Order(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_PProdN(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Internal_Order_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Order(builtin);
}
#ifdef __cplusplus
}
#endif
