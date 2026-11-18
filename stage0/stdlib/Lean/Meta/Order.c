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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
lean_object* lean_array_uget(lean_object*, size_t);
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
lean_object* v___x_7_; lean_object* v_env_8_; uint8_t v___x_9_; lean_object* v_env_10_; lean_object* v___x_11_; lean_object* v_toCold_12_; lean_object* v_mctx_13_; lean_object* v_lctx_14_; lean_object* v_options_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_7_ = lean_st_ref_get(v___y_5_);
v_env_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc_ref(v_env_8_);
lean_dec(v___x_7_);
v___x_9_ = 0;
v_env_10_ = l_Lean_Environment_setRecordingDeps(v_env_8_, v___x_9_);
v___x_11_ = lean_st_ref_get(v___y_3_);
v_toCold_12_ = lean_ctor_get(v___y_4_, 0);
v_mctx_13_ = lean_ctor_get(v___x_11_, 0);
lean_inc_ref(v_mctx_13_);
lean_dec(v___x_11_);
v_lctx_14_ = lean_ctor_get(v___y_2_, 2);
v_options_15_ = lean_ctor_get(v_toCold_12_, 2);
lean_inc_ref(v_options_15_);
lean_inc_ref(v_lctx_14_);
v___x_16_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_16_, 0, v_env_10_);
lean_ctor_set(v___x_16_, 1, v_mctx_13_);
lean_ctor_set(v___x_16_, 2, v_lctx_14_);
lean_ctor_set(v___x_16_, 3, v_options_15_);
v___x_17_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_17_, 0, v___x_16_);
lean_ctor_set(v___x_17_, 1, v_msgData_1_);
v___x_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_18_, 0, v___x_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0_spec__0___boxed(lean_object* v_msgData_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0_spec__0(v_msgData_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_);
lean_dec(v___y_23_);
lean_dec_ref(v___y_22_);
lean_dec(v___y_21_);
lean_dec_ref(v___y_20_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0___redArg(lean_object* v_msg_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_){
_start:
{
lean_object* v_ref_32_; lean_object* v___x_33_; lean_object* v_a_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_42_; 
v_ref_32_ = lean_ctor_get(v___y_29_, 2);
v___x_33_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0_spec__0(v_msg_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_);
v_a_34_ = lean_ctor_get(v___x_33_, 0);
v_isSharedCheck_42_ = !lean_is_exclusive(v___x_33_);
if (v_isSharedCheck_42_ == 0)
{
v___x_36_ = v___x_33_;
v_isShared_37_ = v_isSharedCheck_42_;
goto v_resetjp_35_;
}
else
{
lean_inc(v_a_34_);
lean_dec(v___x_33_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_42_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
lean_object* v___x_38_; lean_object* v___x_40_; 
lean_inc(v_ref_32_);
v___x_38_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_38_, 0, v_ref_32_);
lean_ctor_set(v___x_38_, 1, v_a_34_);
if (v_isShared_37_ == 0)
{
lean_ctor_set_tag(v___x_36_, 1);
lean_ctor_set(v___x_36_, 0, v___x_38_);
v___x_40_ = v___x_36_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v___x_38_);
v___x_40_ = v_reuseFailAlloc_41_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
return v___x_40_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0___redArg___boxed(lean_object* v_msg_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0___redArg(v_msg_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_);
lean_dec(v___y_47_);
lean_dec_ref(v___y_46_);
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
return v_res_49_;
}
}
static lean_object* _init_l_Lean_Meta_mkInstPiOfInstForall___closed__7(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_63_ = ((lean_object*)(l_Lean_Meta_mkInstPiOfInstForall___closed__6));
v___x_64_ = l_Lean_stringToMessageData(v___x_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInstPiOfInstForall(lean_object* v_x_75_, lean_object* v_inst_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_){
_start:
{
lean_object* v___x_82_; 
lean_inc(v_a_80_);
lean_inc_ref(v_a_79_);
lean_inc(v_a_78_);
lean_inc_ref(v_a_77_);
lean_inc_ref(v_inst_76_);
v___x_82_ = lean_infer_type(v_inst_76_, v_a_77_, v_a_78_, v_a_79_, v_a_80_);
if (lean_obj_tag(v___x_82_) == 0)
{
lean_object* v_a_83_; lean_object* v___x_84_; uint8_t v___x_85_; uint8_t v___x_86_; 
v_a_83_ = lean_ctor_get(v___x_82_, 0);
lean_inc(v_a_83_);
lean_dec_ref_known(v___x_82_, 1);
v___x_84_ = ((lean_object*)(l_Lean_Meta_mkInstPiOfInstForall___closed__3));
v___x_85_ = l_Lean_Expr_isAppOf(v_a_83_, v___x_84_);
lean_dec(v_a_83_);
v___x_86_ = 1;
if (v___x_85_ == 0)
{
lean_object* v___x_87_; 
lean_inc(v_a_80_);
lean_inc_ref(v_a_79_);
lean_inc(v_a_78_);
lean_inc_ref(v_a_77_);
lean_inc_ref(v_inst_76_);
v___x_87_ = lean_infer_type(v_inst_76_, v_a_77_, v_a_78_, v_a_79_, v_a_80_);
if (lean_obj_tag(v___x_87_) == 0)
{
lean_object* v_a_88_; lean_object* v___x_89_; uint8_t v___x_90_; 
v_a_88_ = lean_ctor_get(v___x_87_, 0);
lean_inc(v_a_88_);
lean_dec_ref_known(v___x_87_, 1);
v___x_89_ = ((lean_object*)(l_Lean_Meta_mkInstPiOfInstForall___closed__5));
v___x_90_ = l_Lean_Expr_isAppOf(v_a_88_, v___x_89_);
lean_dec(v_a_88_);
if (v___x_90_ == 0)
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
lean_dec_ref(v_x_75_);
v___x_91_ = lean_obj_once(&l_Lean_Meta_mkInstPiOfInstForall___closed__7, &l_Lean_Meta_mkInstPiOfInstForall___closed__7_once, _init_l_Lean_Meta_mkInstPiOfInstForall___closed__7);
v___x_92_ = l_Lean_MessageData_ofExpr(v_inst_76_);
v___x_93_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_93_, 0, v___x_91_);
lean_ctor_set(v___x_93_, 1, v___x_92_);
v___x_94_ = l_Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0___redArg(v___x_93_, v_a_77_, v_a_78_, v_a_79_, v_a_80_);
return v___x_94_;
}
else
{
lean_object* v___x_95_; 
lean_inc(v_a_80_);
lean_inc_ref(v_a_79_);
lean_inc(v_a_78_);
lean_inc_ref(v_a_77_);
lean_inc_ref(v_x_75_);
v___x_95_ = lean_infer_type(v_x_75_, v_a_77_, v_a_78_, v_a_79_, v_a_80_);
if (lean_obj_tag(v___x_95_) == 0)
{
lean_object* v_a_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_124_; 
v_a_96_ = lean_ctor_get(v___x_95_, 0);
v_isSharedCheck_124_ = !lean_is_exclusive(v___x_95_);
if (v_isSharedCheck_124_ == 0)
{
v___x_98_ = v___x_95_;
v_isShared_99_ = v_isSharedCheck_124_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_a_96_);
lean_dec(v___x_95_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_124_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; uint8_t v___x_103_; lean_object* v___x_104_; 
v___x_100_ = lean_unsigned_to_nat(1u);
v___x_101_ = lean_mk_empty_array_with_capacity(v___x_100_);
v___x_102_ = lean_array_push(v___x_101_, v_x_75_);
v___x_103_ = 1;
v___x_104_ = l_Lean_Meta_mkLambdaFVars(v___x_102_, v_inst_76_, v___x_85_, v___x_86_, v___x_85_, v___x_86_, v___x_103_, v_a_77_, v_a_78_, v_a_79_, v_a_80_);
lean_dec_ref(v___x_102_);
if (lean_obj_tag(v___x_104_) == 0)
{
lean_object* v_a_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_123_; 
v_a_105_ = lean_ctor_get(v___x_104_, 0);
v_isSharedCheck_123_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_123_ == 0)
{
v___x_107_ = v___x_104_;
v_isShared_108_ = v_isSharedCheck_123_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_a_105_);
lean_dec(v___x_104_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_123_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v___x_109_; lean_object* v___x_111_; 
v___x_109_ = ((lean_object*)(l_Lean_Meta_mkInstPiOfInstForall___closed__9));
if (v_isShared_108_ == 0)
{
lean_ctor_set_tag(v___x_107_, 1);
lean_ctor_set(v___x_107_, 0, v_a_96_);
v___x_111_ = v___x_107_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v_a_96_);
v___x_111_ = v_reuseFailAlloc_122_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
lean_object* v___x_112_; lean_object* v___x_114_; 
v___x_112_ = lean_box(0);
if (v_isShared_99_ == 0)
{
lean_ctor_set_tag(v___x_98_, 1);
lean_ctor_set(v___x_98_, 0, v_a_105_);
v___x_114_ = v___x_98_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v_a_105_);
v___x_114_ = v_reuseFailAlloc_121_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_115_ = lean_unsigned_to_nat(3u);
v___x_116_ = lean_mk_empty_array_with_capacity(v___x_115_);
v___x_117_ = lean_array_push(v___x_116_, v___x_111_);
v___x_118_ = lean_array_push(v___x_117_, v___x_112_);
v___x_119_ = lean_array_push(v___x_118_, v___x_114_);
v___x_120_ = l_Lean_Meta_mkAppOptM(v___x_109_, v___x_119_, v_a_77_, v_a_78_, v_a_79_, v_a_80_);
return v___x_120_;
}
}
}
}
else
{
lean_del_object(v___x_98_);
lean_dec(v_a_96_);
return v___x_104_;
}
}
}
else
{
lean_dec_ref(v_inst_76_);
lean_dec_ref(v_x_75_);
return v___x_95_;
}
}
}
else
{
lean_dec_ref(v_inst_76_);
lean_dec_ref(v_x_75_);
return v___x_87_;
}
}
else
{
lean_object* v___x_125_; 
lean_inc(v_a_80_);
lean_inc_ref(v_a_79_);
lean_inc(v_a_78_);
lean_inc_ref(v_a_77_);
lean_inc_ref(v_x_75_);
v___x_125_ = lean_infer_type(v_x_75_, v_a_77_, v_a_78_, v_a_79_, v_a_80_);
if (lean_obj_tag(v___x_125_) == 0)
{
lean_object* v_a_126_; lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_155_; 
v_a_126_ = lean_ctor_get(v___x_125_, 0);
v_isSharedCheck_155_ = !lean_is_exclusive(v___x_125_);
if (v_isSharedCheck_155_ == 0)
{
v___x_128_ = v___x_125_;
v_isShared_129_ = v_isSharedCheck_155_;
goto v_resetjp_127_;
}
else
{
lean_inc(v_a_126_);
lean_dec(v___x_125_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_155_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; uint8_t v___x_133_; uint8_t v___x_134_; lean_object* v___x_135_; 
v___x_130_ = lean_unsigned_to_nat(1u);
v___x_131_ = lean_mk_empty_array_with_capacity(v___x_130_);
v___x_132_ = lean_array_push(v___x_131_, v_x_75_);
v___x_133_ = 0;
v___x_134_ = 1;
v___x_135_ = l_Lean_Meta_mkLambdaFVars(v___x_132_, v_inst_76_, v___x_133_, v___x_86_, v___x_133_, v___x_86_, v___x_134_, v_a_77_, v_a_78_, v_a_79_, v_a_80_);
lean_dec_ref(v___x_132_);
if (lean_obj_tag(v___x_135_) == 0)
{
lean_object* v_a_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_154_; 
v_a_136_ = lean_ctor_get(v___x_135_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v___x_135_);
if (v_isSharedCheck_154_ == 0)
{
v___x_138_ = v___x_135_;
v_isShared_139_ = v_isSharedCheck_154_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_a_136_);
lean_dec(v___x_135_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_154_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___x_140_; lean_object* v___x_142_; 
v___x_140_ = ((lean_object*)(l_Lean_Meta_mkInstPiOfInstForall___closed__11));
if (v_isShared_139_ == 0)
{
lean_ctor_set_tag(v___x_138_, 1);
lean_ctor_set(v___x_138_, 0, v_a_126_);
v___x_142_ = v___x_138_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v_a_126_);
v___x_142_ = v_reuseFailAlloc_153_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
lean_object* v___x_143_; lean_object* v___x_145_; 
v___x_143_ = lean_box(0);
if (v_isShared_129_ == 0)
{
lean_ctor_set_tag(v___x_128_, 1);
lean_ctor_set(v___x_128_, 0, v_a_136_);
v___x_145_ = v___x_128_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_a_136_);
v___x_145_ = v_reuseFailAlloc_152_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_146_ = lean_unsigned_to_nat(3u);
v___x_147_ = lean_mk_empty_array_with_capacity(v___x_146_);
v___x_148_ = lean_array_push(v___x_147_, v___x_142_);
v___x_149_ = lean_array_push(v___x_148_, v___x_143_);
v___x_150_ = lean_array_push(v___x_149_, v___x_145_);
v___x_151_ = l_Lean_Meta_mkAppOptM(v___x_140_, v___x_150_, v_a_77_, v_a_78_, v_a_79_, v_a_80_);
return v___x_151_;
}
}
}
}
else
{
lean_del_object(v___x_128_);
lean_dec(v_a_126_);
return v___x_135_;
}
}
}
else
{
lean_dec_ref(v_inst_76_);
lean_dec_ref(v_x_75_);
return v___x_125_;
}
}
}
else
{
lean_dec_ref(v_inst_76_);
lean_dec_ref(v_x_75_);
return v___x_82_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInstPiOfInstForall___boxed(lean_object* v_x_156_, lean_object* v_inst_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l_Lean_Meta_mkInstPiOfInstForall(v_x_156_, v_inst_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_);
lean_dec(v_a_161_);
lean_dec_ref(v_a_160_);
lean_dec(v_a_159_);
lean_dec_ref(v_a_158_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0(lean_object* v_00_u03b1_164_, lean_object* v_msg_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = l_Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0___redArg(v_msg_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0___boxed(lean_object* v_00_u03b1_172_, lean_object* v_msg_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0(v_00_u03b1_172_, v_msg_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_);
lean_dec(v___y_177_);
lean_dec_ref(v___y_176_);
lean_dec(v___y_175_);
lean_dec_ref(v___y_174_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkInstPiOfInstsForall_spec__0(lean_object* v_as_180_, size_t v_sz_181_, size_t v_i_182_, lean_object* v_b_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_){
_start:
{
uint8_t v___x_189_; 
v___x_189_ = lean_usize_dec_lt(v_i_182_, v_sz_181_);
if (v___x_189_ == 0)
{
lean_object* v___x_190_; 
v___x_190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_190_, 0, v_b_183_);
return v___x_190_;
}
else
{
lean_object* v_a_191_; lean_object* v___x_192_; 
v_a_191_ = lean_array_uget_borrowed(v_as_180_, v_i_182_);
lean_inc(v_a_191_);
v___x_192_ = l_Lean_Meta_mkInstPiOfInstForall(v_a_191_, v_b_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_);
if (lean_obj_tag(v___x_192_) == 0)
{
lean_object* v_a_193_; size_t v___x_194_; size_t v___x_195_; 
v_a_193_ = lean_ctor_get(v___x_192_, 0);
lean_inc(v_a_193_);
lean_dec_ref_known(v___x_192_, 1);
v___x_194_ = ((size_t)1ULL);
v___x_195_ = lean_usize_add(v_i_182_, v___x_194_);
v_i_182_ = v___x_195_;
v_b_183_ = v_a_193_;
goto _start;
}
else
{
return v___x_192_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkInstPiOfInstsForall_spec__0___boxed(lean_object* v_as_197_, lean_object* v_sz_198_, lean_object* v_i_199_, lean_object* v_b_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_){
_start:
{
size_t v_sz_boxed_206_; size_t v_i_boxed_207_; lean_object* v_res_208_; 
v_sz_boxed_206_ = lean_unbox_usize(v_sz_198_);
lean_dec(v_sz_198_);
v_i_boxed_207_ = lean_unbox_usize(v_i_199_);
lean_dec(v_i_199_);
v_res_208_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkInstPiOfInstsForall_spec__0(v_as_197_, v_sz_boxed_206_, v_i_boxed_207_, v_b_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_);
lean_dec(v___y_204_);
lean_dec_ref(v___y_203_);
lean_dec(v___y_202_);
lean_dec_ref(v___y_201_);
lean_dec_ref(v_as_197_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInstPiOfInstsForall(lean_object* v_xs_209_, lean_object* v_inst_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_){
_start:
{
lean_object* v___x_216_; size_t v_sz_217_; size_t v___x_218_; lean_object* v___x_219_; 
v___x_216_ = l_Array_reverse___redArg(v_xs_209_);
v_sz_217_ = lean_array_size(v___x_216_);
v___x_218_ = ((size_t)0ULL);
v___x_219_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkInstPiOfInstsForall_spec__0(v___x_216_, v_sz_217_, v___x_218_, v_inst_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_);
lean_dec_ref(v___x_216_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInstPiOfInstsForall___boxed(lean_object* v_xs_220_, lean_object* v_inst_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Lean_Meta_mkInstPiOfInstsForall(v_xs_220_, v_inst_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_);
lean_dec(v_a_225_);
lean_dec_ref(v_a_224_);
lean_dec(v_a_223_);
lean_dec_ref(v_a_222_);
return v_res_227_;
}
}
static lean_object* _init_l_Lean_Meta_mkFixOfMonFun___closed__1(void){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_229_ = ((lean_object*)(l_Lean_Meta_mkFixOfMonFun___closed__0));
v___x_230_ = l_Lean_stringToMessageData(v___x_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFixOfMonFun(lean_object* v_packedType_241_, lean_object* v_packedInst_242_, lean_object* v_hmono_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_){
_start:
{
lean_object* v___x_249_; 
lean_inc(v_a_247_);
lean_inc_ref(v_a_246_);
lean_inc(v_a_245_);
lean_inc_ref(v_a_244_);
lean_inc_ref(v_packedInst_242_);
v___x_249_ = lean_infer_type(v_packedInst_242_, v_a_244_, v_a_245_, v_a_246_, v_a_247_);
if (lean_obj_tag(v___x_249_) == 0)
{
lean_object* v_a_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_298_; 
v_a_250_ = lean_ctor_get(v___x_249_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_298_ == 0)
{
v___x_252_ = v___x_249_;
v_isShared_253_ = v_isSharedCheck_298_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_a_250_);
lean_dec(v___x_249_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_298_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___x_254_; uint8_t v___x_255_; 
v___x_254_ = ((lean_object*)(l_Lean_Meta_mkInstPiOfInstForall___closed__3));
v___x_255_ = l_Lean_Expr_isAppOf(v_a_250_, v___x_254_);
lean_dec(v_a_250_);
if (v___x_255_ == 0)
{
lean_object* v___x_256_; 
lean_inc(v_a_247_);
lean_inc_ref(v_a_246_);
lean_inc(v_a_245_);
lean_inc_ref(v_a_244_);
lean_inc_ref(v_packedInst_242_);
v___x_256_ = lean_infer_type(v_packedInst_242_, v_a_244_, v_a_245_, v_a_246_, v_a_247_);
if (lean_obj_tag(v___x_256_) == 0)
{
lean_object* v_a_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_283_; 
v_a_257_ = lean_ctor_get(v___x_256_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_283_ == 0)
{
v___x_259_ = v___x_256_;
v_isShared_260_ = v_isSharedCheck_283_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_a_257_);
lean_dec(v___x_256_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_283_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_261_; uint8_t v___x_262_; 
v___x_261_ = ((lean_object*)(l_Lean_Meta_mkInstPiOfInstForall___closed__5));
v___x_262_ = l_Lean_Expr_isAppOf(v_a_257_, v___x_261_);
lean_dec(v_a_257_);
if (v___x_262_ == 0)
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
lean_del_object(v___x_259_);
lean_del_object(v___x_252_);
lean_dec_ref(v_hmono_243_);
lean_dec_ref(v_packedType_241_);
v___x_263_ = lean_obj_once(&l_Lean_Meta_mkFixOfMonFun___closed__1, &l_Lean_Meta_mkFixOfMonFun___closed__1_once, _init_l_Lean_Meta_mkFixOfMonFun___closed__1);
v___x_264_ = l_Lean_MessageData_ofExpr(v_packedInst_242_);
v___x_265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_263_);
lean_ctor_set(v___x_265_, 1, v___x_264_);
v___x_266_ = l_Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0___redArg(v___x_265_, v_a_244_, v_a_245_, v_a_246_, v_a_247_);
return v___x_266_;
}
else
{
lean_object* v___x_267_; lean_object* v___x_269_; 
v___x_267_ = ((lean_object*)(l_Lean_Meta_mkFixOfMonFun___closed__3));
if (v_isShared_260_ == 0)
{
lean_ctor_set_tag(v___x_259_, 1);
lean_ctor_set(v___x_259_, 0, v_packedType_241_);
v___x_269_ = v___x_259_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_packedType_241_);
v___x_269_ = v_reuseFailAlloc_282_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
lean_object* v___x_271_; 
if (v_isShared_253_ == 0)
{
lean_ctor_set_tag(v___x_252_, 1);
lean_ctor_set(v___x_252_, 0, v_packedInst_242_);
v___x_271_ = v___x_252_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_packedInst_242_);
v___x_271_ = v_reuseFailAlloc_281_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_272_ = lean_box(0);
v___x_273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_273_, 0, v_hmono_243_);
v___x_274_ = lean_unsigned_to_nat(4u);
v___x_275_ = lean_mk_empty_array_with_capacity(v___x_274_);
v___x_276_ = lean_array_push(v___x_275_, v___x_269_);
v___x_277_ = lean_array_push(v___x_276_, v___x_271_);
v___x_278_ = lean_array_push(v___x_277_, v___x_272_);
v___x_279_ = lean_array_push(v___x_278_, v___x_273_);
v___x_280_ = l_Lean_Meta_mkAppOptM(v___x_267_, v___x_279_, v_a_244_, v_a_245_, v_a_246_, v_a_247_);
return v___x_280_;
}
}
}
}
}
else
{
lean_del_object(v___x_252_);
lean_dec_ref(v_hmono_243_);
lean_dec_ref(v_packedInst_242_);
lean_dec_ref(v_packedType_241_);
return v___x_256_;
}
}
else
{
lean_object* v___x_284_; lean_object* v___x_286_; 
v___x_284_ = ((lean_object*)(l_Lean_Meta_mkFixOfMonFun___closed__5));
if (v_isShared_253_ == 0)
{
lean_ctor_set_tag(v___x_252_, 1);
lean_ctor_set(v___x_252_, 0, v_packedType_241_);
v___x_286_ = v___x_252_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_packedType_241_);
v___x_286_ = v_reuseFailAlloc_297_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_287_, 0, v_packedInst_242_);
v___x_288_ = lean_box(0);
v___x_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_289_, 0, v_hmono_243_);
v___x_290_ = lean_unsigned_to_nat(4u);
v___x_291_ = lean_mk_empty_array_with_capacity(v___x_290_);
v___x_292_ = lean_array_push(v___x_291_, v___x_286_);
v___x_293_ = lean_array_push(v___x_292_, v___x_287_);
v___x_294_ = lean_array_push(v___x_293_, v___x_288_);
v___x_295_ = lean_array_push(v___x_294_, v___x_289_);
v___x_296_ = l_Lean_Meta_mkAppOptM(v___x_284_, v___x_295_, v_a_244_, v_a_245_, v_a_246_, v_a_247_);
return v___x_296_;
}
}
}
}
else
{
lean_dec_ref(v_hmono_243_);
lean_dec_ref(v_packedInst_242_);
lean_dec_ref(v_packedType_241_);
return v___x_249_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFixOfMonFun___boxed(lean_object* v_packedType_299_, lean_object* v_packedInst_300_, lean_object* v_hmono_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Lean_Meta_mkFixOfMonFun(v_packedType_299_, v_packedInst_300_, v_hmono_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_);
lean_dec(v_a_305_);
lean_dec_ref(v_a_304_);
lean_dec(v_a_303_);
lean_dec_ref(v_a_302_);
return v_res_307_;
}
}
static lean_object* _init_l_Lean_Meta_toPartialOrder___closed__1(void){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_309_ = ((lean_object*)(l_Lean_Meta_toPartialOrder___closed__0));
v___x_310_ = l_Lean_stringToMessageData(v___x_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_toPartialOrder(lean_object* v_packedInst_322_, lean_object* v_type_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_){
_start:
{
lean_object* v___x_329_; 
lean_inc(v_a_327_);
lean_inc_ref(v_a_326_);
lean_inc(v_a_325_);
lean_inc_ref(v_a_324_);
lean_inc_ref(v_packedInst_322_);
v___x_329_ = lean_infer_type(v_packedInst_322_, v_a_324_, v_a_325_, v_a_326_, v_a_327_);
if (lean_obj_tag(v___x_329_) == 0)
{
lean_object* v_a_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_366_; 
v_a_330_ = lean_ctor_get(v___x_329_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_329_);
if (v_isSharedCheck_366_ == 0)
{
v___x_332_ = v___x_329_;
v_isShared_333_ = v_isSharedCheck_366_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_a_330_);
lean_dec(v___x_329_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_366_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_334_; uint8_t v___x_335_; 
v___x_334_ = ((lean_object*)(l_Lean_Meta_mkInstPiOfInstForall___closed__3));
v___x_335_ = l_Lean_Expr_isAppOf(v_a_330_, v___x_334_);
lean_dec(v_a_330_);
if (v___x_335_ == 0)
{
lean_object* v___x_336_; 
lean_del_object(v___x_332_);
lean_inc(v_a_327_);
lean_inc_ref(v_a_326_);
lean_inc(v_a_325_);
lean_inc_ref(v_a_324_);
lean_inc_ref(v_packedInst_322_);
v___x_336_ = lean_infer_type(v_packedInst_322_, v_a_324_, v_a_325_, v_a_326_, v_a_327_);
if (lean_obj_tag(v___x_336_) == 0)
{
lean_object* v_a_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_356_; 
v_a_337_ = lean_ctor_get(v___x_336_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_336_);
if (v_isSharedCheck_356_ == 0)
{
v___x_339_ = v___x_336_;
v_isShared_340_ = v_isSharedCheck_356_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_a_337_);
lean_dec(v___x_336_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_356_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_341_; uint8_t v___x_342_; 
v___x_341_ = ((lean_object*)(l_Lean_Meta_mkInstPiOfInstForall___closed__5));
v___x_342_ = l_Lean_Expr_isAppOf(v_a_337_, v___x_341_);
lean_dec(v_a_337_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
lean_del_object(v___x_339_);
lean_dec(v_type_323_);
v___x_343_ = lean_obj_once(&l_Lean_Meta_toPartialOrder___closed__1, &l_Lean_Meta_toPartialOrder___closed__1_once, _init_l_Lean_Meta_toPartialOrder___closed__1);
v___x_344_ = l_Lean_MessageData_ofExpr(v_packedInst_322_);
v___x_345_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_343_);
lean_ctor_set(v___x_345_, 1, v___x_344_);
v___x_346_ = l_Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0___redArg(v___x_345_, v_a_324_, v_a_325_, v_a_326_, v_a_327_);
return v___x_346_;
}
else
{
lean_object* v___x_347_; lean_object* v___x_349_; 
v___x_347_ = ((lean_object*)(l_Lean_Meta_toPartialOrder___closed__3));
if (v_isShared_340_ == 0)
{
lean_ctor_set_tag(v___x_339_, 1);
lean_ctor_set(v___x_339_, 0, v_packedInst_322_);
v___x_349_ = v___x_339_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_packedInst_322_);
v___x_349_ = v_reuseFailAlloc_355_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_350_ = lean_unsigned_to_nat(2u);
v___x_351_ = lean_mk_empty_array_with_capacity(v___x_350_);
v___x_352_ = lean_array_push(v___x_351_, v_type_323_);
v___x_353_ = lean_array_push(v___x_352_, v___x_349_);
v___x_354_ = l_Lean_Meta_mkAppOptM(v___x_347_, v___x_353_, v_a_324_, v_a_325_, v_a_326_, v_a_327_);
return v___x_354_;
}
}
}
}
else
{
lean_dec(v_type_323_);
lean_dec_ref(v_packedInst_322_);
return v___x_336_;
}
}
else
{
lean_object* v___x_357_; lean_object* v___x_359_; 
v___x_357_ = ((lean_object*)(l_Lean_Meta_toPartialOrder___closed__4));
if (v_isShared_333_ == 0)
{
lean_ctor_set_tag(v___x_332_, 1);
lean_ctor_set(v___x_332_, 0, v_packedInst_322_);
v___x_359_ = v___x_332_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_packedInst_322_);
v___x_359_ = v_reuseFailAlloc_365_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_360_ = lean_unsigned_to_nat(2u);
v___x_361_ = lean_mk_empty_array_with_capacity(v___x_360_);
v___x_362_ = lean_array_push(v___x_361_, v_type_323_);
v___x_363_ = lean_array_push(v___x_362_, v___x_359_);
v___x_364_ = l_Lean_Meta_mkAppOptM(v___x_357_, v___x_363_, v_a_324_, v_a_325_, v_a_326_, v_a_327_);
return v___x_364_;
}
}
}
}
else
{
lean_dec(v_type_323_);
lean_dec_ref(v_packedInst_322_);
return v___x_329_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_toPartialOrder___boxed(lean_object* v_packedInst_367_, lean_object* v_type_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Lean_Meta_toPartialOrder(v_packedInst_367_, v_type_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_);
lean_dec(v_a_372_);
lean_dec_ref(v_a_371_);
lean_dec(v_a_370_);
lean_dec_ref(v_a_369_);
return v_res_374_;
}
}
static lean_object* _init_l_Lean_Meta_mkInstCCPOPProd___closed__2(void){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_380_ = lean_box(0);
v___x_381_ = lean_unsigned_to_nat(4u);
v___x_382_ = lean_mk_empty_array_with_capacity(v___x_381_);
v___x_383_ = lean_array_push(v___x_382_, v___x_380_);
return v___x_383_;
}
}
static lean_object* _init_l_Lean_Meta_mkInstCCPOPProd___closed__3(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_384_ = lean_box(0);
v___x_385_ = lean_obj_once(&l_Lean_Meta_mkInstCCPOPProd___closed__2, &l_Lean_Meta_mkInstCCPOPProd___closed__2_once, _init_l_Lean_Meta_mkInstCCPOPProd___closed__2);
v___x_386_ = lean_array_push(v___x_385_, v___x_384_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInstCCPOPProd(lean_object* v_inst_u2081_387_, lean_object* v_inst_u2082_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_394_ = ((lean_object*)(l_Lean_Meta_mkInstCCPOPProd___closed__1));
v___x_395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_395_, 0, v_inst_u2081_387_);
v___x_396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_396_, 0, v_inst_u2082_388_);
v___x_397_ = lean_obj_once(&l_Lean_Meta_mkInstCCPOPProd___closed__3, &l_Lean_Meta_mkInstCCPOPProd___closed__3_once, _init_l_Lean_Meta_mkInstCCPOPProd___closed__3);
v___x_398_ = lean_array_push(v___x_397_, v___x_395_);
v___x_399_ = lean_array_push(v___x_398_, v___x_396_);
v___x_400_ = l_Lean_Meta_mkAppOptM(v___x_394_, v___x_399_, v_a_389_, v_a_390_, v_a_391_, v_a_392_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInstCCPOPProd___boxed(lean_object* v_inst_u2081_401_, lean_object* v_inst_u2082_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Lean_Meta_mkInstCCPOPProd(v_inst_u2081_401_, v_inst_u2082_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_);
lean_dec(v_a_406_);
lean_dec_ref(v_a_405_);
lean_dec(v_a_404_);
lean_dec_ref(v_a_403_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInstCompleteLatticePProd(lean_object* v_inst_u2081_414_, lean_object* v_inst_u2082_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_421_ = ((lean_object*)(l_Lean_Meta_mkInstCompleteLatticePProd___closed__1));
v___x_422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_422_, 0, v_inst_u2081_414_);
v___x_423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_423_, 0, v_inst_u2082_415_);
v___x_424_ = lean_obj_once(&l_Lean_Meta_mkInstCCPOPProd___closed__3, &l_Lean_Meta_mkInstCCPOPProd___closed__3_once, _init_l_Lean_Meta_mkInstCCPOPProd___closed__3);
v___x_425_ = lean_array_push(v___x_424_, v___x_422_);
v___x_426_ = lean_array_push(v___x_425_, v___x_423_);
v___x_427_ = l_Lean_Meta_mkAppOptM(v___x_421_, v___x_426_, v_a_416_, v_a_417_, v_a_418_, v_a_419_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInstCompleteLatticePProd___boxed(lean_object* v_inst_u2081_428_, lean_object* v_inst_u2082_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_Lean_Meta_mkInstCompleteLatticePProd(v_inst_u2081_428_, v_inst_u2082_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_);
lean_dec(v_a_433_);
lean_dec_ref(v_a_432_);
lean_dec(v_a_431_);
lean_dec_ref(v_a_430_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_mkPackedPPRodInstance_spec__3(lean_object* v_a_436_, lean_object* v_a_437_){
_start:
{
if (lean_obj_tag(v_a_436_) == 0)
{
lean_object* v___x_438_; 
v___x_438_ = l_List_reverse___redArg(v_a_437_);
return v___x_438_;
}
else
{
lean_object* v_head_439_; lean_object* v_tail_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_449_; 
v_head_439_ = lean_ctor_get(v_a_436_, 0);
v_tail_440_ = lean_ctor_get(v_a_436_, 1);
v_isSharedCheck_449_ = !lean_is_exclusive(v_a_436_);
if (v_isSharedCheck_449_ == 0)
{
v___x_442_ = v_a_436_;
v_isShared_443_ = v_isSharedCheck_449_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_tail_440_);
lean_inc(v_head_439_);
lean_dec(v_a_436_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_449_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_444_; lean_object* v___x_446_; 
v___x_444_ = l_Lean_MessageData_ofExpr(v_head_439_);
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 1, v_a_437_);
lean_ctor_set(v___x_442_, 0, v___x_444_);
v___x_446_ = v___x_442_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v___x_444_);
lean_ctor_set(v_reuseFailAlloc_448_, 1, v_a_437_);
v___x_446_ = v_reuseFailAlloc_448_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
v_a_436_ = v_tail_440_;
v_a_437_ = v___x_446_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkPackedPPRodInstance_spec__0(size_t v_sz_450_, size_t v_i_451_, lean_object* v_bs_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
uint8_t v___x_458_; 
v___x_458_ = lean_usize_dec_lt(v_i_451_, v_sz_450_);
if (v___x_458_ == 0)
{
lean_object* v___x_459_; 
v___x_459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_459_, 0, v_bs_452_);
return v___x_459_;
}
else
{
lean_object* v_v_460_; lean_object* v___x_461_; lean_object* v_bs_x27_462_; lean_object* v___x_463_; 
v_v_460_ = lean_array_uget(v_bs_452_, v_i_451_);
v___x_461_ = lean_unsigned_to_nat(0u);
v_bs_x27_462_ = lean_array_uset(v_bs_452_, v_i_451_, v___x_461_);
lean_inc(v___y_456_);
lean_inc_ref(v___y_455_);
lean_inc(v___y_454_);
lean_inc_ref(v___y_453_);
v___x_463_ = lean_infer_type(v_v_460_, v___y_453_, v___y_454_, v___y_455_, v___y_456_);
if (lean_obj_tag(v___x_463_) == 0)
{
lean_object* v_a_464_; size_t v___x_465_; size_t v___x_466_; lean_object* v___x_467_; 
v_a_464_ = lean_ctor_get(v___x_463_, 0);
lean_inc(v_a_464_);
lean_dec_ref_known(v___x_463_, 1);
v___x_465_ = ((size_t)1ULL);
v___x_466_ = lean_usize_add(v_i_451_, v___x_465_);
v___x_467_ = lean_array_uset(v_bs_x27_462_, v_i_451_, v_a_464_);
v_i_451_ = v___x_466_;
v_bs_452_ = v___x_467_;
goto _start;
}
else
{
lean_object* v_a_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_476_; 
lean_dec_ref(v_bs_x27_462_);
v_a_469_ = lean_ctor_get(v___x_463_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_476_ == 0)
{
v___x_471_ = v___x_463_;
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_a_469_);
lean_dec(v___x_463_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_474_; 
if (v_isShared_472_ == 0)
{
v___x_474_ = v___x_471_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_a_469_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkPackedPPRodInstance_spec__0___boxed(lean_object* v_sz_477_, lean_object* v_i_478_, lean_object* v_bs_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_){
_start:
{
size_t v_sz_boxed_485_; size_t v_i_boxed_486_; lean_object* v_res_487_; 
v_sz_boxed_485_ = lean_unbox_usize(v_sz_477_);
lean_dec(v_sz_477_);
v_i_boxed_486_ = lean_unbox_usize(v_i_478_);
lean_dec(v_i_478_);
v_res_487_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkPackedPPRodInstance_spec__0(v_sz_boxed_485_, v_i_boxed_486_, v_bs_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_);
lean_dec(v___y_483_);
lean_dec_ref(v___y_482_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
return v_res_487_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkPackedPPRodInstance_spec__1(lean_object* v_as_488_, size_t v_i_489_, size_t v_stop_490_){
_start:
{
uint8_t v___x_491_; 
v___x_491_ = lean_usize_dec_eq(v_i_489_, v_stop_490_);
if (v___x_491_ == 0)
{
lean_object* v___x_492_; lean_object* v___x_493_; uint8_t v___x_494_; 
v___x_492_ = lean_array_uget_borrowed(v_as_488_, v_i_489_);
v___x_493_ = ((lean_object*)(l_Lean_Meta_mkInstPiOfInstForall___closed__3));
v___x_494_ = l_Lean_Expr_isAppOf(v___x_492_, v___x_493_);
if (v___x_494_ == 0)
{
uint8_t v___x_495_; 
v___x_495_ = 1;
return v___x_495_;
}
else
{
size_t v___x_496_; size_t v___x_497_; 
v___x_496_ = ((size_t)1ULL);
v___x_497_ = lean_usize_add(v_i_489_, v___x_496_);
v_i_489_ = v___x_497_;
goto _start;
}
}
else
{
uint8_t v___x_499_; 
v___x_499_ = 0;
return v___x_499_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkPackedPPRodInstance_spec__1___boxed(lean_object* v_as_500_, lean_object* v_i_501_, lean_object* v_stop_502_){
_start:
{
size_t v_i_boxed_503_; size_t v_stop_boxed_504_; uint8_t v_res_505_; lean_object* v_r_506_; 
v_i_boxed_503_ = lean_unbox_usize(v_i_501_);
lean_dec(v_i_501_);
v_stop_boxed_504_ = lean_unbox_usize(v_stop_502_);
lean_dec(v_stop_502_);
v_res_505_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkPackedPPRodInstance_spec__1(v_as_500_, v_i_boxed_503_, v_stop_boxed_504_);
lean_dec_ref(v_as_500_);
v_r_506_ = lean_box(v_res_505_);
return v_r_506_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkPackedPPRodInstance_spec__2(uint8_t v___x_507_, lean_object* v_as_508_, size_t v_i_509_, size_t v_stop_510_){
_start:
{
uint8_t v___x_515_; 
v___x_515_ = lean_usize_dec_eq(v_i_509_, v_stop_510_);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; lean_object* v___x_517_; uint8_t v___x_518_; 
v___x_516_ = lean_array_uget_borrowed(v_as_508_, v_i_509_);
v___x_517_ = ((lean_object*)(l_Lean_Meta_mkInstPiOfInstForall___closed__5));
v___x_518_ = l_Lean_Expr_isAppOf(v___x_516_, v___x_517_);
if (v___x_518_ == 0)
{
if (v___x_507_ == 0)
{
goto v___jp_511_;
}
else
{
return v___x_507_;
}
}
else
{
goto v___jp_511_;
}
}
else
{
uint8_t v___x_519_; 
v___x_519_ = 0;
return v___x_519_;
}
v___jp_511_:
{
size_t v___x_512_; size_t v___x_513_; 
v___x_512_ = ((size_t)1ULL);
v___x_513_ = lean_usize_add(v_i_509_, v___x_512_);
v_i_509_ = v___x_513_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkPackedPPRodInstance_spec__2___boxed(lean_object* v___x_520_, lean_object* v_as_521_, lean_object* v_i_522_, lean_object* v_stop_523_){
_start:
{
uint8_t v___x_1163__boxed_524_; size_t v_i_boxed_525_; size_t v_stop_boxed_526_; uint8_t v_res_527_; lean_object* v_r_528_; 
v___x_1163__boxed_524_ = lean_unbox(v___x_520_);
v_i_boxed_525_ = lean_unbox_usize(v_i_522_);
lean_dec(v_i_522_);
v_stop_boxed_526_ = lean_unbox_usize(v_stop_523_);
lean_dec(v_stop_523_);
v_res_527_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkPackedPPRodInstance_spec__2(v___x_1163__boxed_524_, v_as_521_, v_i_boxed_525_, v_stop_boxed_526_);
lean_dec_ref(v_as_521_);
v_r_528_ = lean_box(v_res_527_);
return v_r_528_;
}
}
static lean_object* _init_l_Lean_Meta_mkPackedPPRodInstance___closed__3(void){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = ((lean_object*)(l_Lean_Meta_mkPackedPPRodInstance___closed__2));
v___x_533_ = l_Lean_stringToMessageData(v___x_532_);
return v___x_533_;
}
}
static lean_object* _init_l_Lean_Meta_mkPackedPPRodInstance___closed__5(void){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = ((lean_object*)(l_Lean_Meta_mkPackedPPRodInstance___closed__4));
v___x_536_ = l_Lean_stringToMessageData(v___x_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPackedPPRodInstance(lean_object* v_insts_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_){
_start:
{
lean_object* v___x_543_; size_t v_sz_544_; size_t v___x_545_; lean_object* v___x_546_; 
v___x_543_ = l_Lean_instInhabitedExpr;
v_sz_544_ = lean_array_size(v_insts_537_);
v___x_545_ = ((size_t)0ULL);
lean_inc_ref(v_insts_537_);
v___x_546_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkPackedPPRodInstance_spec__0(v_sz_544_, v___x_545_, v_insts_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_);
if (lean_obj_tag(v___x_546_) == 0)
{
lean_object* v_a_547_; lean_object* v___x_554_; lean_object* v___x_555_; uint8_t v___x_556_; 
v_a_547_ = lean_ctor_get(v___x_546_, 0);
lean_inc(v_a_547_);
lean_dec_ref_known(v___x_546_, 1);
v___x_554_ = lean_unsigned_to_nat(0u);
v___x_555_ = lean_array_get_size(v_a_547_);
v___x_556_ = lean_nat_dec_lt(v___x_554_, v___x_555_);
if (v___x_556_ == 0)
{
lean_dec(v_a_547_);
goto v___jp_551_;
}
else
{
if (v___x_556_ == 0)
{
lean_dec(v_a_547_);
goto v___jp_551_;
}
else
{
size_t v___x_557_; uint8_t v___x_558_; 
v___x_557_ = lean_usize_of_nat(v___x_555_);
v___x_558_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkPackedPPRodInstance_spec__1(v_a_547_, v___x_545_, v___x_557_);
if (v___x_558_ == 0)
{
lean_dec(v_a_547_);
goto v___jp_551_;
}
else
{
if (v___x_556_ == 0)
{
lean_dec(v_a_547_);
goto v___jp_548_;
}
else
{
if (v___x_556_ == 0)
{
lean_dec(v_a_547_);
goto v___jp_548_;
}
else
{
uint8_t v___x_559_; 
v___x_559_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkPackedPPRodInstance_spec__2(v___x_558_, v_a_547_, v___x_545_, v___x_557_);
if (v___x_559_ == 0)
{
lean_dec(v_a_547_);
goto v___jp_548_;
}
else
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_560_ = lean_obj_once(&l_Lean_Meta_mkPackedPPRodInstance___closed__3, &l_Lean_Meta_mkPackedPPRodInstance___closed__3_once, _init_l_Lean_Meta_mkPackedPPRodInstance___closed__3);
v___x_561_ = lean_array_to_list(v_a_547_);
v___x_562_ = lean_box(0);
v___x_563_ = l_List_mapTR_loop___at___00Lean_Meta_mkPackedPPRodInstance_spec__3(v___x_561_, v___x_562_);
v___x_564_ = l_Lean_MessageData_ofList(v___x_563_);
v___x_565_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_565_, 0, v___x_560_);
lean_ctor_set(v___x_565_, 1, v___x_564_);
v___x_566_ = lean_obj_once(&l_Lean_Meta_mkPackedPPRodInstance___closed__5, &l_Lean_Meta_mkPackedPPRodInstance___closed__5_once, _init_l_Lean_Meta_mkPackedPPRodInstance___closed__5);
v___x_567_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_567_, 0, v___x_565_);
lean_ctor_set(v___x_567_, 1, v___x_566_);
v___x_568_ = lean_array_to_list(v_insts_537_);
v___x_569_ = l_List_mapTR_loop___at___00Lean_Meta_mkPackedPPRodInstance_spec__3(v___x_568_, v___x_562_);
v___x_570_ = l_Lean_MessageData_ofList(v___x_569_);
v___x_571_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_571_, 0, v___x_567_);
lean_ctor_set(v___x_571_, 1, v___x_570_);
v___x_572_ = l_Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0___redArg(v___x_571_, v_a_538_, v_a_539_, v_a_540_, v_a_541_);
return v___x_572_;
}
}
}
}
}
}
v___jp_548_:
{
lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_549_ = ((lean_object*)(l_Lean_Meta_mkPackedPPRodInstance___closed__0));
v___x_550_ = l_Lean_Meta_PProdN_genMk___redArg(v___x_543_, v___x_549_, v_insts_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_);
return v___x_550_;
}
v___jp_551_:
{
lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_552_ = ((lean_object*)(l_Lean_Meta_mkPackedPPRodInstance___closed__1));
v___x_553_ = l_Lean_Meta_PProdN_genMk___redArg(v___x_543_, v___x_552_, v_insts_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_);
return v___x_553_;
}
}
else
{
lean_object* v_a_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_580_; 
lean_dec_ref(v_insts_537_);
v_a_573_ = lean_ctor_get(v___x_546_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_580_ == 0)
{
v___x_575_ = v___x_546_;
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_a_573_);
lean_dec(v___x_546_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_578_; 
if (v_isShared_576_ == 0)
{
v___x_578_ = v___x_575_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_a_573_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPackedPPRodInstance___boxed(lean_object* v_insts_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Lean_Meta_mkPackedPPRodInstance(v_insts_581_, v_a_582_, v_a_583_, v_a_584_, v_a_585_);
lean_dec(v_a_585_);
lean_dec_ref(v_a_584_);
lean_dec(v_a_583_);
lean_dec_ref(v_a_582_);
return v_res_587_;
}
}
lean_object* runtime_initialize_Lean_Meta_PProdN(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Init_Internal_Order_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Order(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
