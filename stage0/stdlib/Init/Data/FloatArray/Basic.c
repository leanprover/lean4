// Lean compiler output
// Module: Init.Data.FloatArray.Basic
// Imports: public import Init.Data.Float.Float import Init.Ext public import Init.GetElem public import Init.Data.ToString.Extra
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
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_float_beq(double, double);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Float_toString___boxed(lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_List_toString___redArg(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_float_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_FloatArray_mk___boxed(lean_object*);
lean_object* lean_float_array_data(lean_object*);
LEAN_EXPORT lean_object* l_FloatArray_data___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00FloatArray_instBEq_beq_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00FloatArray_instBEq_beq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_FloatArray_instBEq_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_FloatArray_instBEq_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00FloatArray_instBEq_beq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00FloatArray_instBEq_beq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_FloatArray_instBEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_FloatArray_instBEq_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_FloatArray_instBEq___closed__0 = (const lean_object*)&l_FloatArray_instBEq___closed__0_value;
LEAN_EXPORT const lean_object* l_FloatArray_instBEq = (const lean_object*)&l_FloatArray_instBEq___closed__0_value;
lean_object* lean_mk_empty_float_array(lean_object*);
LEAN_EXPORT lean_object* l_FloatArray_emptyWithCapacity___boxed(lean_object*);
static lean_once_cell_t l_FloatArray_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_FloatArray_empty___closed__0;
LEAN_EXPORT lean_object* l_FloatArray_empty;
LEAN_EXPORT lean_object* l_FloatArray_instInhabited;
LEAN_EXPORT lean_object* l_FloatArray_instEmptyCollection;
lean_object* lean_float_array_push(lean_object*, double);
LEAN_EXPORT lean_object* l_FloatArray_push___boxed(lean_object*, lean_object*);
lean_object* lean_float_array_size(lean_object*);
LEAN_EXPORT lean_object* l_FloatArray_size___boxed(lean_object*);
size_t lean_sarray_size(lean_object*);
LEAN_EXPORT lean_object* l_FloatArray_usize___boxed(lean_object*);
double lean_float_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_FloatArray_uget___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_FloatArray_get___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_FloatArray_get___auto__1___closed__0 = (const lean_object*)&l_FloatArray_get___auto__1___closed__0_value;
static const lean_string_object l_FloatArray_get___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_FloatArray_get___auto__1___closed__1 = (const lean_object*)&l_FloatArray_get___auto__1___closed__1_value;
static const lean_string_object l_FloatArray_get___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_FloatArray_get___auto__1___closed__2 = (const lean_object*)&l_FloatArray_get___auto__1___closed__2_value;
static const lean_string_object l_FloatArray_get___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_FloatArray_get___auto__1___closed__3 = (const lean_object*)&l_FloatArray_get___auto__1___closed__3_value;
static const lean_ctor_object l_FloatArray_get___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_FloatArray_get___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_FloatArray_get___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_FloatArray_get___auto__1___closed__4_value_aux_0),((lean_object*)&l_FloatArray_get___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_FloatArray_get___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_FloatArray_get___auto__1___closed__4_value_aux_1),((lean_object*)&l_FloatArray_get___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_FloatArray_get___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_FloatArray_get___auto__1___closed__4_value_aux_2),((lean_object*)&l_FloatArray_get___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_FloatArray_get___auto__1___closed__4 = (const lean_object*)&l_FloatArray_get___auto__1___closed__4_value;
static const lean_array_object l_FloatArray_get___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_FloatArray_get___auto__1___closed__5 = (const lean_object*)&l_FloatArray_get___auto__1___closed__5_value;
static const lean_string_object l_FloatArray_get___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_FloatArray_get___auto__1___closed__6 = (const lean_object*)&l_FloatArray_get___auto__1___closed__6_value;
static const lean_ctor_object l_FloatArray_get___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_FloatArray_get___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_FloatArray_get___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_FloatArray_get___auto__1___closed__7_value_aux_0),((lean_object*)&l_FloatArray_get___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_FloatArray_get___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_FloatArray_get___auto__1___closed__7_value_aux_1),((lean_object*)&l_FloatArray_get___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_FloatArray_get___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_FloatArray_get___auto__1___closed__7_value_aux_2),((lean_object*)&l_FloatArray_get___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_FloatArray_get___auto__1___closed__7 = (const lean_object*)&l_FloatArray_get___auto__1___closed__7_value;
static const lean_string_object l_FloatArray_get___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_FloatArray_get___auto__1___closed__8 = (const lean_object*)&l_FloatArray_get___auto__1___closed__8_value;
static const lean_ctor_object l_FloatArray_get___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_FloatArray_get___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_FloatArray_get___auto__1___closed__9 = (const lean_object*)&l_FloatArray_get___auto__1___closed__9_value;
static const lean_string_object l_FloatArray_get___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "tacticGet_elem_tactic"};
static const lean_object* l_FloatArray_get___auto__1___closed__10 = (const lean_object*)&l_FloatArray_get___auto__1___closed__10_value;
static const lean_ctor_object l_FloatArray_get___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_FloatArray_get___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(141, 31, 109, 153, 11, 229, 201, 51)}};
static const lean_object* l_FloatArray_get___auto__1___closed__11 = (const lean_object*)&l_FloatArray_get___auto__1___closed__11_value;
static const lean_string_object l_FloatArray_get___auto__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "get_elem_tactic"};
static const lean_object* l_FloatArray_get___auto__1___closed__12 = (const lean_object*)&l_FloatArray_get___auto__1___closed__12_value;
static lean_once_cell_t l_FloatArray_get___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_FloatArray_get___auto__1___closed__13;
static lean_once_cell_t l_FloatArray_get___auto__1___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_FloatArray_get___auto__1___closed__14;
static lean_once_cell_t l_FloatArray_get___auto__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_FloatArray_get___auto__1___closed__15;
static lean_once_cell_t l_FloatArray_get___auto__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_FloatArray_get___auto__1___closed__16;
static lean_once_cell_t l_FloatArray_get___auto__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_FloatArray_get___auto__1___closed__17;
static lean_once_cell_t l_FloatArray_get___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_FloatArray_get___auto__1___closed__18;
static lean_once_cell_t l_FloatArray_get___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_FloatArray_get___auto__1___closed__19;
static lean_once_cell_t l_FloatArray_get___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_FloatArray_get___auto__1___closed__20;
static lean_once_cell_t l_FloatArray_get___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_FloatArray_get___auto__1___closed__21;
LEAN_EXPORT lean_object* l_FloatArray_get___auto__1;
double lean_float_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_FloatArray_get___boxed(lean_object*, lean_object*, lean_object*);
double lean_float_array_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_FloatArray_get_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_FloatArray_get_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_FloatArray_get_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT double l_FloatArray_instGetElemNatFloatLtSize___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_FloatArray_instGetElemNatFloatLtSize___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_FloatArray_instGetElemNatFloatLtSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_FloatArray_instGetElemNatFloatLtSize___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_FloatArray_instGetElemNatFloatLtSize___closed__0 = (const lean_object*)&l_FloatArray_instGetElemNatFloatLtSize___closed__0_value;
LEAN_EXPORT const lean_object* l_FloatArray_instGetElemNatFloatLtSize = (const lean_object*)&l_FloatArray_instGetElemNatFloatLtSize___closed__0_value;
LEAN_EXPORT double l_FloatArray_instGetElemUSizeFloatLtNatToNatSize___lam__0(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_FloatArray_instGetElemUSizeFloatLtNatToNatSize___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_FloatArray_instGetElemUSizeFloatLtNatToNatSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_FloatArray_instGetElemUSizeFloatLtNatToNatSize___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_FloatArray_instGetElemUSizeFloatLtNatToNatSize___closed__0 = (const lean_object*)&l_FloatArray_instGetElemUSizeFloatLtNatToNatSize___closed__0_value;
LEAN_EXPORT const lean_object* l_FloatArray_instGetElemUSizeFloatLtNatToNatSize = (const lean_object*)&l_FloatArray_instGetElemUSizeFloatLtNatToNatSize___closed__0_value;
LEAN_EXPORT lean_object* l_FloatArray_uset___auto__1;
lean_object* lean_float_array_uset(lean_object*, size_t, double);
LEAN_EXPORT lean_object* l_FloatArray_uset___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_FloatArray_set___auto__1;
lean_object* lean_float_array_fset(lean_object*, lean_object*, double);
LEAN_EXPORT lean_object* l_FloatArray_set___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_float_array_set(lean_object*, lean_object*, double);
LEAN_EXPORT lean_object* l_FloatArray_set_x21___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_sarray_mark_linear(lean_object*);
LEAN_EXPORT lean_object* l_FloatArray_markLinear___boxed(lean_object*);
lean_object* lean_sarray_propagate_mark(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_FloatArray_propagateMark___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_FloatArray_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_FloatArray_isEmpty___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_toList_loop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_toList_loop___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_FloatArray_toList(lean_object*);
LEAN_EXPORT lean_object* l_FloatArray_toList___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg___lam__0(lean_object*, size_t, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_FloatArray_forInUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_FloatArray_forInUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_FloatArray_instForInFloatOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_FloatArray_instForInFloatOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_FloatArray_instForInFloatOfMonad(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg___lam__0(size_t, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_FloatArray_foldlMUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_FloatArray_foldlMUnsafe___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_FloatArray_foldlMUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_FloatArray_foldlMUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_FloatArray_foldl___redArg___lam__0(lean_object*, lean_object*, double);
LEAN_EXPORT lean_object* l_FloatArray_foldl___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_FloatArray_foldl___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_FloatArray_foldl___redArg___closed__0 = (const lean_object*)&l_FloatArray_foldl___redArg___closed__0_value;
static const lean_closure_object l_FloatArray_foldl___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_FloatArray_foldl___redArg___closed__1 = (const lean_object*)&l_FloatArray_foldl___redArg___closed__1_value;
static const lean_closure_object l_FloatArray_foldl___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_FloatArray_foldl___redArg___closed__2 = (const lean_object*)&l_FloatArray_foldl___redArg___closed__2_value;
static const lean_closure_object l_FloatArray_foldl___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_FloatArray_foldl___redArg___closed__3 = (const lean_object*)&l_FloatArray_foldl___redArg___closed__3_value;
static const lean_closure_object l_FloatArray_foldl___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_FloatArray_foldl___redArg___closed__4 = (const lean_object*)&l_FloatArray_foldl___redArg___closed__4_value;
static const lean_closure_object l_FloatArray_foldl___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_FloatArray_foldl___redArg___closed__5 = (const lean_object*)&l_FloatArray_foldl___redArg___closed__5_value;
static const lean_closure_object l_FloatArray_foldl___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_FloatArray_foldl___redArg___closed__6 = (const lean_object*)&l_FloatArray_foldl___redArg___closed__6_value;
static const lean_ctor_object l_FloatArray_foldl___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_FloatArray_foldl___redArg___closed__0_value),((lean_object*)&l_FloatArray_foldl___redArg___closed__1_value)}};
static const lean_object* l_FloatArray_foldl___redArg___closed__7 = (const lean_object*)&l_FloatArray_foldl___redArg___closed__7_value;
static const lean_ctor_object l_FloatArray_foldl___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_FloatArray_foldl___redArg___closed__7_value),((lean_object*)&l_FloatArray_foldl___redArg___closed__2_value),((lean_object*)&l_FloatArray_foldl___redArg___closed__3_value),((lean_object*)&l_FloatArray_foldl___redArg___closed__4_value),((lean_object*)&l_FloatArray_foldl___redArg___closed__5_value)}};
static const lean_object* l_FloatArray_foldl___redArg___closed__8 = (const lean_object*)&l_FloatArray_foldl___redArg___closed__8_value;
static const lean_ctor_object l_FloatArray_foldl___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_FloatArray_foldl___redArg___closed__8_value),((lean_object*)&l_FloatArray_foldl___redArg___closed__6_value)}};
static const lean_object* l_FloatArray_foldl___redArg___closed__9 = (const lean_object*)&l_FloatArray_foldl___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_FloatArray_foldl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_FloatArray_foldl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_FloatArray_foldl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_FloatArray_foldl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__List_toFloatArray_loop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__List_toFloatArray_loop___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_toFloatArray(lean_object*);
LEAN_EXPORT lean_object* l_List_toFloatArray___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instToStringFloatArray___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringFloatArray___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instToStringFloatArray___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float_toString___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instToStringFloatArray___closed__0 = (const lean_object*)&l_instToStringFloatArray___closed__0_value;
static const lean_closure_object l_instToStringFloatArray___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringFloatArray___lam__0___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_instToStringFloatArray___closed__0_value)} };
static const lean_object* l_instToStringFloatArray___closed__1 = (const lean_object*)&l_instToStringFloatArray___closed__1_value;
LEAN_EXPORT const lean_object* l_instToStringFloatArray = (const lean_object*)&l_instToStringFloatArray___closed__1_value;
LEAN_EXPORT void l_FloatArray_mk_0interp(lean_interpreter_value* stack)
{
lean_object* v_data_1_ = stack[0].m_obj;
lean_object* v_res_2_;
v_res_2_ = lean_float_array_mk(v_data_1_);
stack->m_obj
 = v_res_2_;
}
LEAN_EXPORT lean_object* l_FloatArray_mk___boxed(lean_object* v_data_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lean_float_array_mk(v_data_3_);
return v_res_4_;
}
}
LEAN_EXPORT void l_FloatArray_data_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_5_ = stack[0].m_obj;
lean_object* v_res_6_;
v_res_6_ = lean_float_array_data(v_self_5_);
stack->m_obj
 = v_res_6_;
}
LEAN_EXPORT lean_object* l_FloatArray_data___boxed(lean_object* v_self_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = lean_float_array_data(v_self_7_);
return v_res_8_;
}
}
uint8_t l_Array_isEqvAux___at___00FloatArray_instBEq_beq_spec__0___redArg(lean_object* v_xs_9_, lean_object* v_ys_10_, lean_object* v_x_11_){
_start:
{
lean_object* v_zero_12_; uint8_t v_isZero_13_; 
v_zero_12_ = lean_unsigned_to_nat(0u);
v_isZero_13_ = lean_nat_dec_eq(v_x_11_, v_zero_12_);
if (v_isZero_13_ == 1)
{
lean_dec(v_x_11_);
return v_isZero_13_;
}
else
{
lean_object* v_one_14_; lean_object* v_n_15_; lean_object* v___x_16_; lean_object* v___x_17_; double v___x_18_; double v___x_19_; uint8_t v___x_20_; 
v_one_14_ = lean_unsigned_to_nat(1u);
v_n_15_ = lean_nat_sub(v_x_11_, v_one_14_);
lean_dec(v_x_11_);
v___x_16_ = lean_array_fget_borrowed(v_xs_9_, v_n_15_);
v___x_17_ = lean_array_fget_borrowed(v_ys_10_, v_n_15_);
v___x_18_ = lean_unbox_float(v___x_16_);
v___x_19_ = lean_unbox_float(v___x_17_);
v___x_20_ = lean_float_beq(v___x_18_, v___x_19_);
if (v___x_20_ == 0)
{
lean_dec(v_n_15_);
return v___x_20_;
}
else
{
v_x_11_ = v_n_15_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_Array_isEqvAux___at___00FloatArray_instBEq_beq_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_9_ = stack[0].m_obj;
lean_object* v_ys_10_ = stack[1].m_obj;
lean_object* v_x_11_ = stack[2].m_obj;
uint8_t v_res_22_;
v_res_22_ = l_Array_isEqvAux___at___00FloatArray_instBEq_beq_spec__0___redArg(v_xs_9_, v_ys_10_, v_x_11_);
stack->m_num = v_res_22_;
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00FloatArray_instBEq_beq_spec__0___redArg___boxed(lean_object* v_xs_23_, lean_object* v_ys_24_, lean_object* v_x_25_){
_start:
{
uint8_t v_res_26_; lean_object* v_r_27_; 
v_res_26_ = l_Array_isEqvAux___at___00FloatArray_instBEq_beq_spec__0___redArg(v_xs_23_, v_ys_24_, v_x_25_);
lean_dec_ref(v_ys_24_);
lean_dec_ref(v_xs_23_);
v_r_27_ = lean_box(v_res_26_);
return v_r_27_;
}
}
uint8_t l_FloatArray_instBEq_beq(lean_object* v_x_28_, lean_object* v_x_29_){
_start:
{
lean_object* v_data_30_; lean_object* v_data_31_; lean_object* v___x_32_; lean_object* v___x_33_; uint8_t v___x_34_; 
v_data_30_ = lean_float_array_data(v_x_28_);
v_data_31_ = lean_float_array_data(v_x_29_);
v___x_32_ = lean_array_get_size(v_data_30_);
v___x_33_ = lean_array_get_size(v_data_31_);
v___x_34_ = lean_nat_dec_eq(v___x_32_, v___x_33_);
if (v___x_34_ == 0)
{
lean_dec_ref(v_data_31_);
lean_dec_ref(v_data_30_);
return v___x_34_;
}
else
{
uint8_t v___x_35_; 
v___x_35_ = l_Array_isEqvAux___at___00FloatArray_instBEq_beq_spec__0___redArg(v_data_30_, v_data_31_, v___x_32_);
lean_dec_ref(v_data_31_);
lean_dec_ref(v_data_30_);
return v___x_35_;
}
}
}
LEAN_EXPORT void l_FloatArray_instBEq_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_28_ = stack[0].m_obj;
lean_object* v_x_29_ = stack[1].m_obj;
uint8_t v_res_36_;
v_res_36_ = l_FloatArray_instBEq_beq(v_x_28_, v_x_29_);
stack->m_num = v_res_36_;
}
LEAN_EXPORT lean_object* l_FloatArray_instBEq_beq___boxed(lean_object* v_x_37_, lean_object* v_x_38_){
_start:
{
uint8_t v_res_39_; lean_object* v_r_40_; 
v_res_39_ = l_FloatArray_instBEq_beq(v_x_37_, v_x_38_);
v_r_40_ = lean_box(v_res_39_);
return v_r_40_;
}
}
uint8_t l_Array_isEqvAux___at___00FloatArray_instBEq_beq_spec__0(lean_object* v_xs_41_, lean_object* v_ys_42_, lean_object* v_hsz_43_, lean_object* v_x_44_, lean_object* v_x_45_){
_start:
{
uint8_t v___x_46_; 
v___x_46_ = l_Array_isEqvAux___at___00FloatArray_instBEq_beq_spec__0___redArg(v_xs_41_, v_ys_42_, v_x_44_);
return v___x_46_;
}
}
LEAN_EXPORT void l_Array_isEqvAux___at___00FloatArray_instBEq_beq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_41_ = stack[0].m_obj;
lean_object* v_ys_42_ = stack[1].m_obj;
lean_object* v_x_44_ = stack[3].m_obj;
uint8_t v_res_47_;
v_res_47_ = l_Array_isEqvAux___at___00FloatArray_instBEq_beq_spec__0(v_xs_41_, v_ys_42_, lean_box(0), v_x_44_, lean_box(0));
stack->m_num = v_res_47_;
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00FloatArray_instBEq_beq_spec__0___boxed(lean_object* v_xs_48_, lean_object* v_ys_49_, lean_object* v_hsz_50_, lean_object* v_x_51_, lean_object* v_x_52_){
_start:
{
uint8_t v_res_53_; lean_object* v_r_54_; 
v_res_53_ = l_Array_isEqvAux___at___00FloatArray_instBEq_beq_spec__0(v_xs_48_, v_ys_49_, v_hsz_50_, v_x_51_, v_x_52_);
lean_dec_ref(v_ys_49_);
lean_dec_ref(v_xs_48_);
v_r_54_ = lean_box(v_res_53_);
return v_r_54_;
}
}
LEAN_EXPORT void l_FloatArray_emptyWithCapacity_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_57_ = stack[0].m_obj;
lean_object* v_res_58_;
v_res_58_ = lean_mk_empty_float_array(v_c_57_);
stack->m_obj
 = v_res_58_;
}
LEAN_EXPORT lean_object* l_FloatArray_emptyWithCapacity___boxed(lean_object* v_c_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = lean_mk_empty_float_array(v_c_59_);
lean_dec(v_c_59_);
return v_res_60_;
}
}
static lean_object* _init_l_FloatArray_empty___closed__0(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_61_ = lean_unsigned_to_nat(0u);
v___x_62_ = lean_mk_empty_float_array(v___x_61_);
return v___x_62_;
}
}
static lean_object* _init_l_FloatArray_empty(void){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = lean_obj_once(&l_FloatArray_empty___closed__0, &l_FloatArray_empty___closed__0_once, _init_l_FloatArray_empty___closed__0);
return v___x_63_;
}
}
static lean_object* _init_l_FloatArray_instInhabited(void){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = l_FloatArray_empty;
return v___x_64_;
}
}
static lean_object* _init_l_FloatArray_instEmptyCollection(void){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l_FloatArray_empty;
return v___x_65_;
}
}
LEAN_EXPORT void l_FloatArray_push_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_66_ = stack[0].m_obj;
double v_a_00___x40___internal___hyg_67_ = stack[1].m_float;
lean_object* v_res_68_;
v_res_68_ = lean_float_array_push(v_a_00___x40___internal___hyg_66_, v_a_00___x40___internal___hyg_67_);
stack->m_obj
 = v_res_68_;
}
LEAN_EXPORT lean_object* l_FloatArray_push___boxed(lean_object* v_a_00___x40___internal___hyg_69_, lean_object* v_a_00___x40___internal___hyg_70_){
_start:
{
double v_a_00___x40___internal___hyg_2__boxed_71_; lean_object* v_res_72_; 
v_a_00___x40___internal___hyg_2__boxed_71_ = lean_unbox_float(v_a_00___x40___internal___hyg_70_);
lean_dec_ref(v_a_00___x40___internal___hyg_70_);
v_res_72_ = lean_float_array_push(v_a_00___x40___internal___hyg_69_, v_a_00___x40___internal___hyg_2__boxed_71_);
return v_res_72_;
}
}
LEAN_EXPORT void l_FloatArray_size_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_73_ = stack[0].m_obj;
lean_object* v_res_74_;
v_res_74_ = lean_float_array_size(v_a_00___x40___internal___hyg_73_);
stack->m_obj
 = v_res_74_;
}
LEAN_EXPORT lean_object* l_FloatArray_size___boxed(lean_object* v_a_00___x40___internal___hyg_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = lean_float_array_size(v_a_00___x40___internal___hyg_75_);
lean_dec_ref(v_a_00___x40___internal___hyg_75_);
return v_res_76_;
}
}
LEAN_EXPORT void l_FloatArray_usize_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_77_ = stack[0].m_obj;
size_t v_res_78_;
v_res_78_ = lean_sarray_size(v_a_77_);
stack->m_num = v_res_78_;
}
LEAN_EXPORT lean_object* l_FloatArray_usize___boxed(lean_object* v_a_79_){
_start:
{
size_t v_res_80_; lean_object* v_r_81_; 
v_res_80_ = lean_sarray_size(v_a_79_);
lean_dec_ref(v_a_79_);
v_r_81_ = lean_box_usize(v_res_80_);
return v_r_81_;
}
}
LEAN_EXPORT void l_FloatArray_uget_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_82_ = stack[0].m_obj;
size_t v_i_83_ = stack[1].m_num;
double v_res_85_;
v_res_85_ = lean_float_array_uget(v_a_82_, v_i_83_);
stack->m_float
 = v_res_85_;
}
LEAN_EXPORT lean_object* l_FloatArray_uget___boxed(lean_object* v_a_86_, lean_object* v_i_87_, lean_object* v_a_00___x40___internal___hyg_88_){
_start:
{
size_t v_i_boxed_89_; double v_res_90_; lean_object* v_r_91_; 
v_i_boxed_89_ = lean_unbox_usize(v_i_87_);
lean_dec(v_i_87_);
v_res_90_ = lean_float_array_uget(v_a_86_, v_i_boxed_89_);
lean_dec_ref(v_a_86_);
v_r_91_ = lean_box_float(v_res_90_);
return v_r_91_;
}
}
static lean_object* _init_l_FloatArray_get___auto__1___closed__13(void){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_116_ = ((lean_object*)(l_FloatArray_get___auto__1___closed__12));
v___x_117_ = l_Lean_mkAtom(v___x_116_);
return v___x_117_;
}
}
static lean_object* _init_l_FloatArray_get___auto__1___closed__14(void){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_118_ = lean_obj_once(&l_FloatArray_get___auto__1___closed__13, &l_FloatArray_get___auto__1___closed__13_once, _init_l_FloatArray_get___auto__1___closed__13);
v___x_119_ = ((lean_object*)(l_FloatArray_get___auto__1___closed__5));
v___x_120_ = lean_array_push(v___x_119_, v___x_118_);
return v___x_120_;
}
}
static lean_object* _init_l_FloatArray_get___auto__1___closed__15(void){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_121_ = lean_obj_once(&l_FloatArray_get___auto__1___closed__14, &l_FloatArray_get___auto__1___closed__14_once, _init_l_FloatArray_get___auto__1___closed__14);
v___x_122_ = ((lean_object*)(l_FloatArray_get___auto__1___closed__11));
v___x_123_ = lean_box(2);
v___x_124_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_124_, 0, v___x_123_);
lean_ctor_set(v___x_124_, 1, v___x_122_);
lean_ctor_set(v___x_124_, 2, v___x_121_);
return v___x_124_;
}
}
static lean_object* _init_l_FloatArray_get___auto__1___closed__16(void){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_125_ = lean_obj_once(&l_FloatArray_get___auto__1___closed__15, &l_FloatArray_get___auto__1___closed__15_once, _init_l_FloatArray_get___auto__1___closed__15);
v___x_126_ = ((lean_object*)(l_FloatArray_get___auto__1___closed__5));
v___x_127_ = lean_array_push(v___x_126_, v___x_125_);
return v___x_127_;
}
}
static lean_object* _init_l_FloatArray_get___auto__1___closed__17(void){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_128_ = lean_obj_once(&l_FloatArray_get___auto__1___closed__16, &l_FloatArray_get___auto__1___closed__16_once, _init_l_FloatArray_get___auto__1___closed__16);
v___x_129_ = ((lean_object*)(l_FloatArray_get___auto__1___closed__9));
v___x_130_ = lean_box(2);
v___x_131_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
lean_ctor_set(v___x_131_, 1, v___x_129_);
lean_ctor_set(v___x_131_, 2, v___x_128_);
return v___x_131_;
}
}
static lean_object* _init_l_FloatArray_get___auto__1___closed__18(void){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_132_ = lean_obj_once(&l_FloatArray_get___auto__1___closed__17, &l_FloatArray_get___auto__1___closed__17_once, _init_l_FloatArray_get___auto__1___closed__17);
v___x_133_ = ((lean_object*)(l_FloatArray_get___auto__1___closed__5));
v___x_134_ = lean_array_push(v___x_133_, v___x_132_);
return v___x_134_;
}
}
static lean_object* _init_l_FloatArray_get___auto__1___closed__19(void){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_135_ = lean_obj_once(&l_FloatArray_get___auto__1___closed__18, &l_FloatArray_get___auto__1___closed__18_once, _init_l_FloatArray_get___auto__1___closed__18);
v___x_136_ = ((lean_object*)(l_FloatArray_get___auto__1___closed__7));
v___x_137_ = lean_box(2);
v___x_138_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_138_, 0, v___x_137_);
lean_ctor_set(v___x_138_, 1, v___x_136_);
lean_ctor_set(v___x_138_, 2, v___x_135_);
return v___x_138_;
}
}
static lean_object* _init_l_FloatArray_get___auto__1___closed__20(void){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_139_ = lean_obj_once(&l_FloatArray_get___auto__1___closed__19, &l_FloatArray_get___auto__1___closed__19_once, _init_l_FloatArray_get___auto__1___closed__19);
v___x_140_ = ((lean_object*)(l_FloatArray_get___auto__1___closed__5));
v___x_141_ = lean_array_push(v___x_140_, v___x_139_);
return v___x_141_;
}
}
static lean_object* _init_l_FloatArray_get___auto__1___closed__21(void){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_142_ = lean_obj_once(&l_FloatArray_get___auto__1___closed__20, &l_FloatArray_get___auto__1___closed__20_once, _init_l_FloatArray_get___auto__1___closed__20);
v___x_143_ = ((lean_object*)(l_FloatArray_get___auto__1___closed__4));
v___x_144_ = lean_box(2);
v___x_145_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
lean_ctor_set(v___x_145_, 1, v___x_143_);
lean_ctor_set(v___x_145_, 2, v___x_142_);
return v___x_145_;
}
}
static lean_object* _init_l_FloatArray_get___auto__1(void){
_start:
{
lean_object* v___x_146_; 
v___x_146_ = lean_obj_once(&l_FloatArray_get___auto__1___closed__21, &l_FloatArray_get___auto__1___closed__21_once, _init_l_FloatArray_get___auto__1___closed__21);
return v___x_146_;
}
}
LEAN_EXPORT void l_FloatArray_get_0interp(lean_interpreter_value* stack)
{
lean_object* v_ds_147_ = stack[0].m_obj;
lean_object* v_i_148_ = stack[1].m_obj;
double v_res_150_;
v_res_150_ = lean_float_array_fget(v_ds_147_, v_i_148_);
stack->m_float
 = v_res_150_;
}
LEAN_EXPORT lean_object* l_FloatArray_get___boxed(lean_object* v_ds_151_, lean_object* v_i_152_, lean_object* v_h_153_){
_start:
{
double v_res_154_; lean_object* v_r_155_; 
v_res_154_ = lean_float_array_fget(v_ds_151_, v_i_152_);
lean_dec(v_i_152_);
lean_dec_ref(v_ds_151_);
v_r_155_ = lean_box_float(v_res_154_);
return v_r_155_;
}
}
LEAN_EXPORT void l_FloatArray_get_x21_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_156_ = stack[0].m_obj;
lean_object* v_a_00___x40___internal___hyg_157_ = stack[1].m_obj;
double v_res_158_;
v_res_158_ = lean_float_array_get(v_a_00___x40___internal___hyg_156_, v_a_00___x40___internal___hyg_157_);
stack->m_float
 = v_res_158_;
}
LEAN_EXPORT lean_object* l_FloatArray_get_x21___boxed(lean_object* v_a_00___x40___internal___hyg_159_, lean_object* v_a_00___x40___internal___hyg_160_){
_start:
{
double v_res_161_; lean_object* v_r_162_; 
v_res_161_ = lean_float_array_get(v_a_00___x40___internal___hyg_159_, v_a_00___x40___internal___hyg_160_);
lean_dec(v_a_00___x40___internal___hyg_160_);
lean_dec_ref(v_a_00___x40___internal___hyg_159_);
v_r_162_ = lean_box_float(v_res_161_);
return v_r_162_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_get_x3f(lean_object* v_ds_163_, lean_object* v_i_164_){
_start:
{
lean_object* v___x_165_; uint8_t v___x_166_; 
v___x_165_ = lean_float_array_size(v_ds_163_);
v___x_166_ = lean_nat_dec_lt(v_i_164_, v___x_165_);
if (v___x_166_ == 0)
{
lean_object* v___x_167_; 
v___x_167_ = lean_box(0);
return v___x_167_;
}
else
{
double v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_168_ = lean_float_array_fget(v_ds_163_, v_i_164_);
v___x_169_ = lean_box_float(v___x_168_);
v___x_170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
return v___x_170_;
}
}
}
LEAN_EXPORT lean_object* l_FloatArray_get_x3f___boxed(lean_object* v_ds_171_, lean_object* v_i_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_FloatArray_get_x3f(v_ds_171_, v_i_172_);
lean_dec(v_i_172_);
lean_dec_ref(v_ds_171_);
return v_res_173_;
}
}
double l_FloatArray_instGetElemNatFloatLtSize___lam__0(lean_object* v_xs_174_, lean_object* v_i_175_, lean_object* v_h_176_){
_start:
{
double v___x_177_; 
v___x_177_ = lean_float_array_fget(v_xs_174_, v_i_175_);
return v___x_177_;
}
}
LEAN_EXPORT void l_FloatArray_instGetElemNatFloatLtSize___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_174_ = stack[0].m_obj;
lean_object* v_i_175_ = stack[1].m_obj;
double v_res_178_;
v_res_178_ = l_FloatArray_instGetElemNatFloatLtSize___lam__0(v_xs_174_, v_i_175_, lean_box(0));
stack->m_float
 = v_res_178_;
}
LEAN_EXPORT lean_object* l_FloatArray_instGetElemNatFloatLtSize___lam__0___boxed(lean_object* v_xs_179_, lean_object* v_i_180_, lean_object* v_h_181_){
_start:
{
double v_res_182_; lean_object* v_r_183_; 
v_res_182_ = l_FloatArray_instGetElemNatFloatLtSize___lam__0(v_xs_179_, v_i_180_, v_h_181_);
lean_dec(v_i_180_);
lean_dec_ref(v_xs_179_);
v_r_183_ = lean_box_float(v_res_182_);
return v_r_183_;
}
}
double l_FloatArray_instGetElemUSizeFloatLtNatToNatSize___lam__0(lean_object* v_xs_186_, size_t v_i_187_, lean_object* v_h_188_){
_start:
{
double v___x_189_; 
v___x_189_ = lean_float_array_uget(v_xs_186_, v_i_187_);
return v___x_189_;
}
}
LEAN_EXPORT void l_FloatArray_instGetElemUSizeFloatLtNatToNatSize___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_186_ = stack[0].m_obj;
size_t v_i_187_ = stack[1].m_num;
double v_res_190_;
v_res_190_ = l_FloatArray_instGetElemUSizeFloatLtNatToNatSize___lam__0(v_xs_186_, v_i_187_, lean_box(0));
stack->m_float
 = v_res_190_;
}
LEAN_EXPORT lean_object* l_FloatArray_instGetElemUSizeFloatLtNatToNatSize___lam__0___boxed(lean_object* v_xs_191_, lean_object* v_i_192_, lean_object* v_h_193_){
_start:
{
size_t v_i_boxed_194_; double v_res_195_; lean_object* v_r_196_; 
v_i_boxed_194_ = lean_unbox_usize(v_i_192_);
lean_dec(v_i_192_);
v_res_195_ = l_FloatArray_instGetElemUSizeFloatLtNatToNatSize___lam__0(v_xs_191_, v_i_boxed_194_, v_h_193_);
lean_dec_ref(v_xs_191_);
v_r_196_ = lean_box_float(v_res_195_);
return v_r_196_;
}
}
static lean_object* _init_l_FloatArray_uset___auto__1(void){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = lean_obj_once(&l_FloatArray_get___auto__1___closed__21, &l_FloatArray_get___auto__1___closed__21_once, _init_l_FloatArray_get___auto__1___closed__21);
return v___x_199_;
}
}
LEAN_EXPORT void l_FloatArray_uset_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_200_ = stack[0].m_obj;
size_t v_i_201_ = stack[1].m_num;
double v_a_00___x40___internal___hyg_202_ = stack[2].m_float;
lean_object* v_res_204_;
v_res_204_ = lean_float_array_uset(v_a_200_, v_i_201_, v_a_00___x40___internal___hyg_202_);
stack->m_obj
 = v_res_204_;
}
LEAN_EXPORT lean_object* l_FloatArray_uset___boxed(lean_object* v_a_205_, lean_object* v_i_206_, lean_object* v_a_00___x40___internal___hyg_207_, lean_object* v_h_208_){
_start:
{
size_t v_i_boxed_209_; double v_a_00___x40___internal___hyg_1__boxed_210_; lean_object* v_res_211_; 
v_i_boxed_209_ = lean_unbox_usize(v_i_206_);
lean_dec(v_i_206_);
v_a_00___x40___internal___hyg_1__boxed_210_ = lean_unbox_float(v_a_00___x40___internal___hyg_207_);
lean_dec_ref(v_a_00___x40___internal___hyg_207_);
v_res_211_ = lean_float_array_uset(v_a_205_, v_i_boxed_209_, v_a_00___x40___internal___hyg_1__boxed_210_);
return v_res_211_;
}
}
static lean_object* _init_l_FloatArray_set___auto__1(void){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = lean_obj_once(&l_FloatArray_get___auto__1___closed__21, &l_FloatArray_get___auto__1___closed__21_once, _init_l_FloatArray_get___auto__1___closed__21);
return v___x_212_;
}
}
LEAN_EXPORT void l_FloatArray_set_0interp(lean_interpreter_value* stack)
{
lean_object* v_ds_213_ = stack[0].m_obj;
lean_object* v_i_214_ = stack[1].m_obj;
double v_a_00___x40___internal___hyg_215_ = stack[2].m_float;
lean_object* v_res_217_;
v_res_217_ = lean_float_array_fset(v_ds_213_, v_i_214_, v_a_00___x40___internal___hyg_215_);
stack->m_obj
 = v_res_217_;
}
LEAN_EXPORT lean_object* l_FloatArray_set___boxed(lean_object* v_ds_218_, lean_object* v_i_219_, lean_object* v_a_00___x40___internal___hyg_220_, lean_object* v_h_221_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_222_; lean_object* v_res_223_; 
v_a_00___x40___internal___hyg_1__boxed_222_ = lean_unbox_float(v_a_00___x40___internal___hyg_220_);
lean_dec_ref(v_a_00___x40___internal___hyg_220_);
v_res_223_ = lean_float_array_fset(v_ds_218_, v_i_219_, v_a_00___x40___internal___hyg_1__boxed_222_);
lean_dec(v_i_219_);
return v_res_223_;
}
}
LEAN_EXPORT void l_FloatArray_set_x21_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_224_ = stack[0].m_obj;
lean_object* v_a_00___x40___internal___hyg_225_ = stack[1].m_obj;
double v_a_00___x40___internal___hyg_226_ = stack[2].m_float;
lean_object* v_res_227_;
v_res_227_ = lean_float_array_set(v_a_00___x40___internal___hyg_224_, v_a_00___x40___internal___hyg_225_, v_a_00___x40___internal___hyg_226_);
stack->m_obj
 = v_res_227_;
}
LEAN_EXPORT lean_object* l_FloatArray_set_x21___boxed(lean_object* v_a_00___x40___internal___hyg_228_, lean_object* v_a_00___x40___internal___hyg_229_, lean_object* v_a_00___x40___internal___hyg_230_){
_start:
{
double v_a_00___x40___internal___hyg_3__boxed_231_; lean_object* v_res_232_; 
v_a_00___x40___internal___hyg_3__boxed_231_ = lean_unbox_float(v_a_00___x40___internal___hyg_230_);
lean_dec_ref(v_a_00___x40___internal___hyg_230_);
v_res_232_ = lean_float_array_set(v_a_00___x40___internal___hyg_228_, v_a_00___x40___internal___hyg_229_, v_a_00___x40___internal___hyg_3__boxed_231_);
lean_dec(v_a_00___x40___internal___hyg_229_);
return v_res_232_;
}
}
LEAN_EXPORT void l_FloatArray_markLinear_0interp(lean_interpreter_value* stack)
{
lean_object* v_ds_233_ = stack[0].m_obj;
lean_object* v_res_234_;
v_res_234_ = lean_sarray_mark_linear(v_ds_233_);
stack->m_obj
 = v_res_234_;
}
LEAN_EXPORT lean_object* l_FloatArray_markLinear___boxed(lean_object* v_ds_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = lean_sarray_mark_linear(v_ds_235_);
return v_res_236_;
}
}
LEAN_EXPORT void l_FloatArray_propagateMark_0interp(lean_interpreter_value* stack)
{
lean_object* v_ds_237_ = stack[0].m_obj;
lean_object* v_es_238_ = stack[1].m_obj;
lean_object* v_res_239_;
v_res_239_ = lean_sarray_propagate_mark(v_ds_237_, v_es_238_);
stack->m_obj
 = v_res_239_;
}
LEAN_EXPORT lean_object* l_FloatArray_propagateMark___boxed(lean_object* v_ds_240_, lean_object* v_es_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = lean_sarray_propagate_mark(v_ds_240_, v_es_241_);
lean_dec_ref(v_ds_240_);
return v_res_242_;
}
}
uint8_t l_FloatArray_isEmpty(lean_object* v_s_243_){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; uint8_t v___x_246_; 
v___x_244_ = lean_float_array_size(v_s_243_);
v___x_245_ = lean_unsigned_to_nat(0u);
v___x_246_ = lean_nat_dec_eq(v___x_244_, v___x_245_);
return v___x_246_;
}
}
LEAN_EXPORT void l_FloatArray_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_243_ = stack[0].m_obj;
uint8_t v_res_247_;
v_res_247_ = l_FloatArray_isEmpty(v_s_243_);
stack->m_num = v_res_247_;
}
LEAN_EXPORT lean_object* l_FloatArray_isEmpty___boxed(lean_object* v_s_248_){
_start:
{
uint8_t v_res_249_; lean_object* v_r_250_; 
v_res_249_ = l_FloatArray_isEmpty(v_s_248_);
lean_dec_ref(v_s_248_);
v_r_250_ = lean_box(v_res_249_);
return v_r_250_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_toList_loop(lean_object* v_ds_251_, lean_object* v_i_252_, lean_object* v_r_253_){
_start:
{
lean_object* v___x_254_; uint8_t v___x_255_; 
v___x_254_ = lean_float_array_size(v_ds_251_);
v___x_255_ = lean_nat_dec_lt(v_i_252_, v___x_254_);
if (v___x_255_ == 0)
{
lean_object* v___x_256_; 
lean_dec(v_i_252_);
v___x_256_ = l_List_reverse___redArg(v_r_253_);
return v___x_256_;
}
else
{
lean_object* v___x_257_; lean_object* v___x_258_; double v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_257_ = lean_unsigned_to_nat(1u);
v___x_258_ = lean_nat_add(v_i_252_, v___x_257_);
v___x_259_ = lean_float_array_fget(v_ds_251_, v_i_252_);
lean_dec(v_i_252_);
v___x_260_ = lean_box_float(v___x_259_);
v___x_261_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
lean_ctor_set(v___x_261_, 1, v_r_253_);
v_i_252_ = v___x_258_;
v_r_253_ = v___x_261_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_toList_loop___boxed(lean_object* v_ds_263_, lean_object* v_i_264_, lean_object* v_r_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_toList_loop(v_ds_263_, v_i_264_, v_r_265_);
lean_dec_ref(v_ds_263_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_toList(lean_object* v_ds_267_){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_268_ = lean_unsigned_to_nat(0u);
v___x_269_ = lean_box(0);
v___x_270_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_toList_loop(v_ds_267_, v___x_268_, v___x_269_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_toList___boxed(lean_object* v_ds_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_FloatArray_toList(v_ds_271_);
lean_dec_ref(v_ds_271_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg___lam__0___boxed(lean_object* v_toPure_273_, lean_object* v_i_274_, lean_object* v_inst_275_, lean_object* v_as_276_, lean_object* v_f_277_, lean_object* v_sz_278_, lean_object* v_____do__lift_279_){
_start:
{
size_t v_i_boxed_280_; size_t v_sz_boxed_281_; lean_object* v_res_282_; 
v_i_boxed_280_ = lean_unbox_usize(v_i_274_);
lean_dec(v_i_274_);
v_sz_boxed_281_ = lean_unbox_usize(v_sz_278_);
lean_dec(v_sz_278_);
v_res_282_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg___lam__0(v_toPure_273_, v_i_boxed_280_, v_inst_275_, v_as_276_, v_f_277_, v_sz_boxed_281_, v_____do__lift_279_);
return v_res_282_;
}
}
lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg(lean_object* v_inst_283_, lean_object* v_as_284_, lean_object* v_f_285_, size_t v_sz_286_, size_t v_i_287_, lean_object* v_b_288_){
_start:
{
lean_object* v_toApplicative_289_; lean_object* v_toBind_290_; lean_object* v_toPure_291_; uint8_t v___x_292_; 
v_toApplicative_289_ = lean_ctor_get(v_inst_283_, 0);
v_toBind_290_ = lean_ctor_get(v_inst_283_, 1);
lean_inc(v_toBind_290_);
v_toPure_291_ = lean_ctor_get(v_toApplicative_289_, 1);
lean_inc(v_toPure_291_);
v___x_292_ = lean_usize_dec_lt(v_i_287_, v_sz_286_);
if (v___x_292_ == 0)
{
lean_object* v___x_293_; 
lean_dec(v_toBind_290_);
lean_dec(v_f_285_);
lean_dec_ref(v_as_284_);
lean_dec_ref(v_inst_283_);
v___x_293_ = lean_apply_2(v_toPure_291_, lean_box(0), v_b_288_);
return v___x_293_;
}
else
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___f_296_; double v_a_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_294_ = lean_box_usize(v_i_287_);
v___x_295_ = lean_box_usize(v_sz_286_);
lean_inc(v_f_285_);
lean_inc_ref(v_as_284_);
v___f_296_ = lean_alloc_closure((void*)(l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_296_, 0, v_toPure_291_);
lean_closure_set(v___f_296_, 1, v___x_294_);
lean_closure_set(v___f_296_, 2, v_inst_283_);
lean_closure_set(v___f_296_, 3, v_as_284_);
lean_closure_set(v___f_296_, 4, v_f_285_);
lean_closure_set(v___f_296_, 5, v___x_295_);
v_a_297_ = lean_float_array_uget(v_as_284_, v_i_287_);
lean_dec_ref(v_as_284_);
v___x_298_ = lean_box_float(v_a_297_);
v___x_299_ = lean_apply_2(v_f_285_, v___x_298_, v_b_288_);
v___x_300_ = lean_apply_4(v_toBind_290_, lean_box(0), lean_box(0), v___x_299_, v___f_296_);
return v___x_300_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_283_ = stack[0].m_obj;
lean_object* v_as_284_ = stack[1].m_obj;
lean_object* v_f_285_ = stack[2].m_obj;
size_t v_sz_286_ = stack[3].m_num;
size_t v_i_287_ = stack[4].m_num;
lean_object* v_b_288_ = stack[5].m_obj;
lean_object* v_res_301_;
v_res_301_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg(v_inst_283_, v_as_284_, v_f_285_, v_sz_286_, v_i_287_, v_b_288_);
stack->m_obj
 = v_res_301_;
}
lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg___lam__0(lean_object* v_toPure_302_, size_t v_i_303_, lean_object* v_inst_304_, lean_object* v_as_305_, lean_object* v_f_306_, size_t v_sz_307_, lean_object* v_____do__lift_308_){
_start:
{
if (lean_obj_tag(v_____do__lift_308_) == 0)
{
lean_object* v_a_309_; lean_object* v___x_310_; 
lean_dec(v_f_306_);
lean_dec_ref(v_as_305_);
lean_dec_ref(v_inst_304_);
v_a_309_ = lean_ctor_get(v_____do__lift_308_, 0);
lean_inc(v_a_309_);
lean_dec_ref_known(v_____do__lift_308_, 1);
v___x_310_ = lean_apply_2(v_toPure_302_, lean_box(0), v_a_309_);
return v___x_310_;
}
else
{
lean_object* v_a_311_; size_t v___x_312_; size_t v___x_313_; lean_object* v___x_314_; 
lean_dec(v_toPure_302_);
v_a_311_ = lean_ctor_get(v_____do__lift_308_, 0);
lean_inc(v_a_311_);
lean_dec_ref_known(v_____do__lift_308_, 1);
v___x_312_ = ((size_t)1ULL);
v___x_313_ = lean_usize_add(v_i_303_, v___x_312_);
v___x_314_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg(v_inst_304_, v_as_305_, v_f_306_, v_sz_307_, v___x_313_, v_a_311_);
return v___x_314_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_302_ = stack[0].m_obj;
size_t v_i_303_ = stack[1].m_num;
lean_object* v_inst_304_ = stack[2].m_obj;
lean_object* v_as_305_ = stack[3].m_obj;
lean_object* v_f_306_ = stack[4].m_obj;
size_t v_sz_307_ = stack[5].m_num;
lean_object* v_____do__lift_308_ = stack[6].m_obj;
lean_object* v_res_315_;
v_res_315_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg___lam__0(v_toPure_302_, v_i_303_, v_inst_304_, v_as_305_, v_f_306_, v_sz_307_, v_____do__lift_308_);
stack->m_obj
 = v_res_315_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg___boxed(lean_object* v_inst_316_, lean_object* v_as_317_, lean_object* v_f_318_, lean_object* v_sz_319_, lean_object* v_i_320_, lean_object* v_b_321_){
_start:
{
size_t v_sz_boxed_322_; size_t v_i_boxed_323_; lean_object* v_res_324_; 
v_sz_boxed_322_ = lean_unbox_usize(v_sz_319_);
lean_dec(v_sz_319_);
v_i_boxed_323_ = lean_unbox_usize(v_i_320_);
lean_dec(v_i_320_);
v_res_324_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg(v_inst_316_, v_as_317_, v_f_318_, v_sz_boxed_322_, v_i_boxed_323_, v_b_321_);
return v_res_324_;
}
}
lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop(lean_object* v_00_u03b2_325_, lean_object* v_m_326_, lean_object* v_inst_327_, lean_object* v_as_328_, lean_object* v_f_329_, size_t v_sz_330_, size_t v_i_331_, lean_object* v_b_332_){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg(v_inst_327_, v_as_328_, v_f_329_, v_sz_330_, v_i_331_, v_b_332_);
return v___x_333_;
}
}
LEAN_EXPORT void l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_327_ = stack[2].m_obj;
lean_object* v_as_328_ = stack[3].m_obj;
lean_object* v_f_329_ = stack[4].m_obj;
size_t v_sz_330_ = stack[5].m_num;
size_t v_i_331_ = stack[6].m_num;
lean_object* v_b_332_ = stack[7].m_obj;
lean_object* v_res_334_;
v_res_334_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop(lean_box(0), lean_box(0), v_inst_327_, v_as_328_, v_f_329_, v_sz_330_, v_i_331_, v_b_332_);
stack->m_obj
 = v_res_334_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___boxed(lean_object* v_00_u03b2_335_, lean_object* v_m_336_, lean_object* v_inst_337_, lean_object* v_as_338_, lean_object* v_f_339_, lean_object* v_sz_340_, lean_object* v_i_341_, lean_object* v_b_342_){
_start:
{
size_t v_sz_boxed_343_; size_t v_i_boxed_344_; lean_object* v_res_345_; 
v_sz_boxed_343_ = lean_unbox_usize(v_sz_340_);
lean_dec(v_sz_340_);
v_i_boxed_344_ = lean_unbox_usize(v_i_341_);
lean_dec(v_i_341_);
v_res_345_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop(v_00_u03b2_335_, v_m_336_, v_inst_337_, v_as_338_, v_f_339_, v_sz_boxed_343_, v_i_boxed_344_, v_b_342_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_forInUnsafe___redArg(lean_object* v_inst_346_, lean_object* v_as_347_, lean_object* v_b_348_, lean_object* v_f_349_){
_start:
{
size_t v_sz_350_; size_t v___x_351_; lean_object* v___x_352_; 
v_sz_350_ = lean_sarray_size(v_as_347_);
v___x_351_ = ((size_t)0ULL);
v___x_352_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg(v_inst_346_, v_as_347_, v_f_349_, v_sz_350_, v___x_351_, v_b_348_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_forInUnsafe(lean_object* v_00_u03b2_353_, lean_object* v_m_354_, lean_object* v_inst_355_, lean_object* v_as_356_, lean_object* v_b_357_, lean_object* v_f_358_){
_start:
{
size_t v_sz_359_; size_t v___x_360_; lean_object* v___x_361_; 
v_sz_359_ = lean_sarray_size(v_as_356_);
v___x_360_ = ((size_t)0ULL);
v___x_361_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg(v_inst_355_, v_as_356_, v_f_358_, v_sz_359_, v___x_360_, v_b_357_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop___redArg___lam__0___boxed(lean_object* v_toPure_362_, lean_object* v_inst_363_, lean_object* v_as_364_, lean_object* v_f_365_, lean_object* v_n_366_, lean_object* v_____do__lift_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop___redArg___lam__0(v_toPure_362_, v_inst_363_, v_as_364_, v_f_365_, v_n_366_, v_____do__lift_367_);
lean_dec(v_n_366_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop___redArg(lean_object* v_inst_369_, lean_object* v_as_370_, lean_object* v_f_371_, lean_object* v_i_372_, lean_object* v_b_373_){
_start:
{
lean_object* v_toApplicative_374_; lean_object* v_toBind_375_; lean_object* v_toPure_376_; lean_object* v_zero_377_; uint8_t v_isZero_378_; 
v_toApplicative_374_ = lean_ctor_get(v_inst_369_, 0);
v_toBind_375_ = lean_ctor_get(v_inst_369_, 1);
lean_inc(v_toBind_375_);
v_toPure_376_ = lean_ctor_get(v_toApplicative_374_, 1);
lean_inc(v_toPure_376_);
v_zero_377_ = lean_unsigned_to_nat(0u);
v_isZero_378_ = lean_nat_dec_eq(v_i_372_, v_zero_377_);
if (v_isZero_378_ == 1)
{
lean_object* v___x_379_; 
lean_dec(v_toBind_375_);
lean_dec(v_f_371_);
lean_dec_ref(v_as_370_);
lean_dec_ref(v_inst_369_);
v___x_379_ = lean_apply_2(v_toPure_376_, lean_box(0), v_b_373_);
return v___x_379_;
}
else
{
lean_object* v_one_380_; lean_object* v_n_381_; lean_object* v___f_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; double v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v_one_380_ = lean_unsigned_to_nat(1u);
v_n_381_ = lean_nat_sub(v_i_372_, v_one_380_);
lean_inc(v_n_381_);
lean_inc(v_f_371_);
lean_inc_ref(v_as_370_);
v___f_382_ = lean_alloc_closure((void*)(l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_382_, 0, v_toPure_376_);
lean_closure_set(v___f_382_, 1, v_inst_369_);
lean_closure_set(v___f_382_, 2, v_as_370_);
lean_closure_set(v___f_382_, 3, v_f_371_);
lean_closure_set(v___f_382_, 4, v_n_381_);
v___x_383_ = lean_float_array_size(v_as_370_);
v___x_384_ = lean_nat_sub(v___x_383_, v_one_380_);
v___x_385_ = lean_nat_sub(v___x_384_, v_n_381_);
lean_dec(v_n_381_);
lean_dec(v___x_384_);
v___x_386_ = lean_float_array_fget(v_as_370_, v___x_385_);
lean_dec(v___x_385_);
lean_dec_ref(v_as_370_);
v___x_387_ = lean_box_float(v___x_386_);
v___x_388_ = lean_apply_2(v_f_371_, v___x_387_, v_b_373_);
v___x_389_ = lean_apply_4(v_toBind_375_, lean_box(0), lean_box(0), v___x_388_, v___f_382_);
return v___x_389_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop___redArg___lam__0(lean_object* v_toPure_390_, lean_object* v_inst_391_, lean_object* v_as_392_, lean_object* v_f_393_, lean_object* v_n_394_, lean_object* v_____do__lift_395_){
_start:
{
if (lean_obj_tag(v_____do__lift_395_) == 0)
{
lean_object* v_a_396_; lean_object* v___x_397_; 
lean_dec(v_f_393_);
lean_dec_ref(v_as_392_);
lean_dec_ref(v_inst_391_);
v_a_396_ = lean_ctor_get(v_____do__lift_395_, 0);
lean_inc(v_a_396_);
lean_dec_ref_known(v_____do__lift_395_, 1);
v___x_397_ = lean_apply_2(v_toPure_390_, lean_box(0), v_a_396_);
return v___x_397_;
}
else
{
lean_object* v_a_398_; lean_object* v___x_399_; 
lean_dec(v_toPure_390_);
v_a_398_ = lean_ctor_get(v_____do__lift_395_, 0);
lean_inc(v_a_398_);
lean_dec_ref_known(v_____do__lift_395_, 1);
v___x_399_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop___redArg(v_inst_391_, v_as_392_, v_f_393_, v_n_394_, v_a_398_);
return v___x_399_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop___redArg___boxed(lean_object* v_inst_400_, lean_object* v_as_401_, lean_object* v_f_402_, lean_object* v_i_403_, lean_object* v_b_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop___redArg(v_inst_400_, v_as_401_, v_f_402_, v_i_403_, v_b_404_);
lean_dec(v_i_403_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop(lean_object* v_00_u03b2_406_, lean_object* v_m_407_, lean_object* v_inst_408_, lean_object* v_as_409_, lean_object* v_f_410_, lean_object* v_i_411_, lean_object* v_h_412_, lean_object* v_b_413_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop___redArg(v_inst_408_, v_as_409_, v_f_410_, v_i_411_, v_b_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop___boxed(lean_object* v_00_u03b2_415_, lean_object* v_m_416_, lean_object* v_inst_417_, lean_object* v_as_418_, lean_object* v_f_419_, lean_object* v_i_420_, lean_object* v_h_421_, lean_object* v_b_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop(v_00_u03b2_415_, v_m_416_, v_inst_417_, v_as_418_, v_f_419_, v_i_420_, v_h_421_, v_b_422_);
lean_dec(v_i_420_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_instForInFloatOfMonad___redArg___lam__0(lean_object* v_inst_424_, lean_object* v_00_u03b2_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
size_t v_sz_429_; size_t v___x_430_; lean_object* v___x_431_; 
v_sz_429_ = lean_sarray_size(v___y_426_);
v___x_430_ = ((size_t)0ULL);
v___x_431_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg(v_inst_424_, v___y_426_, v___y_428_, v_sz_429_, v___x_430_, v___y_427_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_instForInFloatOfMonad___redArg(lean_object* v_inst_432_){
_start:
{
lean_object* v___f_433_; 
v___f_433_ = lean_alloc_closure((void*)(l_FloatArray_instForInFloatOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_433_, 0, v_inst_432_);
return v___f_433_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_instForInFloatOfMonad(lean_object* v_m_434_, lean_object* v_inst_435_){
_start:
{
lean_object* v___f_436_; 
v___f_436_ = lean_alloc_closure((void*)(l_FloatArray_instForInFloatOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_436_, 0, v_inst_435_);
return v___f_436_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg___lam__0___boxed(lean_object* v_i_437_, lean_object* v_inst_438_, lean_object* v_f_439_, lean_object* v_as_440_, lean_object* v_stop_441_, lean_object* v_____do__lift_442_){
_start:
{
size_t v_i_boxed_443_; size_t v_stop_boxed_444_; lean_object* v_res_445_; 
v_i_boxed_443_ = lean_unbox_usize(v_i_437_);
lean_dec(v_i_437_);
v_stop_boxed_444_ = lean_unbox_usize(v_stop_441_);
lean_dec(v_stop_441_);
v_res_445_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg___lam__0(v_i_boxed_443_, v_inst_438_, v_f_439_, v_as_440_, v_stop_boxed_444_, v_____do__lift_442_);
return v_res_445_;
}
}
lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(lean_object* v_inst_446_, lean_object* v_f_447_, lean_object* v_as_448_, size_t v_i_449_, size_t v_stop_450_, lean_object* v_b_451_){
_start:
{
lean_object* v_toApplicative_452_; lean_object* v_toBind_453_; lean_object* v_toPure_454_; uint8_t v___x_455_; 
v_toApplicative_452_ = lean_ctor_get(v_inst_446_, 0);
v_toBind_453_ = lean_ctor_get(v_inst_446_, 1);
lean_inc(v_toBind_453_);
v_toPure_454_ = lean_ctor_get(v_toApplicative_452_, 1);
v___x_455_ = lean_usize_dec_eq(v_i_449_, v_stop_450_);
if (v___x_455_ == 0)
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___f_458_; double v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_456_ = lean_box_usize(v_i_449_);
v___x_457_ = lean_box_usize(v_stop_450_);
lean_inc_ref(v_as_448_);
lean_inc(v_f_447_);
v___f_458_ = lean_alloc_closure((void*)(l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_458_, 0, v___x_456_);
lean_closure_set(v___f_458_, 1, v_inst_446_);
lean_closure_set(v___f_458_, 2, v_f_447_);
lean_closure_set(v___f_458_, 3, v_as_448_);
lean_closure_set(v___f_458_, 4, v___x_457_);
v___x_459_ = lean_float_array_uget(v_as_448_, v_i_449_);
lean_dec_ref(v_as_448_);
v___x_460_ = lean_box_float(v___x_459_);
v___x_461_ = lean_apply_2(v_f_447_, v_b_451_, v___x_460_);
v___x_462_ = lean_apply_4(v_toBind_453_, lean_box(0), lean_box(0), v___x_461_, v___f_458_);
return v___x_462_;
}
else
{
lean_object* v___x_463_; 
lean_inc(v_toPure_454_);
lean_dec(v_toBind_453_);
lean_dec_ref(v_as_448_);
lean_dec(v_f_447_);
lean_dec_ref(v_inst_446_);
v___x_463_ = lean_apply_2(v_toPure_454_, lean_box(0), v_b_451_);
return v___x_463_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_446_ = stack[0].m_obj;
lean_object* v_f_447_ = stack[1].m_obj;
lean_object* v_as_448_ = stack[2].m_obj;
size_t v_i_449_ = stack[3].m_num;
size_t v_stop_450_ = stack[4].m_num;
lean_object* v_b_451_ = stack[5].m_obj;
lean_object* v_res_464_;
v_res_464_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(v_inst_446_, v_f_447_, v_as_448_, v_i_449_, v_stop_450_, v_b_451_);
stack->m_obj
 = v_res_464_;
}
lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg___lam__0(size_t v_i_465_, lean_object* v_inst_466_, lean_object* v_f_467_, lean_object* v_as_468_, size_t v_stop_469_, lean_object* v_____do__lift_470_){
_start:
{
size_t v___x_471_; size_t v___x_472_; lean_object* v___x_473_; 
v___x_471_ = ((size_t)1ULL);
v___x_472_ = lean_usize_add(v_i_465_, v___x_471_);
v___x_473_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(v_inst_466_, v_f_467_, v_as_468_, v___x_472_, v_stop_469_, v_____do__lift_470_);
return v___x_473_;
}
}
LEAN_EXPORT void l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
size_t v_i_465_ = stack[0].m_num;
lean_object* v_inst_466_ = stack[1].m_obj;
lean_object* v_f_467_ = stack[2].m_obj;
lean_object* v_as_468_ = stack[3].m_obj;
size_t v_stop_469_ = stack[4].m_num;
lean_object* v_____do__lift_470_ = stack[5].m_obj;
lean_object* v_res_474_;
v_res_474_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg___lam__0(v_i_465_, v_inst_466_, v_f_467_, v_as_468_, v_stop_469_, v_____do__lift_470_);
stack->m_obj
 = v_res_474_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg___boxed(lean_object* v_inst_475_, lean_object* v_f_476_, lean_object* v_as_477_, lean_object* v_i_478_, lean_object* v_stop_479_, lean_object* v_b_480_){
_start:
{
size_t v_i_boxed_481_; size_t v_stop_boxed_482_; lean_object* v_res_483_; 
v_i_boxed_481_ = lean_unbox_usize(v_i_478_);
lean_dec(v_i_478_);
v_stop_boxed_482_ = lean_unbox_usize(v_stop_479_);
lean_dec(v_stop_479_);
v_res_483_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(v_inst_475_, v_f_476_, v_as_477_, v_i_boxed_481_, v_stop_boxed_482_, v_b_480_);
return v_res_483_;
}
}
lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold(lean_object* v_00_u03b2_484_, lean_object* v_m_485_, lean_object* v_inst_486_, lean_object* v_f_487_, lean_object* v_as_488_, size_t v_i_489_, size_t v_stop_490_, lean_object* v_b_491_){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(v_inst_486_, v_f_487_, v_as_488_, v_i_489_, v_stop_490_, v_b_491_);
return v___x_492_;
}
}
LEAN_EXPORT void l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_486_ = stack[2].m_obj;
lean_object* v_f_487_ = stack[3].m_obj;
lean_object* v_as_488_ = stack[4].m_obj;
size_t v_i_489_ = stack[5].m_num;
size_t v_stop_490_ = stack[6].m_num;
lean_object* v_b_491_ = stack[7].m_obj;
lean_object* v_res_493_;
v_res_493_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold(lean_box(0), lean_box(0), v_inst_486_, v_f_487_, v_as_488_, v_i_489_, v_stop_490_, v_b_491_);
stack->m_obj
 = v_res_493_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___boxed(lean_object* v_00_u03b2_494_, lean_object* v_m_495_, lean_object* v_inst_496_, lean_object* v_f_497_, lean_object* v_as_498_, lean_object* v_i_499_, lean_object* v_stop_500_, lean_object* v_b_501_){
_start:
{
size_t v_i_boxed_502_; size_t v_stop_boxed_503_; lean_object* v_res_504_; 
v_i_boxed_502_ = lean_unbox_usize(v_i_499_);
lean_dec(v_i_499_);
v_stop_boxed_503_ = lean_unbox_usize(v_stop_500_);
lean_dec(v_stop_500_);
v_res_504_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold(v_00_u03b2_494_, v_m_495_, v_inst_496_, v_f_497_, v_as_498_, v_i_boxed_502_, v_stop_boxed_503_, v_b_501_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_foldlMUnsafe___redArg(lean_object* v_inst_505_, lean_object* v_f_506_, lean_object* v_init_507_, lean_object* v_as_508_, lean_object* v_start_509_, lean_object* v_stop_510_){
_start:
{
lean_object* v_toApplicative_511_; lean_object* v_toPure_512_; uint8_t v___x_513_; 
v_toApplicative_511_ = lean_ctor_get(v_inst_505_, 0);
v_toPure_512_ = lean_ctor_get(v_toApplicative_511_, 1);
v___x_513_ = lean_nat_dec_lt(v_start_509_, v_stop_510_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; 
lean_inc(v_toPure_512_);
lean_dec_ref(v_as_508_);
lean_dec(v_f_506_);
lean_dec_ref(v_inst_505_);
v___x_514_ = lean_apply_2(v_toPure_512_, lean_box(0), v_init_507_);
return v___x_514_;
}
else
{
lean_object* v___x_515_; uint8_t v___x_516_; 
v___x_515_ = lean_float_array_size(v_as_508_);
v___x_516_ = lean_nat_dec_le(v_stop_510_, v___x_515_);
if (v___x_516_ == 0)
{
uint8_t v___x_517_; 
v___x_517_ = lean_nat_dec_lt(v_start_509_, v___x_515_);
if (v___x_517_ == 0)
{
lean_object* v___x_518_; 
lean_inc(v_toPure_512_);
lean_dec_ref(v_as_508_);
lean_dec(v_f_506_);
lean_dec_ref(v_inst_505_);
v___x_518_ = lean_apply_2(v_toPure_512_, lean_box(0), v_init_507_);
return v___x_518_;
}
else
{
size_t v___x_519_; size_t v___x_520_; lean_object* v___x_521_; 
v___x_519_ = lean_usize_of_nat(v_start_509_);
v___x_520_ = lean_usize_of_nat(v___x_515_);
v___x_521_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(v_inst_505_, v_f_506_, v_as_508_, v___x_519_, v___x_520_, v_init_507_);
return v___x_521_;
}
}
else
{
size_t v___x_522_; size_t v___x_523_; lean_object* v___x_524_; 
v___x_522_ = lean_usize_of_nat(v_start_509_);
v___x_523_ = lean_usize_of_nat(v_stop_510_);
v___x_524_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(v_inst_505_, v_f_506_, v_as_508_, v___x_522_, v___x_523_, v_init_507_);
return v___x_524_;
}
}
}
}
LEAN_EXPORT lean_object* l_FloatArray_foldlMUnsafe___redArg___boxed(lean_object* v_inst_525_, lean_object* v_f_526_, lean_object* v_init_527_, lean_object* v_as_528_, lean_object* v_start_529_, lean_object* v_stop_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_FloatArray_foldlMUnsafe___redArg(v_inst_525_, v_f_526_, v_init_527_, v_as_528_, v_start_529_, v_stop_530_);
lean_dec(v_stop_530_);
lean_dec(v_start_529_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_foldlMUnsafe(lean_object* v_00_u03b2_532_, lean_object* v_m_533_, lean_object* v_inst_534_, lean_object* v_f_535_, lean_object* v_init_536_, lean_object* v_as_537_, lean_object* v_start_538_, lean_object* v_stop_539_){
_start:
{
lean_object* v_toApplicative_540_; lean_object* v_toPure_541_; uint8_t v___x_542_; 
v_toApplicative_540_ = lean_ctor_get(v_inst_534_, 0);
v_toPure_541_ = lean_ctor_get(v_toApplicative_540_, 1);
v___x_542_ = lean_nat_dec_lt(v_start_538_, v_stop_539_);
if (v___x_542_ == 0)
{
lean_object* v___x_543_; 
lean_inc(v_toPure_541_);
lean_dec_ref(v_as_537_);
lean_dec(v_f_535_);
lean_dec_ref(v_inst_534_);
v___x_543_ = lean_apply_2(v_toPure_541_, lean_box(0), v_init_536_);
return v___x_543_;
}
else
{
lean_object* v___x_544_; uint8_t v___x_545_; 
v___x_544_ = lean_float_array_size(v_as_537_);
v___x_545_ = lean_nat_dec_le(v_stop_539_, v___x_544_);
if (v___x_545_ == 0)
{
uint8_t v___x_546_; 
v___x_546_ = lean_nat_dec_lt(v_start_538_, v___x_544_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; 
lean_inc(v_toPure_541_);
lean_dec_ref(v_as_537_);
lean_dec(v_f_535_);
lean_dec_ref(v_inst_534_);
v___x_547_ = lean_apply_2(v_toPure_541_, lean_box(0), v_init_536_);
return v___x_547_;
}
else
{
size_t v___x_548_; size_t v___x_549_; lean_object* v___x_550_; 
v___x_548_ = lean_usize_of_nat(v_start_538_);
v___x_549_ = lean_usize_of_nat(v___x_544_);
v___x_550_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(v_inst_534_, v_f_535_, v_as_537_, v___x_548_, v___x_549_, v_init_536_);
return v___x_550_;
}
}
else
{
size_t v___x_551_; size_t v___x_552_; lean_object* v___x_553_; 
v___x_551_ = lean_usize_of_nat(v_start_538_);
v___x_552_ = lean_usize_of_nat(v_stop_539_);
v___x_553_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(v_inst_534_, v_f_535_, v_as_537_, v___x_551_, v___x_552_, v_init_536_);
return v___x_553_;
}
}
}
}
LEAN_EXPORT lean_object* l_FloatArray_foldlMUnsafe___boxed(lean_object* v_00_u03b2_554_, lean_object* v_m_555_, lean_object* v_inst_556_, lean_object* v_f_557_, lean_object* v_init_558_, lean_object* v_as_559_, lean_object* v_start_560_, lean_object* v_stop_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_FloatArray_foldlMUnsafe(v_00_u03b2_554_, v_m_555_, v_inst_556_, v_f_557_, v_init_558_, v_as_559_, v_start_560_, v_stop_561_);
lean_dec(v_stop_561_);
lean_dec(v_start_560_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop___redArg___lam__0___boxed(lean_object* v_j_563_, lean_object* v_inst_564_, lean_object* v_f_565_, lean_object* v_as_566_, lean_object* v_stop_567_, lean_object* v_n_568_, lean_object* v_____do__lift_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop___redArg___lam__0(v_j_563_, v_inst_564_, v_f_565_, v_as_566_, v_stop_567_, v_n_568_, v_____do__lift_569_);
lean_dec(v_n_568_);
lean_dec(v_j_563_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop___redArg(lean_object* v_inst_571_, lean_object* v_f_572_, lean_object* v_as_573_, lean_object* v_stop_574_, lean_object* v_i_575_, lean_object* v_j_576_, lean_object* v_b_577_){
_start:
{
lean_object* v_toApplicative_578_; lean_object* v_toBind_579_; lean_object* v_toPure_580_; uint8_t v___x_581_; 
v_toApplicative_578_ = lean_ctor_get(v_inst_571_, 0);
v_toBind_579_ = lean_ctor_get(v_inst_571_, 1);
lean_inc(v_toBind_579_);
v_toPure_580_ = lean_ctor_get(v_toApplicative_578_, 1);
v___x_581_ = lean_nat_dec_lt(v_j_576_, v_stop_574_);
if (v___x_581_ == 0)
{
lean_object* v___x_582_; 
lean_inc(v_toPure_580_);
lean_dec(v_toBind_579_);
lean_dec(v_j_576_);
lean_dec(v_stop_574_);
lean_dec_ref(v_as_573_);
lean_dec(v_f_572_);
lean_dec_ref(v_inst_571_);
v___x_582_ = lean_apply_2(v_toPure_580_, lean_box(0), v_b_577_);
return v___x_582_;
}
else
{
lean_object* v_zero_583_; uint8_t v_isZero_584_; 
v_zero_583_ = lean_unsigned_to_nat(0u);
v_isZero_584_ = lean_nat_dec_eq(v_i_575_, v_zero_583_);
if (v_isZero_584_ == 1)
{
lean_object* v___x_585_; 
lean_inc(v_toPure_580_);
lean_dec(v_toBind_579_);
lean_dec(v_j_576_);
lean_dec(v_stop_574_);
lean_dec_ref(v_as_573_);
lean_dec(v_f_572_);
lean_dec_ref(v_inst_571_);
v___x_585_ = lean_apply_2(v_toPure_580_, lean_box(0), v_b_577_);
return v___x_585_;
}
else
{
lean_object* v_one_586_; lean_object* v_n_587_; lean_object* v___f_588_; double v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v_one_586_ = lean_unsigned_to_nat(1u);
v_n_587_ = lean_nat_sub(v_i_575_, v_one_586_);
lean_inc_ref(v_as_573_);
lean_inc(v_f_572_);
lean_inc(v_j_576_);
v___f_588_ = lean_alloc_closure((void*)(l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_588_, 0, v_j_576_);
lean_closure_set(v___f_588_, 1, v_inst_571_);
lean_closure_set(v___f_588_, 2, v_f_572_);
lean_closure_set(v___f_588_, 3, v_as_573_);
lean_closure_set(v___f_588_, 4, v_stop_574_);
lean_closure_set(v___f_588_, 5, v_n_587_);
v___x_589_ = lean_float_array_fget(v_as_573_, v_j_576_);
lean_dec(v_j_576_);
lean_dec_ref(v_as_573_);
v___x_590_ = lean_box_float(v___x_589_);
v___x_591_ = lean_apply_2(v_f_572_, v_b_577_, v___x_590_);
v___x_592_ = lean_apply_4(v_toBind_579_, lean_box(0), lean_box(0), v___x_591_, v___f_588_);
return v___x_592_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop___redArg___lam__0(lean_object* v_j_593_, lean_object* v_inst_594_, lean_object* v_f_595_, lean_object* v_as_596_, lean_object* v_stop_597_, lean_object* v_n_598_, lean_object* v_____do__lift_599_){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_600_ = lean_unsigned_to_nat(1u);
v___x_601_ = lean_nat_add(v_j_593_, v___x_600_);
v___x_602_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop___redArg(v_inst_594_, v_f_595_, v_as_596_, v_stop_597_, v_n_598_, v___x_601_, v_____do__lift_599_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop___redArg___boxed(lean_object* v_inst_603_, lean_object* v_f_604_, lean_object* v_as_605_, lean_object* v_stop_606_, lean_object* v_i_607_, lean_object* v_j_608_, lean_object* v_b_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop___redArg(v_inst_603_, v_f_604_, v_as_605_, v_stop_606_, v_i_607_, v_j_608_, v_b_609_);
lean_dec(v_i_607_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop(lean_object* v_00_u03b2_611_, lean_object* v_m_612_, lean_object* v_inst_613_, lean_object* v_f_614_, lean_object* v_as_615_, lean_object* v_stop_616_, lean_object* v_h_617_, lean_object* v_i_618_, lean_object* v_j_619_, lean_object* v_b_620_){
_start:
{
lean_object* v___x_621_; 
v___x_621_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop___redArg(v_inst_613_, v_f_614_, v_as_615_, v_stop_616_, v_i_618_, v_j_619_, v_b_620_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop___boxed(lean_object* v_00_u03b2_622_, lean_object* v_m_623_, lean_object* v_inst_624_, lean_object* v_f_625_, lean_object* v_as_626_, lean_object* v_stop_627_, lean_object* v_h_628_, lean_object* v_i_629_, lean_object* v_j_630_, lean_object* v_b_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop(v_00_u03b2_622_, v_m_623_, v_inst_624_, v_f_625_, v_as_626_, v_stop_627_, v_h_628_, v_i_629_, v_j_630_, v_b_631_);
lean_dec(v_i_629_);
return v_res_632_;
}
}
lean_object* l_FloatArray_foldl___redArg___lam__0(lean_object* v_f_633_, lean_object* v_x1_634_, double v_x2_635_){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_636_ = lean_box_float(v_x2_635_);
v___x_637_ = lean_apply_2(v_f_633_, v_x1_634_, v___x_636_);
return v___x_637_;
}
}
LEAN_EXPORT void l_FloatArray_foldl___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_633_ = stack[0].m_obj;
lean_object* v_x1_634_ = stack[1].m_obj;
double v_x2_635_ = stack[2].m_float;
lean_object* v_res_638_;
v_res_638_ = l_FloatArray_foldl___redArg___lam__0(v_f_633_, v_x1_634_, v_x2_635_);
stack->m_obj
 = v_res_638_;
}
LEAN_EXPORT lean_object* l_FloatArray_foldl___redArg___lam__0___boxed(lean_object* v_f_639_, lean_object* v_x1_640_, lean_object* v_x2_641_){
_start:
{
double v_x2_187__boxed_642_; lean_object* v_res_643_; 
v_x2_187__boxed_642_ = lean_unbox_float(v_x2_641_);
lean_dec_ref(v_x2_641_);
v_res_643_ = l_FloatArray_foldl___redArg___lam__0(v_f_639_, v_x1_640_, v_x2_187__boxed_642_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_foldl___redArg(lean_object* v_f_663_, lean_object* v_init_664_, lean_object* v_as_665_, lean_object* v_start_666_, lean_object* v_stop_667_){
_start:
{
lean_object* v___x_668_; uint8_t v___x_669_; 
v___x_668_ = ((lean_object*)(l_FloatArray_foldl___redArg___closed__9));
v___x_669_ = lean_nat_dec_lt(v_start_666_, v_stop_667_);
if (v___x_669_ == 0)
{
lean_dec_ref(v_as_665_);
lean_dec(v_f_663_);
return v_init_664_;
}
else
{
lean_object* v___f_670_; lean_object* v___x_671_; uint8_t v___x_672_; 
v___f_670_ = lean_alloc_closure((void*)(l_FloatArray_foldl___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_670_, 0, v_f_663_);
v___x_671_ = lean_float_array_size(v_as_665_);
v___x_672_ = lean_nat_dec_le(v_stop_667_, v___x_671_);
if (v___x_672_ == 0)
{
uint8_t v___x_673_; 
v___x_673_ = lean_nat_dec_lt(v_start_666_, v___x_671_);
if (v___x_673_ == 0)
{
lean_dec_ref(v___f_670_);
lean_dec_ref(v_as_665_);
return v_init_664_;
}
else
{
size_t v___x_674_; size_t v___x_675_; lean_object* v___x_676_; 
v___x_674_ = lean_usize_of_nat(v_start_666_);
v___x_675_ = lean_usize_of_nat(v___x_671_);
v___x_676_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(v___x_668_, v___f_670_, v_as_665_, v___x_674_, v___x_675_, v_init_664_);
return v___x_676_;
}
}
else
{
size_t v___x_677_; size_t v___x_678_; lean_object* v___x_679_; 
v___x_677_ = lean_usize_of_nat(v_start_666_);
v___x_678_ = lean_usize_of_nat(v_stop_667_);
v___x_679_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(v___x_668_, v___f_670_, v_as_665_, v___x_677_, v___x_678_, v_init_664_);
return v___x_679_;
}
}
}
}
LEAN_EXPORT lean_object* l_FloatArray_foldl___redArg___boxed(lean_object* v_f_680_, lean_object* v_init_681_, lean_object* v_as_682_, lean_object* v_start_683_, lean_object* v_stop_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l_FloatArray_foldl___redArg(v_f_680_, v_init_681_, v_as_682_, v_start_683_, v_stop_684_);
lean_dec(v_stop_684_);
lean_dec(v_start_683_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_foldl(lean_object* v_00_u03b2_686_, lean_object* v_f_687_, lean_object* v_init_688_, lean_object* v_as_689_, lean_object* v_start_690_, lean_object* v_stop_691_){
_start:
{
lean_object* v___x_692_; uint8_t v___x_693_; 
v___x_692_ = ((lean_object*)(l_FloatArray_foldl___redArg___closed__9));
v___x_693_ = lean_nat_dec_lt(v_start_690_, v_stop_691_);
if (v___x_693_ == 0)
{
lean_dec_ref(v_as_689_);
lean_dec(v_f_687_);
return v_init_688_;
}
else
{
lean_object* v___f_694_; lean_object* v___x_695_; uint8_t v___x_696_; 
v___f_694_ = lean_alloc_closure((void*)(l_FloatArray_foldl___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_694_, 0, v_f_687_);
v___x_695_ = lean_float_array_size(v_as_689_);
v___x_696_ = lean_nat_dec_le(v_stop_691_, v___x_695_);
if (v___x_696_ == 0)
{
uint8_t v___x_697_; 
v___x_697_ = lean_nat_dec_lt(v_start_690_, v___x_695_);
if (v___x_697_ == 0)
{
lean_dec_ref(v___f_694_);
lean_dec_ref(v_as_689_);
return v_init_688_;
}
else
{
size_t v___x_698_; size_t v___x_699_; lean_object* v___x_700_; 
v___x_698_ = lean_usize_of_nat(v_start_690_);
v___x_699_ = lean_usize_of_nat(v___x_695_);
v___x_700_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(v___x_692_, v___f_694_, v_as_689_, v___x_698_, v___x_699_, v_init_688_);
return v___x_700_;
}
}
else
{
size_t v___x_701_; size_t v___x_702_; lean_object* v___x_703_; 
v___x_701_ = lean_usize_of_nat(v_start_690_);
v___x_702_ = lean_usize_of_nat(v_stop_691_);
v___x_703_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(v___x_692_, v___f_694_, v_as_689_, v___x_701_, v___x_702_, v_init_688_);
return v___x_703_;
}
}
}
}
LEAN_EXPORT lean_object* l_FloatArray_foldl___boxed(lean_object* v_00_u03b2_704_, lean_object* v_f_705_, lean_object* v_init_706_, lean_object* v_as_707_, lean_object* v_start_708_, lean_object* v_stop_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_FloatArray_foldl(v_00_u03b2_704_, v_f_705_, v_init_706_, v_as_707_, v_start_708_, v_stop_709_);
lean_dec(v_stop_709_);
lean_dec(v_start_708_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__List_toFloatArray_loop(lean_object* v_x_711_, lean_object* v_x_712_){
_start:
{
if (lean_obj_tag(v_x_711_) == 0)
{
return v_x_712_;
}
else
{
lean_object* v_head_713_; lean_object* v_tail_714_; double v___x_715_; lean_object* v___x_716_; 
v_head_713_ = lean_ctor_get(v_x_711_, 0);
v_tail_714_ = lean_ctor_get(v_x_711_, 1);
v___x_715_ = lean_unbox_float(v_head_713_);
v___x_716_ = lean_float_array_push(v_x_712_, v___x_715_);
v_x_711_ = v_tail_714_;
v_x_712_ = v___x_716_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__List_toFloatArray_loop___boxed(lean_object* v_x_718_, lean_object* v_x_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l___private_Init_Data_FloatArray_Basic_0__List_toFloatArray_loop(v_x_718_, v_x_719_);
lean_dec(v_x_718_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_List_toFloatArray(lean_object* v_ds_721_){
_start:
{
lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_722_ = l_FloatArray_empty;
v___x_723_ = l___private_Init_Data_FloatArray_Basic_0__List_toFloatArray_loop(v_ds_721_, v___x_722_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l_List_toFloatArray___boxed(lean_object* v_ds_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l_List_toFloatArray(v_ds_724_);
lean_dec(v_ds_724_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_instToStringFloatArray___lam__0(lean_object* v___x_726_, lean_object* v_ds_727_){
_start:
{
lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_728_ = l_FloatArray_toList(v_ds_727_);
v___x_729_ = l_List_toString___redArg(v___x_726_, v___x_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_instToStringFloatArray___lam__0___boxed(lean_object* v___x_730_, lean_object* v_ds_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_instToStringFloatArray___lam__0(v___x_730_, v_ds_731_);
lean_dec_ref(v_ds_731_);
return v_res_732_;
}
}
lean_object* runtime_initialize_Init_Data_Float_Float(uint8_t builtin);
lean_object* runtime_initialize_Init_Ext(uint8_t builtin);
lean_object* runtime_initialize_Init_GetElem(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Extra(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_FloatArray_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Float_Float(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_GetElem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_FloatArray_empty = _init_l_FloatArray_empty();
lean_mark_persistent(l_FloatArray_empty);
l_FloatArray_instInhabited = _init_l_FloatArray_instInhabited();
lean_mark_persistent(l_FloatArray_instInhabited);
l_FloatArray_instEmptyCollection = _init_l_FloatArray_instEmptyCollection();
lean_mark_persistent(l_FloatArray_instEmptyCollection);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_FloatArray_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_FloatArray_get___auto__1 = _init_l_FloatArray_get___auto__1();
lean_mark_persistent(l_FloatArray_get___auto__1);
l_FloatArray_uset___auto__1 = _init_l_FloatArray_uset___auto__1();
lean_mark_persistent(l_FloatArray_uset___auto__1);
l_FloatArray_set___auto__1 = _init_l_FloatArray_set___auto__1();
lean_mark_persistent(l_FloatArray_set___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Float_Float(uint8_t builtin);
lean_object* initialize_Init_Ext(uint8_t builtin);
lean_object* initialize_Init_GetElem(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Extra(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_FloatArray_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Float_Float(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_GetElem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_FloatArray_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_FloatArray_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_FloatArray_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
