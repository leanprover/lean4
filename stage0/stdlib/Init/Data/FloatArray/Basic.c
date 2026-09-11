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
LEAN_EXPORT lean_object* l_FloatArray_mk___boxed(lean_object* v_data_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = lean_float_array_mk(v_data_2_);
return v_res_3_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_data___boxed(lean_object* v_self_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = lean_float_array_data(v_self_5_);
return v_res_6_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00FloatArray_instBEq_beq_spec__0___redArg(lean_object* v_xs_7_, lean_object* v_ys_8_, lean_object* v_x_9_){
_start:
{
lean_object* v_zero_10_; uint8_t v_isZero_11_; 
v_zero_10_ = lean_unsigned_to_nat(0u);
v_isZero_11_ = lean_nat_dec_eq(v_x_9_, v_zero_10_);
if (v_isZero_11_ == 1)
{
lean_dec(v_x_9_);
return v_isZero_11_;
}
else
{
lean_object* v_one_12_; lean_object* v_n_13_; lean_object* v___x_14_; lean_object* v___x_15_; double v___x_16_; double v___x_17_; uint8_t v___x_18_; 
v_one_12_ = lean_unsigned_to_nat(1u);
v_n_13_ = lean_nat_sub(v_x_9_, v_one_12_);
lean_dec(v_x_9_);
v___x_14_ = lean_array_fget_borrowed(v_xs_7_, v_n_13_);
v___x_15_ = lean_array_fget_borrowed(v_ys_8_, v_n_13_);
v___x_16_ = lean_unbox_float(v___x_14_);
v___x_17_ = lean_unbox_float(v___x_15_);
v___x_18_ = lean_float_beq(v___x_16_, v___x_17_);
if (v___x_18_ == 0)
{
lean_dec(v_n_13_);
return v___x_18_;
}
else
{
v_x_9_ = v_n_13_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00FloatArray_instBEq_beq_spec__0___redArg___boxed(lean_object* v_xs_20_, lean_object* v_ys_21_, lean_object* v_x_22_){
_start:
{
uint8_t v_res_23_; lean_object* v_r_24_; 
v_res_23_ = l_Array_isEqvAux___at___00FloatArray_instBEq_beq_spec__0___redArg(v_xs_20_, v_ys_21_, v_x_22_);
lean_dec_ref(v_ys_21_);
lean_dec_ref(v_xs_20_);
v_r_24_ = lean_box(v_res_23_);
return v_r_24_;
}
}
LEAN_EXPORT uint8_t l_FloatArray_instBEq_beq(lean_object* v_x_25_, lean_object* v_x_26_){
_start:
{
lean_object* v_data_27_; lean_object* v_data_28_; lean_object* v___x_29_; lean_object* v___x_30_; uint8_t v___x_31_; 
v_data_27_ = lean_float_array_data(v_x_25_);
v_data_28_ = lean_float_array_data(v_x_26_);
v___x_29_ = lean_array_get_size(v_data_27_);
v___x_30_ = lean_array_get_size(v_data_28_);
v___x_31_ = lean_nat_dec_eq(v___x_29_, v___x_30_);
if (v___x_31_ == 0)
{
lean_dec_ref(v_data_28_);
lean_dec_ref(v_data_27_);
return v___x_31_;
}
else
{
uint8_t v___x_32_; 
v___x_32_ = l_Array_isEqvAux___at___00FloatArray_instBEq_beq_spec__0___redArg(v_data_27_, v_data_28_, v___x_29_);
lean_dec_ref(v_data_28_);
lean_dec_ref(v_data_27_);
return v___x_32_;
}
}
}
LEAN_EXPORT lean_object* l_FloatArray_instBEq_beq___boxed(lean_object* v_x_33_, lean_object* v_x_34_){
_start:
{
uint8_t v_res_35_; lean_object* v_r_36_; 
v_res_35_ = l_FloatArray_instBEq_beq(v_x_33_, v_x_34_);
v_r_36_ = lean_box(v_res_35_);
return v_r_36_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00FloatArray_instBEq_beq_spec__0(lean_object* v_xs_37_, lean_object* v_ys_38_, lean_object* v_hsz_39_, lean_object* v_x_40_, lean_object* v_x_41_){
_start:
{
uint8_t v___x_42_; 
v___x_42_ = l_Array_isEqvAux___at___00FloatArray_instBEq_beq_spec__0___redArg(v_xs_37_, v_ys_38_, v_x_40_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00FloatArray_instBEq_beq_spec__0___boxed(lean_object* v_xs_43_, lean_object* v_ys_44_, lean_object* v_hsz_45_, lean_object* v_x_46_, lean_object* v_x_47_){
_start:
{
uint8_t v_res_48_; lean_object* v_r_49_; 
v_res_48_ = l_Array_isEqvAux___at___00FloatArray_instBEq_beq_spec__0(v_xs_43_, v_ys_44_, v_hsz_45_, v_x_46_, v_x_47_);
lean_dec_ref(v_ys_44_);
lean_dec_ref(v_xs_43_);
v_r_49_ = lean_box(v_res_48_);
return v_r_49_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_emptyWithCapacity___boxed(lean_object* v_c_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = lean_mk_empty_float_array(v_c_53_);
lean_dec(v_c_53_);
return v_res_54_;
}
}
static lean_object* _init_l_FloatArray_empty___closed__0(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_55_ = lean_unsigned_to_nat(0u);
v___x_56_ = lean_mk_empty_float_array(v___x_55_);
return v___x_56_;
}
}
static lean_object* _init_l_FloatArray_empty(void){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = lean_obj_once(&l_FloatArray_empty___closed__0, &l_FloatArray_empty___closed__0_once, _init_l_FloatArray_empty___closed__0);
return v___x_57_;
}
}
static lean_object* _init_l_FloatArray_instInhabited(void){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_FloatArray_empty;
return v___x_58_;
}
}
static lean_object* _init_l_FloatArray_instEmptyCollection(void){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = l_FloatArray_empty;
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_push___boxed(lean_object* v_a_00___x40___internal___hyg_62_, lean_object* v_a_00___x40___internal___hyg_63_){
_start:
{
double v_a_00___x40___internal___hyg_2__boxed_64_; lean_object* v_res_65_; 
v_a_00___x40___internal___hyg_2__boxed_64_ = lean_unbox_float(v_a_00___x40___internal___hyg_63_);
lean_dec_ref(v_a_00___x40___internal___hyg_63_);
v_res_65_ = lean_float_array_push(v_a_00___x40___internal___hyg_62_, v_a_00___x40___internal___hyg_2__boxed_64_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_size___boxed(lean_object* v_a_00___x40___internal___hyg_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = lean_float_array_size(v_a_00___x40___internal___hyg_67_);
lean_dec_ref(v_a_00___x40___internal___hyg_67_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_usize___boxed(lean_object* v_a_70_){
_start:
{
size_t v_res_71_; lean_object* v_r_72_; 
v_res_71_ = lean_sarray_size(v_a_70_);
lean_dec_ref(v_a_70_);
v_r_72_ = lean_box_usize(v_res_71_);
return v_r_72_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_uget___boxed(lean_object* v_a_76_, lean_object* v_i_77_, lean_object* v_a_00___x40___internal___hyg_78_){
_start:
{
size_t v_i_boxed_79_; double v_res_80_; lean_object* v_r_81_; 
v_i_boxed_79_ = lean_unbox_usize(v_i_77_);
lean_dec(v_i_77_);
v_res_80_ = lean_float_array_uget(v_a_76_, v_i_boxed_79_);
lean_dec_ref(v_a_76_);
v_r_81_ = lean_box_float(v_res_80_);
return v_r_81_;
}
}
static lean_object* _init_l_FloatArray_get___auto__1___closed__13(void){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_106_ = ((lean_object*)(l_FloatArray_get___auto__1___closed__12));
v___x_107_ = l_Lean_mkAtom(v___x_106_);
return v___x_107_;
}
}
static lean_object* _init_l_FloatArray_get___auto__1___closed__14(void){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_108_ = lean_obj_once(&l_FloatArray_get___auto__1___closed__13, &l_FloatArray_get___auto__1___closed__13_once, _init_l_FloatArray_get___auto__1___closed__13);
v___x_109_ = ((lean_object*)(l_FloatArray_get___auto__1___closed__5));
v___x_110_ = lean_array_push(v___x_109_, v___x_108_);
return v___x_110_;
}
}
static lean_object* _init_l_FloatArray_get___auto__1___closed__15(void){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_111_ = lean_obj_once(&l_FloatArray_get___auto__1___closed__14, &l_FloatArray_get___auto__1___closed__14_once, _init_l_FloatArray_get___auto__1___closed__14);
v___x_112_ = ((lean_object*)(l_FloatArray_get___auto__1___closed__11));
v___x_113_ = lean_box(2);
v___x_114_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
lean_ctor_set(v___x_114_, 1, v___x_112_);
lean_ctor_set(v___x_114_, 2, v___x_111_);
return v___x_114_;
}
}
static lean_object* _init_l_FloatArray_get___auto__1___closed__16(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_115_ = lean_obj_once(&l_FloatArray_get___auto__1___closed__15, &l_FloatArray_get___auto__1___closed__15_once, _init_l_FloatArray_get___auto__1___closed__15);
v___x_116_ = ((lean_object*)(l_FloatArray_get___auto__1___closed__5));
v___x_117_ = lean_array_push(v___x_116_, v___x_115_);
return v___x_117_;
}
}
static lean_object* _init_l_FloatArray_get___auto__1___closed__17(void){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_118_ = lean_obj_once(&l_FloatArray_get___auto__1___closed__16, &l_FloatArray_get___auto__1___closed__16_once, _init_l_FloatArray_get___auto__1___closed__16);
v___x_119_ = ((lean_object*)(l_FloatArray_get___auto__1___closed__9));
v___x_120_ = lean_box(2);
v___x_121_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_121_, 0, v___x_120_);
lean_ctor_set(v___x_121_, 1, v___x_119_);
lean_ctor_set(v___x_121_, 2, v___x_118_);
return v___x_121_;
}
}
static lean_object* _init_l_FloatArray_get___auto__1___closed__18(void){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_122_ = lean_obj_once(&l_FloatArray_get___auto__1___closed__17, &l_FloatArray_get___auto__1___closed__17_once, _init_l_FloatArray_get___auto__1___closed__17);
v___x_123_ = ((lean_object*)(l_FloatArray_get___auto__1___closed__5));
v___x_124_ = lean_array_push(v___x_123_, v___x_122_);
return v___x_124_;
}
}
static lean_object* _init_l_FloatArray_get___auto__1___closed__19(void){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_125_ = lean_obj_once(&l_FloatArray_get___auto__1___closed__18, &l_FloatArray_get___auto__1___closed__18_once, _init_l_FloatArray_get___auto__1___closed__18);
v___x_126_ = ((lean_object*)(l_FloatArray_get___auto__1___closed__7));
v___x_127_ = lean_box(2);
v___x_128_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
lean_ctor_set(v___x_128_, 1, v___x_126_);
lean_ctor_set(v___x_128_, 2, v___x_125_);
return v___x_128_;
}
}
static lean_object* _init_l_FloatArray_get___auto__1___closed__20(void){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_129_ = lean_obj_once(&l_FloatArray_get___auto__1___closed__19, &l_FloatArray_get___auto__1___closed__19_once, _init_l_FloatArray_get___auto__1___closed__19);
v___x_130_ = ((lean_object*)(l_FloatArray_get___auto__1___closed__5));
v___x_131_ = lean_array_push(v___x_130_, v___x_129_);
return v___x_131_;
}
}
static lean_object* _init_l_FloatArray_get___auto__1___closed__21(void){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_132_ = lean_obj_once(&l_FloatArray_get___auto__1___closed__20, &l_FloatArray_get___auto__1___closed__20_once, _init_l_FloatArray_get___auto__1___closed__20);
v___x_133_ = ((lean_object*)(l_FloatArray_get___auto__1___closed__4));
v___x_134_ = lean_box(2);
v___x_135_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
lean_ctor_set(v___x_135_, 1, v___x_133_);
lean_ctor_set(v___x_135_, 2, v___x_132_);
return v___x_135_;
}
}
static lean_object* _init_l_FloatArray_get___auto__1(void){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = lean_obj_once(&l_FloatArray_get___auto__1___closed__21, &l_FloatArray_get___auto__1___closed__21_once, _init_l_FloatArray_get___auto__1___closed__21);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_get___boxed(lean_object* v_ds_140_, lean_object* v_i_141_, lean_object* v_h_142_){
_start:
{
double v_res_143_; lean_object* v_r_144_; 
v_res_143_ = lean_float_array_fget(v_ds_140_, v_i_141_);
lean_dec(v_i_141_);
lean_dec_ref(v_ds_140_);
v_r_144_ = lean_box_float(v_res_143_);
return v_r_144_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_get_x21___boxed(lean_object* v_a_00___x40___internal___hyg_147_, lean_object* v_a_00___x40___internal___hyg_148_){
_start:
{
double v_res_149_; lean_object* v_r_150_; 
v_res_149_ = lean_float_array_get(v_a_00___x40___internal___hyg_147_, v_a_00___x40___internal___hyg_148_);
lean_dec(v_a_00___x40___internal___hyg_148_);
lean_dec_ref(v_a_00___x40___internal___hyg_147_);
v_r_150_ = lean_box_float(v_res_149_);
return v_r_150_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_get_x3f(lean_object* v_ds_151_, lean_object* v_i_152_){
_start:
{
lean_object* v___x_153_; uint8_t v___x_154_; 
v___x_153_ = lean_float_array_size(v_ds_151_);
v___x_154_ = lean_nat_dec_lt(v_i_152_, v___x_153_);
if (v___x_154_ == 0)
{
lean_object* v___x_155_; 
v___x_155_ = lean_box(0);
return v___x_155_;
}
else
{
double v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_156_ = lean_float_array_fget(v_ds_151_, v_i_152_);
v___x_157_ = lean_box_float(v___x_156_);
v___x_158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_158_, 0, v___x_157_);
return v___x_158_;
}
}
}
LEAN_EXPORT lean_object* l_FloatArray_get_x3f___boxed(lean_object* v_ds_159_, lean_object* v_i_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_FloatArray_get_x3f(v_ds_159_, v_i_160_);
lean_dec(v_i_160_);
lean_dec_ref(v_ds_159_);
return v_res_161_;
}
}
LEAN_EXPORT double l_FloatArray_instGetElemNatFloatLtSize___lam__0(lean_object* v_xs_162_, lean_object* v_i_163_, lean_object* v_h_164_){
_start:
{
double v___x_165_; 
v___x_165_ = lean_float_array_fget(v_xs_162_, v_i_163_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_instGetElemNatFloatLtSize___lam__0___boxed(lean_object* v_xs_166_, lean_object* v_i_167_, lean_object* v_h_168_){
_start:
{
double v_res_169_; lean_object* v_r_170_; 
v_res_169_ = l_FloatArray_instGetElemNatFloatLtSize___lam__0(v_xs_166_, v_i_167_, v_h_168_);
lean_dec(v_i_167_);
lean_dec_ref(v_xs_166_);
v_r_170_ = lean_box_float(v_res_169_);
return v_r_170_;
}
}
LEAN_EXPORT double l_FloatArray_instGetElemUSizeFloatLtNatToNatSize___lam__0(lean_object* v_xs_173_, size_t v_i_174_, lean_object* v_h_175_){
_start:
{
double v___x_176_; 
v___x_176_ = lean_float_array_uget(v_xs_173_, v_i_174_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_instGetElemUSizeFloatLtNatToNatSize___lam__0___boxed(lean_object* v_xs_177_, lean_object* v_i_178_, lean_object* v_h_179_){
_start:
{
size_t v_i_boxed_180_; double v_res_181_; lean_object* v_r_182_; 
v_i_boxed_180_ = lean_unbox_usize(v_i_178_);
lean_dec(v_i_178_);
v_res_181_ = l_FloatArray_instGetElemUSizeFloatLtNatToNatSize___lam__0(v_xs_177_, v_i_boxed_180_, v_h_179_);
lean_dec_ref(v_xs_177_);
v_r_182_ = lean_box_float(v_res_181_);
return v_r_182_;
}
}
static lean_object* _init_l_FloatArray_uset___auto__1(void){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = lean_obj_once(&l_FloatArray_get___auto__1___closed__21, &l_FloatArray_get___auto__1___closed__21_once, _init_l_FloatArray_get___auto__1___closed__21);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_uset___boxed(lean_object* v_a_190_, lean_object* v_i_191_, lean_object* v_a_00___x40___internal___hyg_192_, lean_object* v_h_193_){
_start:
{
size_t v_i_boxed_194_; double v_a_00___x40___internal___hyg_1__boxed_195_; lean_object* v_res_196_; 
v_i_boxed_194_ = lean_unbox_usize(v_i_191_);
lean_dec(v_i_191_);
v_a_00___x40___internal___hyg_1__boxed_195_ = lean_unbox_float(v_a_00___x40___internal___hyg_192_);
lean_dec_ref(v_a_00___x40___internal___hyg_192_);
v_res_196_ = lean_float_array_uset(v_a_190_, v_i_boxed_194_, v_a_00___x40___internal___hyg_1__boxed_195_);
return v_res_196_;
}
}
static lean_object* _init_l_FloatArray_set___auto__1(void){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = lean_obj_once(&l_FloatArray_get___auto__1___closed__21, &l_FloatArray_get___auto__1___closed__21_once, _init_l_FloatArray_get___auto__1___closed__21);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_set___boxed(lean_object* v_ds_202_, lean_object* v_i_203_, lean_object* v_a_00___x40___internal___hyg_204_, lean_object* v_h_205_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_206_; lean_object* v_res_207_; 
v_a_00___x40___internal___hyg_1__boxed_206_ = lean_unbox_float(v_a_00___x40___internal___hyg_204_);
lean_dec_ref(v_a_00___x40___internal___hyg_204_);
v_res_207_ = lean_float_array_fset(v_ds_202_, v_i_203_, v_a_00___x40___internal___hyg_1__boxed_206_);
lean_dec(v_i_203_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_set_x21___boxed(lean_object* v_a_00___x40___internal___hyg_211_, lean_object* v_a_00___x40___internal___hyg_212_, lean_object* v_a_00___x40___internal___hyg_213_){
_start:
{
double v_a_00___x40___internal___hyg_3__boxed_214_; lean_object* v_res_215_; 
v_a_00___x40___internal___hyg_3__boxed_214_ = lean_unbox_float(v_a_00___x40___internal___hyg_213_);
lean_dec_ref(v_a_00___x40___internal___hyg_213_);
v_res_215_ = lean_float_array_set(v_a_00___x40___internal___hyg_211_, v_a_00___x40___internal___hyg_212_, v_a_00___x40___internal___hyg_3__boxed_214_);
lean_dec(v_a_00___x40___internal___hyg_212_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_markLinear___boxed(lean_object* v_ds_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = lean_sarray_mark_linear(v_ds_217_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_propagateMark___boxed(lean_object* v_ds_221_, lean_object* v_es_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = lean_sarray_propagate_mark(v_ds_221_, v_es_222_);
lean_dec_ref(v_ds_221_);
return v_res_223_;
}
}
LEAN_EXPORT uint8_t l_FloatArray_isEmpty(lean_object* v_s_224_){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; uint8_t v___x_227_; 
v___x_225_ = lean_float_array_size(v_s_224_);
v___x_226_ = lean_unsigned_to_nat(0u);
v___x_227_ = lean_nat_dec_eq(v___x_225_, v___x_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_isEmpty___boxed(lean_object* v_s_228_){
_start:
{
uint8_t v_res_229_; lean_object* v_r_230_; 
v_res_229_ = l_FloatArray_isEmpty(v_s_228_);
lean_dec_ref(v_s_228_);
v_r_230_ = lean_box(v_res_229_);
return v_r_230_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_toList_loop(lean_object* v_ds_231_, lean_object* v_i_232_, lean_object* v_r_233_){
_start:
{
lean_object* v___x_234_; uint8_t v___x_235_; 
v___x_234_ = lean_float_array_size(v_ds_231_);
v___x_235_ = lean_nat_dec_lt(v_i_232_, v___x_234_);
if (v___x_235_ == 0)
{
lean_object* v___x_236_; 
lean_dec(v_i_232_);
v___x_236_ = l_List_reverse___redArg(v_r_233_);
return v___x_236_;
}
else
{
lean_object* v___x_237_; lean_object* v___x_238_; double v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_237_ = lean_unsigned_to_nat(1u);
v___x_238_ = lean_nat_add(v_i_232_, v___x_237_);
v___x_239_ = lean_float_array_fget(v_ds_231_, v_i_232_);
lean_dec(v_i_232_);
v___x_240_ = lean_box_float(v___x_239_);
v___x_241_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
lean_ctor_set(v___x_241_, 1, v_r_233_);
v_i_232_ = v___x_238_;
v_r_233_ = v___x_241_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_toList_loop___boxed(lean_object* v_ds_243_, lean_object* v_i_244_, lean_object* v_r_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_toList_loop(v_ds_243_, v_i_244_, v_r_245_);
lean_dec_ref(v_ds_243_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_toList(lean_object* v_ds_247_){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_248_ = lean_unsigned_to_nat(0u);
v___x_249_ = lean_box(0);
v___x_250_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_toList_loop(v_ds_247_, v___x_248_, v___x_249_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_toList___boxed(lean_object* v_ds_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_FloatArray_toList(v_ds_251_);
lean_dec_ref(v_ds_251_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg___lam__0___boxed(lean_object* v_toPure_253_, lean_object* v_i_254_, lean_object* v_inst_255_, lean_object* v_as_256_, lean_object* v_f_257_, lean_object* v_sz_258_, lean_object* v_____do__lift_259_){
_start:
{
size_t v_i_boxed_260_; size_t v_sz_boxed_261_; lean_object* v_res_262_; 
v_i_boxed_260_ = lean_unbox_usize(v_i_254_);
lean_dec(v_i_254_);
v_sz_boxed_261_ = lean_unbox_usize(v_sz_258_);
lean_dec(v_sz_258_);
v_res_262_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg___lam__0(v_toPure_253_, v_i_boxed_260_, v_inst_255_, v_as_256_, v_f_257_, v_sz_boxed_261_, v_____do__lift_259_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg(lean_object* v_inst_263_, lean_object* v_as_264_, lean_object* v_f_265_, size_t v_sz_266_, size_t v_i_267_, lean_object* v_b_268_){
_start:
{
lean_object* v_toApplicative_269_; lean_object* v_toBind_270_; lean_object* v_toPure_271_; uint8_t v___x_272_; 
v_toApplicative_269_ = lean_ctor_get(v_inst_263_, 0);
v_toBind_270_ = lean_ctor_get(v_inst_263_, 1);
lean_inc(v_toBind_270_);
v_toPure_271_ = lean_ctor_get(v_toApplicative_269_, 1);
lean_inc(v_toPure_271_);
v___x_272_ = lean_usize_dec_lt(v_i_267_, v_sz_266_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; 
lean_dec(v_toBind_270_);
lean_dec(v_f_265_);
lean_dec_ref(v_as_264_);
lean_dec_ref(v_inst_263_);
v___x_273_ = lean_apply_2(v_toPure_271_, lean_box(0), v_b_268_);
return v___x_273_;
}
else
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___f_276_; double v_a_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_274_ = lean_box_usize(v_i_267_);
v___x_275_ = lean_box_usize(v_sz_266_);
lean_inc(v_f_265_);
lean_inc_ref(v_as_264_);
v___f_276_ = lean_alloc_closure((void*)(l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_276_, 0, v_toPure_271_);
lean_closure_set(v___f_276_, 1, v___x_274_);
lean_closure_set(v___f_276_, 2, v_inst_263_);
lean_closure_set(v___f_276_, 3, v_as_264_);
lean_closure_set(v___f_276_, 4, v_f_265_);
lean_closure_set(v___f_276_, 5, v___x_275_);
v_a_277_ = lean_float_array_uget(v_as_264_, v_i_267_);
lean_dec_ref(v_as_264_);
v___x_278_ = lean_box_float(v_a_277_);
v___x_279_ = lean_apply_2(v_f_265_, v___x_278_, v_b_268_);
v___x_280_ = lean_apply_4(v_toBind_270_, lean_box(0), lean_box(0), v___x_279_, v___f_276_);
return v___x_280_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg___lam__0(lean_object* v_toPure_281_, size_t v_i_282_, lean_object* v_inst_283_, lean_object* v_as_284_, lean_object* v_f_285_, size_t v_sz_286_, lean_object* v_____do__lift_287_){
_start:
{
if (lean_obj_tag(v_____do__lift_287_) == 0)
{
lean_object* v_a_288_; lean_object* v___x_289_; 
lean_dec(v_f_285_);
lean_dec_ref(v_as_284_);
lean_dec_ref(v_inst_283_);
v_a_288_ = lean_ctor_get(v_____do__lift_287_, 0);
lean_inc(v_a_288_);
lean_dec_ref_known(v_____do__lift_287_, 1);
v___x_289_ = lean_apply_2(v_toPure_281_, lean_box(0), v_a_288_);
return v___x_289_;
}
else
{
lean_object* v_a_290_; size_t v___x_291_; size_t v___x_292_; lean_object* v___x_293_; 
lean_dec(v_toPure_281_);
v_a_290_ = lean_ctor_get(v_____do__lift_287_, 0);
lean_inc(v_a_290_);
lean_dec_ref_known(v_____do__lift_287_, 1);
v___x_291_ = ((size_t)1ULL);
v___x_292_ = lean_usize_add(v_i_282_, v___x_291_);
v___x_293_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg(v_inst_283_, v_as_284_, v_f_285_, v_sz_286_, v___x_292_, v_a_290_);
return v___x_293_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg___boxed(lean_object* v_inst_294_, lean_object* v_as_295_, lean_object* v_f_296_, lean_object* v_sz_297_, lean_object* v_i_298_, lean_object* v_b_299_){
_start:
{
size_t v_sz_boxed_300_; size_t v_i_boxed_301_; lean_object* v_res_302_; 
v_sz_boxed_300_ = lean_unbox_usize(v_sz_297_);
lean_dec(v_sz_297_);
v_i_boxed_301_ = lean_unbox_usize(v_i_298_);
lean_dec(v_i_298_);
v_res_302_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg(v_inst_294_, v_as_295_, v_f_296_, v_sz_boxed_300_, v_i_boxed_301_, v_b_299_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop(lean_object* v_00_u03b2_303_, lean_object* v_m_304_, lean_object* v_inst_305_, lean_object* v_as_306_, lean_object* v_f_307_, size_t v_sz_308_, size_t v_i_309_, lean_object* v_b_310_){
_start:
{
lean_object* v___x_311_; 
v___x_311_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg(v_inst_305_, v_as_306_, v_f_307_, v_sz_308_, v_i_309_, v_b_310_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___boxed(lean_object* v_00_u03b2_312_, lean_object* v_m_313_, lean_object* v_inst_314_, lean_object* v_as_315_, lean_object* v_f_316_, lean_object* v_sz_317_, lean_object* v_i_318_, lean_object* v_b_319_){
_start:
{
size_t v_sz_boxed_320_; size_t v_i_boxed_321_; lean_object* v_res_322_; 
v_sz_boxed_320_ = lean_unbox_usize(v_sz_317_);
lean_dec(v_sz_317_);
v_i_boxed_321_ = lean_unbox_usize(v_i_318_);
lean_dec(v_i_318_);
v_res_322_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop(v_00_u03b2_312_, v_m_313_, v_inst_314_, v_as_315_, v_f_316_, v_sz_boxed_320_, v_i_boxed_321_, v_b_319_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_forInUnsafe___redArg(lean_object* v_inst_323_, lean_object* v_as_324_, lean_object* v_b_325_, lean_object* v_f_326_){
_start:
{
size_t v_sz_327_; size_t v___x_328_; lean_object* v___x_329_; 
v_sz_327_ = lean_sarray_size(v_as_324_);
v___x_328_ = ((size_t)0ULL);
v___x_329_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg(v_inst_323_, v_as_324_, v_f_326_, v_sz_327_, v___x_328_, v_b_325_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_forInUnsafe(lean_object* v_00_u03b2_330_, lean_object* v_m_331_, lean_object* v_inst_332_, lean_object* v_as_333_, lean_object* v_b_334_, lean_object* v_f_335_){
_start:
{
size_t v_sz_336_; size_t v___x_337_; lean_object* v___x_338_; 
v_sz_336_ = lean_sarray_size(v_as_333_);
v___x_337_ = ((size_t)0ULL);
v___x_338_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg(v_inst_332_, v_as_333_, v_f_335_, v_sz_336_, v___x_337_, v_b_334_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop___redArg___lam__0___boxed(lean_object* v_toPure_339_, lean_object* v_inst_340_, lean_object* v_as_341_, lean_object* v_f_342_, lean_object* v_n_343_, lean_object* v_____do__lift_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop___redArg___lam__0(v_toPure_339_, v_inst_340_, v_as_341_, v_f_342_, v_n_343_, v_____do__lift_344_);
lean_dec(v_n_343_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop___redArg(lean_object* v_inst_346_, lean_object* v_as_347_, lean_object* v_f_348_, lean_object* v_i_349_, lean_object* v_b_350_){
_start:
{
lean_object* v_toApplicative_351_; lean_object* v_toBind_352_; lean_object* v_toPure_353_; lean_object* v_zero_354_; uint8_t v_isZero_355_; 
v_toApplicative_351_ = lean_ctor_get(v_inst_346_, 0);
v_toBind_352_ = lean_ctor_get(v_inst_346_, 1);
lean_inc(v_toBind_352_);
v_toPure_353_ = lean_ctor_get(v_toApplicative_351_, 1);
lean_inc(v_toPure_353_);
v_zero_354_ = lean_unsigned_to_nat(0u);
v_isZero_355_ = lean_nat_dec_eq(v_i_349_, v_zero_354_);
if (v_isZero_355_ == 1)
{
lean_object* v___x_356_; 
lean_dec(v_toBind_352_);
lean_dec(v_f_348_);
lean_dec_ref(v_as_347_);
lean_dec_ref(v_inst_346_);
v___x_356_ = lean_apply_2(v_toPure_353_, lean_box(0), v_b_350_);
return v___x_356_;
}
else
{
lean_object* v_one_357_; lean_object* v_n_358_; lean_object* v___f_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; double v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v_one_357_ = lean_unsigned_to_nat(1u);
v_n_358_ = lean_nat_sub(v_i_349_, v_one_357_);
lean_inc(v_n_358_);
lean_inc(v_f_348_);
lean_inc_ref(v_as_347_);
v___f_359_ = lean_alloc_closure((void*)(l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_359_, 0, v_toPure_353_);
lean_closure_set(v___f_359_, 1, v_inst_346_);
lean_closure_set(v___f_359_, 2, v_as_347_);
lean_closure_set(v___f_359_, 3, v_f_348_);
lean_closure_set(v___f_359_, 4, v_n_358_);
v___x_360_ = lean_float_array_size(v_as_347_);
v___x_361_ = lean_nat_sub(v___x_360_, v_one_357_);
v___x_362_ = lean_nat_sub(v___x_361_, v_n_358_);
lean_dec(v_n_358_);
lean_dec(v___x_361_);
v___x_363_ = lean_float_array_fget(v_as_347_, v___x_362_);
lean_dec(v___x_362_);
lean_dec_ref(v_as_347_);
v___x_364_ = lean_box_float(v___x_363_);
v___x_365_ = lean_apply_2(v_f_348_, v___x_364_, v_b_350_);
v___x_366_ = lean_apply_4(v_toBind_352_, lean_box(0), lean_box(0), v___x_365_, v___f_359_);
return v___x_366_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop___redArg___lam__0(lean_object* v_toPure_367_, lean_object* v_inst_368_, lean_object* v_as_369_, lean_object* v_f_370_, lean_object* v_n_371_, lean_object* v_____do__lift_372_){
_start:
{
if (lean_obj_tag(v_____do__lift_372_) == 0)
{
lean_object* v_a_373_; lean_object* v___x_374_; 
lean_dec(v_f_370_);
lean_dec_ref(v_as_369_);
lean_dec_ref(v_inst_368_);
v_a_373_ = lean_ctor_get(v_____do__lift_372_, 0);
lean_inc(v_a_373_);
lean_dec_ref_known(v_____do__lift_372_, 1);
v___x_374_ = lean_apply_2(v_toPure_367_, lean_box(0), v_a_373_);
return v___x_374_;
}
else
{
lean_object* v_a_375_; lean_object* v___x_376_; 
lean_dec(v_toPure_367_);
v_a_375_ = lean_ctor_get(v_____do__lift_372_, 0);
lean_inc(v_a_375_);
lean_dec_ref_known(v_____do__lift_372_, 1);
v___x_376_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop___redArg(v_inst_368_, v_as_369_, v_f_370_, v_n_371_, v_a_375_);
return v___x_376_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop___redArg___boxed(lean_object* v_inst_377_, lean_object* v_as_378_, lean_object* v_f_379_, lean_object* v_i_380_, lean_object* v_b_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop___redArg(v_inst_377_, v_as_378_, v_f_379_, v_i_380_, v_b_381_);
lean_dec(v_i_380_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop(lean_object* v_00_u03b2_383_, lean_object* v_m_384_, lean_object* v_inst_385_, lean_object* v_as_386_, lean_object* v_f_387_, lean_object* v_i_388_, lean_object* v_h_389_, lean_object* v_b_390_){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop___redArg(v_inst_385_, v_as_386_, v_f_387_, v_i_388_, v_b_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop___boxed(lean_object* v_00_u03b2_392_, lean_object* v_m_393_, lean_object* v_inst_394_, lean_object* v_as_395_, lean_object* v_f_396_, lean_object* v_i_397_, lean_object* v_h_398_, lean_object* v_b_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop(v_00_u03b2_392_, v_m_393_, v_inst_394_, v_as_395_, v_f_396_, v_i_397_, v_h_398_, v_b_399_);
lean_dec(v_i_397_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_instForInFloatOfMonad___redArg___lam__0(lean_object* v_inst_401_, lean_object* v_00_u03b2_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_){
_start:
{
size_t v_sz_406_; size_t v___x_407_; lean_object* v___x_408_; 
v_sz_406_ = lean_sarray_size(v___y_403_);
v___x_407_ = ((size_t)0ULL);
v___x_408_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg(v_inst_401_, v___y_403_, v___y_405_, v_sz_406_, v___x_407_, v___y_404_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_instForInFloatOfMonad___redArg(lean_object* v_inst_409_){
_start:
{
lean_object* v___f_410_; 
v___f_410_ = lean_alloc_closure((void*)(l_FloatArray_instForInFloatOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_410_, 0, v_inst_409_);
return v___f_410_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_instForInFloatOfMonad(lean_object* v_m_411_, lean_object* v_inst_412_){
_start:
{
lean_object* v___f_413_; 
v___f_413_ = lean_alloc_closure((void*)(l_FloatArray_instForInFloatOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_413_, 0, v_inst_412_);
return v___f_413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg___lam__0___boxed(lean_object* v_i_414_, lean_object* v_inst_415_, lean_object* v_f_416_, lean_object* v_as_417_, lean_object* v_stop_418_, lean_object* v_____do__lift_419_){
_start:
{
size_t v_i_boxed_420_; size_t v_stop_boxed_421_; lean_object* v_res_422_; 
v_i_boxed_420_ = lean_unbox_usize(v_i_414_);
lean_dec(v_i_414_);
v_stop_boxed_421_ = lean_unbox_usize(v_stop_418_);
lean_dec(v_stop_418_);
v_res_422_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg___lam__0(v_i_boxed_420_, v_inst_415_, v_f_416_, v_as_417_, v_stop_boxed_421_, v_____do__lift_419_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(lean_object* v_inst_423_, lean_object* v_f_424_, lean_object* v_as_425_, size_t v_i_426_, size_t v_stop_427_, lean_object* v_b_428_){
_start:
{
lean_object* v_toApplicative_429_; lean_object* v_toBind_430_; lean_object* v_toPure_431_; uint8_t v___x_432_; 
v_toApplicative_429_ = lean_ctor_get(v_inst_423_, 0);
v_toBind_430_ = lean_ctor_get(v_inst_423_, 1);
lean_inc(v_toBind_430_);
v_toPure_431_ = lean_ctor_get(v_toApplicative_429_, 1);
v___x_432_ = lean_usize_dec_eq(v_i_426_, v_stop_427_);
if (v___x_432_ == 0)
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___f_435_; double v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_433_ = lean_box_usize(v_i_426_);
v___x_434_ = lean_box_usize(v_stop_427_);
lean_inc_ref(v_as_425_);
lean_inc(v_f_424_);
v___f_435_ = lean_alloc_closure((void*)(l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_435_, 0, v___x_433_);
lean_closure_set(v___f_435_, 1, v_inst_423_);
lean_closure_set(v___f_435_, 2, v_f_424_);
lean_closure_set(v___f_435_, 3, v_as_425_);
lean_closure_set(v___f_435_, 4, v___x_434_);
v___x_436_ = lean_float_array_uget(v_as_425_, v_i_426_);
lean_dec_ref(v_as_425_);
v___x_437_ = lean_box_float(v___x_436_);
v___x_438_ = lean_apply_2(v_f_424_, v_b_428_, v___x_437_);
v___x_439_ = lean_apply_4(v_toBind_430_, lean_box(0), lean_box(0), v___x_438_, v___f_435_);
return v___x_439_;
}
else
{
lean_object* v___x_440_; 
lean_inc(v_toPure_431_);
lean_dec(v_toBind_430_);
lean_dec_ref(v_as_425_);
lean_dec(v_f_424_);
lean_dec_ref(v_inst_423_);
v___x_440_ = lean_apply_2(v_toPure_431_, lean_box(0), v_b_428_);
return v___x_440_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg___lam__0(size_t v_i_441_, lean_object* v_inst_442_, lean_object* v_f_443_, lean_object* v_as_444_, size_t v_stop_445_, lean_object* v_____do__lift_446_){
_start:
{
size_t v___x_447_; size_t v___x_448_; lean_object* v___x_449_; 
v___x_447_ = ((size_t)1ULL);
v___x_448_ = lean_usize_add(v_i_441_, v___x_447_);
v___x_449_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(v_inst_442_, v_f_443_, v_as_444_, v___x_448_, v_stop_445_, v_____do__lift_446_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg___boxed(lean_object* v_inst_450_, lean_object* v_f_451_, lean_object* v_as_452_, lean_object* v_i_453_, lean_object* v_stop_454_, lean_object* v_b_455_){
_start:
{
size_t v_i_boxed_456_; size_t v_stop_boxed_457_; lean_object* v_res_458_; 
v_i_boxed_456_ = lean_unbox_usize(v_i_453_);
lean_dec(v_i_453_);
v_stop_boxed_457_ = lean_unbox_usize(v_stop_454_);
lean_dec(v_stop_454_);
v_res_458_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(v_inst_450_, v_f_451_, v_as_452_, v_i_boxed_456_, v_stop_boxed_457_, v_b_455_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold(lean_object* v_00_u03b2_459_, lean_object* v_m_460_, lean_object* v_inst_461_, lean_object* v_f_462_, lean_object* v_as_463_, size_t v_i_464_, size_t v_stop_465_, lean_object* v_b_466_){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(v_inst_461_, v_f_462_, v_as_463_, v_i_464_, v_stop_465_, v_b_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___boxed(lean_object* v_00_u03b2_468_, lean_object* v_m_469_, lean_object* v_inst_470_, lean_object* v_f_471_, lean_object* v_as_472_, lean_object* v_i_473_, lean_object* v_stop_474_, lean_object* v_b_475_){
_start:
{
size_t v_i_boxed_476_; size_t v_stop_boxed_477_; lean_object* v_res_478_; 
v_i_boxed_476_ = lean_unbox_usize(v_i_473_);
lean_dec(v_i_473_);
v_stop_boxed_477_ = lean_unbox_usize(v_stop_474_);
lean_dec(v_stop_474_);
v_res_478_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold(v_00_u03b2_468_, v_m_469_, v_inst_470_, v_f_471_, v_as_472_, v_i_boxed_476_, v_stop_boxed_477_, v_b_475_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_foldlMUnsafe___redArg(lean_object* v_inst_479_, lean_object* v_f_480_, lean_object* v_init_481_, lean_object* v_as_482_, lean_object* v_start_483_, lean_object* v_stop_484_){
_start:
{
lean_object* v_toApplicative_485_; lean_object* v_toPure_486_; uint8_t v___x_487_; 
v_toApplicative_485_ = lean_ctor_get(v_inst_479_, 0);
v_toPure_486_ = lean_ctor_get(v_toApplicative_485_, 1);
v___x_487_ = lean_nat_dec_lt(v_start_483_, v_stop_484_);
if (v___x_487_ == 0)
{
lean_object* v___x_488_; 
lean_inc(v_toPure_486_);
lean_dec_ref(v_as_482_);
lean_dec(v_f_480_);
lean_dec_ref(v_inst_479_);
v___x_488_ = lean_apply_2(v_toPure_486_, lean_box(0), v_init_481_);
return v___x_488_;
}
else
{
lean_object* v___x_489_; uint8_t v___x_490_; 
v___x_489_ = lean_float_array_size(v_as_482_);
v___x_490_ = lean_nat_dec_le(v_stop_484_, v___x_489_);
if (v___x_490_ == 0)
{
uint8_t v___x_491_; 
v___x_491_ = lean_nat_dec_lt(v_start_483_, v___x_489_);
if (v___x_491_ == 0)
{
lean_object* v___x_492_; 
lean_inc(v_toPure_486_);
lean_dec_ref(v_as_482_);
lean_dec(v_f_480_);
lean_dec_ref(v_inst_479_);
v___x_492_ = lean_apply_2(v_toPure_486_, lean_box(0), v_init_481_);
return v___x_492_;
}
else
{
size_t v___x_493_; size_t v___x_494_; lean_object* v___x_495_; 
v___x_493_ = lean_usize_of_nat(v_start_483_);
v___x_494_ = lean_usize_of_nat(v___x_489_);
v___x_495_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(v_inst_479_, v_f_480_, v_as_482_, v___x_493_, v___x_494_, v_init_481_);
return v___x_495_;
}
}
else
{
size_t v___x_496_; size_t v___x_497_; lean_object* v___x_498_; 
v___x_496_ = lean_usize_of_nat(v_start_483_);
v___x_497_ = lean_usize_of_nat(v_stop_484_);
v___x_498_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(v_inst_479_, v_f_480_, v_as_482_, v___x_496_, v___x_497_, v_init_481_);
return v___x_498_;
}
}
}
}
LEAN_EXPORT lean_object* l_FloatArray_foldlMUnsafe___redArg___boxed(lean_object* v_inst_499_, lean_object* v_f_500_, lean_object* v_init_501_, lean_object* v_as_502_, lean_object* v_start_503_, lean_object* v_stop_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_FloatArray_foldlMUnsafe___redArg(v_inst_499_, v_f_500_, v_init_501_, v_as_502_, v_start_503_, v_stop_504_);
lean_dec(v_stop_504_);
lean_dec(v_start_503_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_foldlMUnsafe(lean_object* v_00_u03b2_506_, lean_object* v_m_507_, lean_object* v_inst_508_, lean_object* v_f_509_, lean_object* v_init_510_, lean_object* v_as_511_, lean_object* v_start_512_, lean_object* v_stop_513_){
_start:
{
lean_object* v_toApplicative_514_; lean_object* v_toPure_515_; uint8_t v___x_516_; 
v_toApplicative_514_ = lean_ctor_get(v_inst_508_, 0);
v_toPure_515_ = lean_ctor_get(v_toApplicative_514_, 1);
v___x_516_ = lean_nat_dec_lt(v_start_512_, v_stop_513_);
if (v___x_516_ == 0)
{
lean_object* v___x_517_; 
lean_inc(v_toPure_515_);
lean_dec_ref(v_as_511_);
lean_dec(v_f_509_);
lean_dec_ref(v_inst_508_);
v___x_517_ = lean_apply_2(v_toPure_515_, lean_box(0), v_init_510_);
return v___x_517_;
}
else
{
lean_object* v___x_518_; uint8_t v___x_519_; 
v___x_518_ = lean_float_array_size(v_as_511_);
v___x_519_ = lean_nat_dec_le(v_stop_513_, v___x_518_);
if (v___x_519_ == 0)
{
uint8_t v___x_520_; 
v___x_520_ = lean_nat_dec_lt(v_start_512_, v___x_518_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; 
lean_inc(v_toPure_515_);
lean_dec_ref(v_as_511_);
lean_dec(v_f_509_);
lean_dec_ref(v_inst_508_);
v___x_521_ = lean_apply_2(v_toPure_515_, lean_box(0), v_init_510_);
return v___x_521_;
}
else
{
size_t v___x_522_; size_t v___x_523_; lean_object* v___x_524_; 
v___x_522_ = lean_usize_of_nat(v_start_512_);
v___x_523_ = lean_usize_of_nat(v___x_518_);
v___x_524_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(v_inst_508_, v_f_509_, v_as_511_, v___x_522_, v___x_523_, v_init_510_);
return v___x_524_;
}
}
else
{
size_t v___x_525_; size_t v___x_526_; lean_object* v___x_527_; 
v___x_525_ = lean_usize_of_nat(v_start_512_);
v___x_526_ = lean_usize_of_nat(v_stop_513_);
v___x_527_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(v_inst_508_, v_f_509_, v_as_511_, v___x_525_, v___x_526_, v_init_510_);
return v___x_527_;
}
}
}
}
LEAN_EXPORT lean_object* l_FloatArray_foldlMUnsafe___boxed(lean_object* v_00_u03b2_528_, lean_object* v_m_529_, lean_object* v_inst_530_, lean_object* v_f_531_, lean_object* v_init_532_, lean_object* v_as_533_, lean_object* v_start_534_, lean_object* v_stop_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_FloatArray_foldlMUnsafe(v_00_u03b2_528_, v_m_529_, v_inst_530_, v_f_531_, v_init_532_, v_as_533_, v_start_534_, v_stop_535_);
lean_dec(v_stop_535_);
lean_dec(v_start_534_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop___redArg___lam__0___boxed(lean_object* v_j_537_, lean_object* v_inst_538_, lean_object* v_f_539_, lean_object* v_as_540_, lean_object* v_stop_541_, lean_object* v_n_542_, lean_object* v_____do__lift_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop___redArg___lam__0(v_j_537_, v_inst_538_, v_f_539_, v_as_540_, v_stop_541_, v_n_542_, v_____do__lift_543_);
lean_dec(v_n_542_);
lean_dec(v_j_537_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop___redArg(lean_object* v_inst_545_, lean_object* v_f_546_, lean_object* v_as_547_, lean_object* v_stop_548_, lean_object* v_i_549_, lean_object* v_j_550_, lean_object* v_b_551_){
_start:
{
lean_object* v_toApplicative_552_; lean_object* v_toBind_553_; lean_object* v_toPure_554_; uint8_t v___x_555_; 
v_toApplicative_552_ = lean_ctor_get(v_inst_545_, 0);
v_toBind_553_ = lean_ctor_get(v_inst_545_, 1);
lean_inc(v_toBind_553_);
v_toPure_554_ = lean_ctor_get(v_toApplicative_552_, 1);
v___x_555_ = lean_nat_dec_lt(v_j_550_, v_stop_548_);
if (v___x_555_ == 0)
{
lean_object* v___x_556_; 
lean_inc(v_toPure_554_);
lean_dec(v_toBind_553_);
lean_dec(v_j_550_);
lean_dec(v_stop_548_);
lean_dec_ref(v_as_547_);
lean_dec(v_f_546_);
lean_dec_ref(v_inst_545_);
v___x_556_ = lean_apply_2(v_toPure_554_, lean_box(0), v_b_551_);
return v___x_556_;
}
else
{
lean_object* v_zero_557_; uint8_t v_isZero_558_; 
v_zero_557_ = lean_unsigned_to_nat(0u);
v_isZero_558_ = lean_nat_dec_eq(v_i_549_, v_zero_557_);
if (v_isZero_558_ == 1)
{
lean_object* v___x_559_; 
lean_inc(v_toPure_554_);
lean_dec(v_toBind_553_);
lean_dec(v_j_550_);
lean_dec(v_stop_548_);
lean_dec_ref(v_as_547_);
lean_dec(v_f_546_);
lean_dec_ref(v_inst_545_);
v___x_559_ = lean_apply_2(v_toPure_554_, lean_box(0), v_b_551_);
return v___x_559_;
}
else
{
lean_object* v_one_560_; lean_object* v_n_561_; lean_object* v___f_562_; double v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v_one_560_ = lean_unsigned_to_nat(1u);
v_n_561_ = lean_nat_sub(v_i_549_, v_one_560_);
lean_inc_ref(v_as_547_);
lean_inc(v_f_546_);
lean_inc(v_j_550_);
v___f_562_ = lean_alloc_closure((void*)(l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_562_, 0, v_j_550_);
lean_closure_set(v___f_562_, 1, v_inst_545_);
lean_closure_set(v___f_562_, 2, v_f_546_);
lean_closure_set(v___f_562_, 3, v_as_547_);
lean_closure_set(v___f_562_, 4, v_stop_548_);
lean_closure_set(v___f_562_, 5, v_n_561_);
v___x_563_ = lean_float_array_fget(v_as_547_, v_j_550_);
lean_dec(v_j_550_);
lean_dec_ref(v_as_547_);
v___x_564_ = lean_box_float(v___x_563_);
v___x_565_ = lean_apply_2(v_f_546_, v_b_551_, v___x_564_);
v___x_566_ = lean_apply_4(v_toBind_553_, lean_box(0), lean_box(0), v___x_565_, v___f_562_);
return v___x_566_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop___redArg___lam__0(lean_object* v_j_567_, lean_object* v_inst_568_, lean_object* v_f_569_, lean_object* v_as_570_, lean_object* v_stop_571_, lean_object* v_n_572_, lean_object* v_____do__lift_573_){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_574_ = lean_unsigned_to_nat(1u);
v___x_575_ = lean_nat_add(v_j_567_, v___x_574_);
v___x_576_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop___redArg(v_inst_568_, v_f_569_, v_as_570_, v_stop_571_, v_n_572_, v___x_575_, v_____do__lift_573_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop___redArg___boxed(lean_object* v_inst_577_, lean_object* v_f_578_, lean_object* v_as_579_, lean_object* v_stop_580_, lean_object* v_i_581_, lean_object* v_j_582_, lean_object* v_b_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop___redArg(v_inst_577_, v_f_578_, v_as_579_, v_stop_580_, v_i_581_, v_j_582_, v_b_583_);
lean_dec(v_i_581_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop(lean_object* v_00_u03b2_585_, lean_object* v_m_586_, lean_object* v_inst_587_, lean_object* v_f_588_, lean_object* v_as_589_, lean_object* v_stop_590_, lean_object* v_h_591_, lean_object* v_i_592_, lean_object* v_j_593_, lean_object* v_b_594_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop___redArg(v_inst_587_, v_f_588_, v_as_589_, v_stop_590_, v_i_592_, v_j_593_, v_b_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop___boxed(lean_object* v_00_u03b2_596_, lean_object* v_m_597_, lean_object* v_inst_598_, lean_object* v_f_599_, lean_object* v_as_600_, lean_object* v_stop_601_, lean_object* v_h_602_, lean_object* v_i_603_, lean_object* v_j_604_, lean_object* v_b_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop(v_00_u03b2_596_, v_m_597_, v_inst_598_, v_f_599_, v_as_600_, v_stop_601_, v_h_602_, v_i_603_, v_j_604_, v_b_605_);
lean_dec(v_i_603_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_foldl___redArg___lam__0(lean_object* v_f_607_, lean_object* v_x1_608_, double v_x2_609_){
_start:
{
lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_610_ = lean_box_float(v_x2_609_);
v___x_611_ = lean_apply_2(v_f_607_, v_x1_608_, v___x_610_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_foldl___redArg___lam__0___boxed(lean_object* v_f_612_, lean_object* v_x1_613_, lean_object* v_x2_614_){
_start:
{
double v_x2_185__boxed_615_; lean_object* v_res_616_; 
v_x2_185__boxed_615_ = lean_unbox_float(v_x2_614_);
lean_dec_ref(v_x2_614_);
v_res_616_ = l_FloatArray_foldl___redArg___lam__0(v_f_612_, v_x1_613_, v_x2_185__boxed_615_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_foldl___redArg(lean_object* v_f_636_, lean_object* v_init_637_, lean_object* v_as_638_, lean_object* v_start_639_, lean_object* v_stop_640_){
_start:
{
lean_object* v___x_641_; uint8_t v___x_642_; 
v___x_641_ = ((lean_object*)(l_FloatArray_foldl___redArg___closed__9));
v___x_642_ = lean_nat_dec_lt(v_start_639_, v_stop_640_);
if (v___x_642_ == 0)
{
lean_dec_ref(v_as_638_);
lean_dec(v_f_636_);
return v_init_637_;
}
else
{
lean_object* v___f_643_; lean_object* v___x_644_; uint8_t v___x_645_; 
v___f_643_ = lean_alloc_closure((void*)(l_FloatArray_foldl___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_643_, 0, v_f_636_);
v___x_644_ = lean_float_array_size(v_as_638_);
v___x_645_ = lean_nat_dec_le(v_stop_640_, v___x_644_);
if (v___x_645_ == 0)
{
uint8_t v___x_646_; 
v___x_646_ = lean_nat_dec_lt(v_start_639_, v___x_644_);
if (v___x_646_ == 0)
{
lean_dec_ref(v___f_643_);
lean_dec_ref(v_as_638_);
return v_init_637_;
}
else
{
size_t v___x_647_; size_t v___x_648_; lean_object* v___x_649_; 
v___x_647_ = lean_usize_of_nat(v_start_639_);
v___x_648_ = lean_usize_of_nat(v___x_644_);
v___x_649_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(v___x_641_, v___f_643_, v_as_638_, v___x_647_, v___x_648_, v_init_637_);
return v___x_649_;
}
}
else
{
size_t v___x_650_; size_t v___x_651_; lean_object* v___x_652_; 
v___x_650_ = lean_usize_of_nat(v_start_639_);
v___x_651_ = lean_usize_of_nat(v_stop_640_);
v___x_652_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(v___x_641_, v___f_643_, v_as_638_, v___x_650_, v___x_651_, v_init_637_);
return v___x_652_;
}
}
}
}
LEAN_EXPORT lean_object* l_FloatArray_foldl___redArg___boxed(lean_object* v_f_653_, lean_object* v_init_654_, lean_object* v_as_655_, lean_object* v_start_656_, lean_object* v_stop_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_FloatArray_foldl___redArg(v_f_653_, v_init_654_, v_as_655_, v_start_656_, v_stop_657_);
lean_dec(v_stop_657_);
lean_dec(v_start_656_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_foldl(lean_object* v_00_u03b2_659_, lean_object* v_f_660_, lean_object* v_init_661_, lean_object* v_as_662_, lean_object* v_start_663_, lean_object* v_stop_664_){
_start:
{
lean_object* v___x_665_; uint8_t v___x_666_; 
v___x_665_ = ((lean_object*)(l_FloatArray_foldl___redArg___closed__9));
v___x_666_ = lean_nat_dec_lt(v_start_663_, v_stop_664_);
if (v___x_666_ == 0)
{
lean_dec_ref(v_as_662_);
lean_dec(v_f_660_);
return v_init_661_;
}
else
{
lean_object* v___f_667_; lean_object* v___x_668_; uint8_t v___x_669_; 
v___f_667_ = lean_alloc_closure((void*)(l_FloatArray_foldl___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_667_, 0, v_f_660_);
v___x_668_ = lean_float_array_size(v_as_662_);
v___x_669_ = lean_nat_dec_le(v_stop_664_, v___x_668_);
if (v___x_669_ == 0)
{
uint8_t v___x_670_; 
v___x_670_ = lean_nat_dec_lt(v_start_663_, v___x_668_);
if (v___x_670_ == 0)
{
lean_dec_ref(v___f_667_);
lean_dec_ref(v_as_662_);
return v_init_661_;
}
else
{
size_t v___x_671_; size_t v___x_672_; lean_object* v___x_673_; 
v___x_671_ = lean_usize_of_nat(v_start_663_);
v___x_672_ = lean_usize_of_nat(v___x_668_);
v___x_673_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(v___x_665_, v___f_667_, v_as_662_, v___x_671_, v___x_672_, v_init_661_);
return v___x_673_;
}
}
else
{
size_t v___x_674_; size_t v___x_675_; lean_object* v___x_676_; 
v___x_674_ = lean_usize_of_nat(v_start_663_);
v___x_675_ = lean_usize_of_nat(v_stop_664_);
v___x_676_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(v___x_665_, v___f_667_, v_as_662_, v___x_674_, v___x_675_, v_init_661_);
return v___x_676_;
}
}
}
}
LEAN_EXPORT lean_object* l_FloatArray_foldl___boxed(lean_object* v_00_u03b2_677_, lean_object* v_f_678_, lean_object* v_init_679_, lean_object* v_as_680_, lean_object* v_start_681_, lean_object* v_stop_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_FloatArray_foldl(v_00_u03b2_677_, v_f_678_, v_init_679_, v_as_680_, v_start_681_, v_stop_682_);
lean_dec(v_stop_682_);
lean_dec(v_start_681_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__List_toFloatArray_loop(lean_object* v_x_684_, lean_object* v_x_685_){
_start:
{
if (lean_obj_tag(v_x_684_) == 0)
{
return v_x_685_;
}
else
{
lean_object* v_head_686_; lean_object* v_tail_687_; double v___x_688_; lean_object* v___x_689_; 
v_head_686_ = lean_ctor_get(v_x_684_, 0);
v_tail_687_ = lean_ctor_get(v_x_684_, 1);
v___x_688_ = lean_unbox_float(v_head_686_);
v___x_689_ = lean_float_array_push(v_x_685_, v___x_688_);
v_x_684_ = v_tail_687_;
v_x_685_ = v___x_689_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__List_toFloatArray_loop___boxed(lean_object* v_x_691_, lean_object* v_x_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l___private_Init_Data_FloatArray_Basic_0__List_toFloatArray_loop(v_x_691_, v_x_692_);
lean_dec(v_x_691_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_List_toFloatArray(lean_object* v_ds_694_){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_695_ = l_FloatArray_empty;
v___x_696_ = l___private_Init_Data_FloatArray_Basic_0__List_toFloatArray_loop(v_ds_694_, v___x_695_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_List_toFloatArray___boxed(lean_object* v_ds_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l_List_toFloatArray(v_ds_697_);
lean_dec(v_ds_697_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l_instToStringFloatArray___lam__0(lean_object* v___x_699_, lean_object* v_ds_700_){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_701_ = l_FloatArray_toList(v_ds_700_);
v___x_702_ = l_List_toString___redArg(v___x_699_, v___x_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_instToStringFloatArray___lam__0___boxed(lean_object* v___x_703_, lean_object* v_ds_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l_instToStringFloatArray___lam__0(v___x_703_, v_ds_704_);
lean_dec_ref(v_ds_704_);
return v_res_705_;
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
