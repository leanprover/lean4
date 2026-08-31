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
LEAN_EXPORT uint8_t l_FloatArray_isEmpty(lean_object* v_s_216_){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; uint8_t v___x_219_; 
v___x_217_ = lean_float_array_size(v_s_216_);
v___x_218_ = lean_unsigned_to_nat(0u);
v___x_219_ = lean_nat_dec_eq(v___x_217_, v___x_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_isEmpty___boxed(lean_object* v_s_220_){
_start:
{
uint8_t v_res_221_; lean_object* v_r_222_; 
v_res_221_ = l_FloatArray_isEmpty(v_s_220_);
lean_dec_ref(v_s_220_);
v_r_222_ = lean_box(v_res_221_);
return v_r_222_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_toList_loop(lean_object* v_ds_223_, lean_object* v_i_224_, lean_object* v_r_225_){
_start:
{
lean_object* v___x_226_; uint8_t v___x_227_; 
v___x_226_ = lean_float_array_size(v_ds_223_);
v___x_227_ = lean_nat_dec_lt(v_i_224_, v___x_226_);
if (v___x_227_ == 0)
{
lean_object* v___x_228_; 
lean_dec(v_i_224_);
v___x_228_ = l_List_reverse___redArg(v_r_225_);
return v___x_228_;
}
else
{
lean_object* v___x_229_; lean_object* v___x_230_; double v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_229_ = lean_unsigned_to_nat(1u);
v___x_230_ = lean_nat_add(v_i_224_, v___x_229_);
v___x_231_ = lean_float_array_fget(v_ds_223_, v_i_224_);
lean_dec(v_i_224_);
v___x_232_ = lean_box_float(v___x_231_);
v___x_233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_233_, 0, v___x_232_);
lean_ctor_set(v___x_233_, 1, v_r_225_);
v_i_224_ = v___x_230_;
v_r_225_ = v___x_233_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_toList_loop___boxed(lean_object* v_ds_235_, lean_object* v_i_236_, lean_object* v_r_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_toList_loop(v_ds_235_, v_i_236_, v_r_237_);
lean_dec_ref(v_ds_235_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_toList(lean_object* v_ds_239_){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_240_ = lean_unsigned_to_nat(0u);
v___x_241_ = lean_box(0);
v___x_242_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_toList_loop(v_ds_239_, v___x_240_, v___x_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_toList___boxed(lean_object* v_ds_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_FloatArray_toList(v_ds_243_);
lean_dec_ref(v_ds_243_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg___lam__0___boxed(lean_object* v_toPure_245_, lean_object* v_i_246_, lean_object* v_inst_247_, lean_object* v_as_248_, lean_object* v_f_249_, lean_object* v_sz_250_, lean_object* v_____do__lift_251_){
_start:
{
size_t v_i_boxed_252_; size_t v_sz_boxed_253_; lean_object* v_res_254_; 
v_i_boxed_252_ = lean_unbox_usize(v_i_246_);
lean_dec(v_i_246_);
v_sz_boxed_253_ = lean_unbox_usize(v_sz_250_);
lean_dec(v_sz_250_);
v_res_254_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg___lam__0(v_toPure_245_, v_i_boxed_252_, v_inst_247_, v_as_248_, v_f_249_, v_sz_boxed_253_, v_____do__lift_251_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg(lean_object* v_inst_255_, lean_object* v_as_256_, lean_object* v_f_257_, size_t v_sz_258_, size_t v_i_259_, lean_object* v_b_260_){
_start:
{
lean_object* v_toApplicative_261_; lean_object* v_toBind_262_; lean_object* v_toPure_263_; uint8_t v___x_264_; 
v_toApplicative_261_ = lean_ctor_get(v_inst_255_, 0);
v_toBind_262_ = lean_ctor_get(v_inst_255_, 1);
lean_inc(v_toBind_262_);
v_toPure_263_ = lean_ctor_get(v_toApplicative_261_, 1);
lean_inc(v_toPure_263_);
v___x_264_ = lean_usize_dec_lt(v_i_259_, v_sz_258_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; 
lean_dec(v_toBind_262_);
lean_dec(v_f_257_);
lean_dec_ref(v_as_256_);
lean_dec_ref(v_inst_255_);
v___x_265_ = lean_apply_2(v_toPure_263_, lean_box(0), v_b_260_);
return v___x_265_;
}
else
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___f_268_; double v_a_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_266_ = lean_box_usize(v_i_259_);
v___x_267_ = lean_box_usize(v_sz_258_);
lean_inc(v_f_257_);
lean_inc_ref(v_as_256_);
v___f_268_ = lean_alloc_closure((void*)(l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_268_, 0, v_toPure_263_);
lean_closure_set(v___f_268_, 1, v___x_266_);
lean_closure_set(v___f_268_, 2, v_inst_255_);
lean_closure_set(v___f_268_, 3, v_as_256_);
lean_closure_set(v___f_268_, 4, v_f_257_);
lean_closure_set(v___f_268_, 5, v___x_267_);
v_a_269_ = lean_float_array_uget(v_as_256_, v_i_259_);
lean_dec_ref(v_as_256_);
v___x_270_ = lean_box_float(v_a_269_);
v___x_271_ = lean_apply_2(v_f_257_, v___x_270_, v_b_260_);
v___x_272_ = lean_apply_4(v_toBind_262_, lean_box(0), lean_box(0), v___x_271_, v___f_268_);
return v___x_272_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg___lam__0(lean_object* v_toPure_273_, size_t v_i_274_, lean_object* v_inst_275_, lean_object* v_as_276_, lean_object* v_f_277_, size_t v_sz_278_, lean_object* v_____do__lift_279_){
_start:
{
if (lean_obj_tag(v_____do__lift_279_) == 0)
{
lean_object* v_a_280_; lean_object* v___x_281_; 
lean_dec(v_f_277_);
lean_dec_ref(v_as_276_);
lean_dec_ref(v_inst_275_);
v_a_280_ = lean_ctor_get(v_____do__lift_279_, 0);
lean_inc(v_a_280_);
lean_dec_ref_known(v_____do__lift_279_, 1);
v___x_281_ = lean_apply_2(v_toPure_273_, lean_box(0), v_a_280_);
return v___x_281_;
}
else
{
lean_object* v_a_282_; size_t v___x_283_; size_t v___x_284_; lean_object* v___x_285_; 
lean_dec(v_toPure_273_);
v_a_282_ = lean_ctor_get(v_____do__lift_279_, 0);
lean_inc(v_a_282_);
lean_dec_ref_known(v_____do__lift_279_, 1);
v___x_283_ = ((size_t)1ULL);
v___x_284_ = lean_usize_add(v_i_274_, v___x_283_);
v___x_285_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg(v_inst_275_, v_as_276_, v_f_277_, v_sz_278_, v___x_284_, v_a_282_);
return v___x_285_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg___boxed(lean_object* v_inst_286_, lean_object* v_as_287_, lean_object* v_f_288_, lean_object* v_sz_289_, lean_object* v_i_290_, lean_object* v_b_291_){
_start:
{
size_t v_sz_boxed_292_; size_t v_i_boxed_293_; lean_object* v_res_294_; 
v_sz_boxed_292_ = lean_unbox_usize(v_sz_289_);
lean_dec(v_sz_289_);
v_i_boxed_293_ = lean_unbox_usize(v_i_290_);
lean_dec(v_i_290_);
v_res_294_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg(v_inst_286_, v_as_287_, v_f_288_, v_sz_boxed_292_, v_i_boxed_293_, v_b_291_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop(lean_object* v_00_u03b2_295_, lean_object* v_m_296_, lean_object* v_inst_297_, lean_object* v_as_298_, lean_object* v_f_299_, size_t v_sz_300_, size_t v_i_301_, lean_object* v_b_302_){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg(v_inst_297_, v_as_298_, v_f_299_, v_sz_300_, v_i_301_, v_b_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___boxed(lean_object* v_00_u03b2_304_, lean_object* v_m_305_, lean_object* v_inst_306_, lean_object* v_as_307_, lean_object* v_f_308_, lean_object* v_sz_309_, lean_object* v_i_310_, lean_object* v_b_311_){
_start:
{
size_t v_sz_boxed_312_; size_t v_i_boxed_313_; lean_object* v_res_314_; 
v_sz_boxed_312_ = lean_unbox_usize(v_sz_309_);
lean_dec(v_sz_309_);
v_i_boxed_313_ = lean_unbox_usize(v_i_310_);
lean_dec(v_i_310_);
v_res_314_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop(v_00_u03b2_304_, v_m_305_, v_inst_306_, v_as_307_, v_f_308_, v_sz_boxed_312_, v_i_boxed_313_, v_b_311_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_forInUnsafe___redArg(lean_object* v_inst_315_, lean_object* v_as_316_, lean_object* v_b_317_, lean_object* v_f_318_){
_start:
{
size_t v_sz_319_; size_t v___x_320_; lean_object* v___x_321_; 
v_sz_319_ = lean_sarray_size(v_as_316_);
v___x_320_ = ((size_t)0ULL);
v___x_321_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg(v_inst_315_, v_as_316_, v_f_318_, v_sz_319_, v___x_320_, v_b_317_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_forInUnsafe(lean_object* v_00_u03b2_322_, lean_object* v_m_323_, lean_object* v_inst_324_, lean_object* v_as_325_, lean_object* v_b_326_, lean_object* v_f_327_){
_start:
{
size_t v_sz_328_; size_t v___x_329_; lean_object* v___x_330_; 
v_sz_328_ = lean_sarray_size(v_as_325_);
v___x_329_ = ((size_t)0ULL);
v___x_330_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg(v_inst_324_, v_as_325_, v_f_327_, v_sz_328_, v___x_329_, v_b_326_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop___redArg___lam__0___boxed(lean_object* v_toPure_331_, lean_object* v_inst_332_, lean_object* v_as_333_, lean_object* v_f_334_, lean_object* v_n_335_, lean_object* v_____do__lift_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop___redArg___lam__0(v_toPure_331_, v_inst_332_, v_as_333_, v_f_334_, v_n_335_, v_____do__lift_336_);
lean_dec(v_n_335_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop___redArg(lean_object* v_inst_338_, lean_object* v_as_339_, lean_object* v_f_340_, lean_object* v_i_341_, lean_object* v_b_342_){
_start:
{
lean_object* v_toApplicative_343_; lean_object* v_toBind_344_; lean_object* v_toPure_345_; lean_object* v_zero_346_; uint8_t v_isZero_347_; 
v_toApplicative_343_ = lean_ctor_get(v_inst_338_, 0);
v_toBind_344_ = lean_ctor_get(v_inst_338_, 1);
lean_inc(v_toBind_344_);
v_toPure_345_ = lean_ctor_get(v_toApplicative_343_, 1);
lean_inc(v_toPure_345_);
v_zero_346_ = lean_unsigned_to_nat(0u);
v_isZero_347_ = lean_nat_dec_eq(v_i_341_, v_zero_346_);
if (v_isZero_347_ == 1)
{
lean_object* v___x_348_; 
lean_dec(v_toBind_344_);
lean_dec(v_f_340_);
lean_dec_ref(v_as_339_);
lean_dec_ref(v_inst_338_);
v___x_348_ = lean_apply_2(v_toPure_345_, lean_box(0), v_b_342_);
return v___x_348_;
}
else
{
lean_object* v_one_349_; lean_object* v_n_350_; lean_object* v___f_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; double v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v_one_349_ = lean_unsigned_to_nat(1u);
v_n_350_ = lean_nat_sub(v_i_341_, v_one_349_);
lean_inc(v_n_350_);
lean_inc(v_f_340_);
lean_inc_ref(v_as_339_);
v___f_351_ = lean_alloc_closure((void*)(l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_351_, 0, v_toPure_345_);
lean_closure_set(v___f_351_, 1, v_inst_338_);
lean_closure_set(v___f_351_, 2, v_as_339_);
lean_closure_set(v___f_351_, 3, v_f_340_);
lean_closure_set(v___f_351_, 4, v_n_350_);
v___x_352_ = lean_float_array_size(v_as_339_);
v___x_353_ = lean_nat_sub(v___x_352_, v_one_349_);
v___x_354_ = lean_nat_sub(v___x_353_, v_n_350_);
lean_dec(v_n_350_);
lean_dec(v___x_353_);
v___x_355_ = lean_float_array_fget(v_as_339_, v___x_354_);
lean_dec(v___x_354_);
lean_dec_ref(v_as_339_);
v___x_356_ = lean_box_float(v___x_355_);
v___x_357_ = lean_apply_2(v_f_340_, v___x_356_, v_b_342_);
v___x_358_ = lean_apply_4(v_toBind_344_, lean_box(0), lean_box(0), v___x_357_, v___f_351_);
return v___x_358_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop___redArg___lam__0(lean_object* v_toPure_359_, lean_object* v_inst_360_, lean_object* v_as_361_, lean_object* v_f_362_, lean_object* v_n_363_, lean_object* v_____do__lift_364_){
_start:
{
if (lean_obj_tag(v_____do__lift_364_) == 0)
{
lean_object* v_a_365_; lean_object* v___x_366_; 
lean_dec(v_f_362_);
lean_dec_ref(v_as_361_);
lean_dec_ref(v_inst_360_);
v_a_365_ = lean_ctor_get(v_____do__lift_364_, 0);
lean_inc(v_a_365_);
lean_dec_ref_known(v_____do__lift_364_, 1);
v___x_366_ = lean_apply_2(v_toPure_359_, lean_box(0), v_a_365_);
return v___x_366_;
}
else
{
lean_object* v_a_367_; lean_object* v___x_368_; 
lean_dec(v_toPure_359_);
v_a_367_ = lean_ctor_get(v_____do__lift_364_, 0);
lean_inc(v_a_367_);
lean_dec_ref_known(v_____do__lift_364_, 1);
v___x_368_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop___redArg(v_inst_360_, v_as_361_, v_f_362_, v_n_363_, v_a_367_);
return v___x_368_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop___redArg___boxed(lean_object* v_inst_369_, lean_object* v_as_370_, lean_object* v_f_371_, lean_object* v_i_372_, lean_object* v_b_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop___redArg(v_inst_369_, v_as_370_, v_f_371_, v_i_372_, v_b_373_);
lean_dec(v_i_372_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop(lean_object* v_00_u03b2_375_, lean_object* v_m_376_, lean_object* v_inst_377_, lean_object* v_as_378_, lean_object* v_f_379_, lean_object* v_i_380_, lean_object* v_h_381_, lean_object* v_b_382_){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop___redArg(v_inst_377_, v_as_378_, v_f_379_, v_i_380_, v_b_382_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop___boxed(lean_object* v_00_u03b2_384_, lean_object* v_m_385_, lean_object* v_inst_386_, lean_object* v_as_387_, lean_object* v_f_388_, lean_object* v_i_389_, lean_object* v_h_390_, lean_object* v_b_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop(v_00_u03b2_384_, v_m_385_, v_inst_386_, v_as_387_, v_f_388_, v_i_389_, v_h_390_, v_b_391_);
lean_dec(v_i_389_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_instForInFloatOfMonad___redArg___lam__0(lean_object* v_inst_393_, lean_object* v_00_u03b2_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
size_t v_sz_398_; size_t v___x_399_; lean_object* v___x_400_; 
v_sz_398_ = lean_sarray_size(v___y_395_);
v___x_399_ = ((size_t)0ULL);
v___x_400_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg(v_inst_393_, v___y_395_, v___y_397_, v_sz_398_, v___x_399_, v___y_396_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_instForInFloatOfMonad___redArg(lean_object* v_inst_401_){
_start:
{
lean_object* v___f_402_; 
v___f_402_ = lean_alloc_closure((void*)(l_FloatArray_instForInFloatOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_402_, 0, v_inst_401_);
return v___f_402_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_instForInFloatOfMonad(lean_object* v_m_403_, lean_object* v_inst_404_){
_start:
{
lean_object* v___f_405_; 
v___f_405_ = lean_alloc_closure((void*)(l_FloatArray_instForInFloatOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_405_, 0, v_inst_404_);
return v___f_405_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg___lam__0___boxed(lean_object* v_i_406_, lean_object* v_inst_407_, lean_object* v_f_408_, lean_object* v_as_409_, lean_object* v_stop_410_, lean_object* v_____do__lift_411_){
_start:
{
size_t v_i_boxed_412_; size_t v_stop_boxed_413_; lean_object* v_res_414_; 
v_i_boxed_412_ = lean_unbox_usize(v_i_406_);
lean_dec(v_i_406_);
v_stop_boxed_413_ = lean_unbox_usize(v_stop_410_);
lean_dec(v_stop_410_);
v_res_414_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg___lam__0(v_i_boxed_412_, v_inst_407_, v_f_408_, v_as_409_, v_stop_boxed_413_, v_____do__lift_411_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(lean_object* v_inst_415_, lean_object* v_f_416_, lean_object* v_as_417_, size_t v_i_418_, size_t v_stop_419_, lean_object* v_b_420_){
_start:
{
lean_object* v_toApplicative_421_; lean_object* v_toBind_422_; lean_object* v_toPure_423_; uint8_t v___x_424_; 
v_toApplicative_421_ = lean_ctor_get(v_inst_415_, 0);
v_toBind_422_ = lean_ctor_get(v_inst_415_, 1);
lean_inc(v_toBind_422_);
v_toPure_423_ = lean_ctor_get(v_toApplicative_421_, 1);
v___x_424_ = lean_usize_dec_eq(v_i_418_, v_stop_419_);
if (v___x_424_ == 0)
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___f_427_; double v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_425_ = lean_box_usize(v_i_418_);
v___x_426_ = lean_box_usize(v_stop_419_);
lean_inc_ref(v_as_417_);
lean_inc(v_f_416_);
v___f_427_ = lean_alloc_closure((void*)(l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_427_, 0, v___x_425_);
lean_closure_set(v___f_427_, 1, v_inst_415_);
lean_closure_set(v___f_427_, 2, v_f_416_);
lean_closure_set(v___f_427_, 3, v_as_417_);
lean_closure_set(v___f_427_, 4, v___x_426_);
v___x_428_ = lean_float_array_uget(v_as_417_, v_i_418_);
lean_dec_ref(v_as_417_);
v___x_429_ = lean_box_float(v___x_428_);
v___x_430_ = lean_apply_2(v_f_416_, v_b_420_, v___x_429_);
v___x_431_ = lean_apply_4(v_toBind_422_, lean_box(0), lean_box(0), v___x_430_, v___f_427_);
return v___x_431_;
}
else
{
lean_object* v___x_432_; 
lean_inc(v_toPure_423_);
lean_dec(v_toBind_422_);
lean_dec_ref(v_as_417_);
lean_dec(v_f_416_);
lean_dec_ref(v_inst_415_);
v___x_432_ = lean_apply_2(v_toPure_423_, lean_box(0), v_b_420_);
return v___x_432_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg___lam__0(size_t v_i_433_, lean_object* v_inst_434_, lean_object* v_f_435_, lean_object* v_as_436_, size_t v_stop_437_, lean_object* v_____do__lift_438_){
_start:
{
size_t v___x_439_; size_t v___x_440_; lean_object* v___x_441_; 
v___x_439_ = ((size_t)1ULL);
v___x_440_ = lean_usize_add(v_i_433_, v___x_439_);
v___x_441_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(v_inst_434_, v_f_435_, v_as_436_, v___x_440_, v_stop_437_, v_____do__lift_438_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg___boxed(lean_object* v_inst_442_, lean_object* v_f_443_, lean_object* v_as_444_, lean_object* v_i_445_, lean_object* v_stop_446_, lean_object* v_b_447_){
_start:
{
size_t v_i_boxed_448_; size_t v_stop_boxed_449_; lean_object* v_res_450_; 
v_i_boxed_448_ = lean_unbox_usize(v_i_445_);
lean_dec(v_i_445_);
v_stop_boxed_449_ = lean_unbox_usize(v_stop_446_);
lean_dec(v_stop_446_);
v_res_450_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(v_inst_442_, v_f_443_, v_as_444_, v_i_boxed_448_, v_stop_boxed_449_, v_b_447_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold(lean_object* v_00_u03b2_451_, lean_object* v_m_452_, lean_object* v_inst_453_, lean_object* v_f_454_, lean_object* v_as_455_, size_t v_i_456_, size_t v_stop_457_, lean_object* v_b_458_){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(v_inst_453_, v_f_454_, v_as_455_, v_i_456_, v_stop_457_, v_b_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___boxed(lean_object* v_00_u03b2_460_, lean_object* v_m_461_, lean_object* v_inst_462_, lean_object* v_f_463_, lean_object* v_as_464_, lean_object* v_i_465_, lean_object* v_stop_466_, lean_object* v_b_467_){
_start:
{
size_t v_i_boxed_468_; size_t v_stop_boxed_469_; lean_object* v_res_470_; 
v_i_boxed_468_ = lean_unbox_usize(v_i_465_);
lean_dec(v_i_465_);
v_stop_boxed_469_ = lean_unbox_usize(v_stop_466_);
lean_dec(v_stop_466_);
v_res_470_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold(v_00_u03b2_460_, v_m_461_, v_inst_462_, v_f_463_, v_as_464_, v_i_boxed_468_, v_stop_boxed_469_, v_b_467_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_foldlMUnsafe___redArg(lean_object* v_inst_471_, lean_object* v_f_472_, lean_object* v_init_473_, lean_object* v_as_474_, lean_object* v_start_475_, lean_object* v_stop_476_){
_start:
{
lean_object* v_toApplicative_477_; lean_object* v_toPure_478_; uint8_t v___x_479_; 
v_toApplicative_477_ = lean_ctor_get(v_inst_471_, 0);
v_toPure_478_ = lean_ctor_get(v_toApplicative_477_, 1);
v___x_479_ = lean_nat_dec_lt(v_start_475_, v_stop_476_);
if (v___x_479_ == 0)
{
lean_object* v___x_480_; 
lean_inc(v_toPure_478_);
lean_dec_ref(v_as_474_);
lean_dec(v_f_472_);
lean_dec_ref(v_inst_471_);
v___x_480_ = lean_apply_2(v_toPure_478_, lean_box(0), v_init_473_);
return v___x_480_;
}
else
{
lean_object* v___x_481_; uint8_t v___x_482_; 
v___x_481_ = lean_float_array_size(v_as_474_);
v___x_482_ = lean_nat_dec_le(v_stop_476_, v___x_481_);
if (v___x_482_ == 0)
{
uint8_t v___x_483_; 
v___x_483_ = lean_nat_dec_lt(v_start_475_, v___x_481_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; 
lean_inc(v_toPure_478_);
lean_dec_ref(v_as_474_);
lean_dec(v_f_472_);
lean_dec_ref(v_inst_471_);
v___x_484_ = lean_apply_2(v_toPure_478_, lean_box(0), v_init_473_);
return v___x_484_;
}
else
{
size_t v___x_485_; size_t v___x_486_; lean_object* v___x_487_; 
v___x_485_ = lean_usize_of_nat(v_start_475_);
v___x_486_ = lean_usize_of_nat(v___x_481_);
v___x_487_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(v_inst_471_, v_f_472_, v_as_474_, v___x_485_, v___x_486_, v_init_473_);
return v___x_487_;
}
}
else
{
size_t v___x_488_; size_t v___x_489_; lean_object* v___x_490_; 
v___x_488_ = lean_usize_of_nat(v_start_475_);
v___x_489_ = lean_usize_of_nat(v_stop_476_);
v___x_490_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(v_inst_471_, v_f_472_, v_as_474_, v___x_488_, v___x_489_, v_init_473_);
return v___x_490_;
}
}
}
}
LEAN_EXPORT lean_object* l_FloatArray_foldlMUnsafe___redArg___boxed(lean_object* v_inst_491_, lean_object* v_f_492_, lean_object* v_init_493_, lean_object* v_as_494_, lean_object* v_start_495_, lean_object* v_stop_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_FloatArray_foldlMUnsafe___redArg(v_inst_491_, v_f_492_, v_init_493_, v_as_494_, v_start_495_, v_stop_496_);
lean_dec(v_stop_496_);
lean_dec(v_start_495_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_foldlMUnsafe(lean_object* v_00_u03b2_498_, lean_object* v_m_499_, lean_object* v_inst_500_, lean_object* v_f_501_, lean_object* v_init_502_, lean_object* v_as_503_, lean_object* v_start_504_, lean_object* v_stop_505_){
_start:
{
lean_object* v_toApplicative_506_; lean_object* v_toPure_507_; uint8_t v___x_508_; 
v_toApplicative_506_ = lean_ctor_get(v_inst_500_, 0);
v_toPure_507_ = lean_ctor_get(v_toApplicative_506_, 1);
v___x_508_ = lean_nat_dec_lt(v_start_504_, v_stop_505_);
if (v___x_508_ == 0)
{
lean_object* v___x_509_; 
lean_inc(v_toPure_507_);
lean_dec_ref(v_as_503_);
lean_dec(v_f_501_);
lean_dec_ref(v_inst_500_);
v___x_509_ = lean_apply_2(v_toPure_507_, lean_box(0), v_init_502_);
return v___x_509_;
}
else
{
lean_object* v___x_510_; uint8_t v___x_511_; 
v___x_510_ = lean_float_array_size(v_as_503_);
v___x_511_ = lean_nat_dec_le(v_stop_505_, v___x_510_);
if (v___x_511_ == 0)
{
uint8_t v___x_512_; 
v___x_512_ = lean_nat_dec_lt(v_start_504_, v___x_510_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; 
lean_inc(v_toPure_507_);
lean_dec_ref(v_as_503_);
lean_dec(v_f_501_);
lean_dec_ref(v_inst_500_);
v___x_513_ = lean_apply_2(v_toPure_507_, lean_box(0), v_init_502_);
return v___x_513_;
}
else
{
size_t v___x_514_; size_t v___x_515_; lean_object* v___x_516_; 
v___x_514_ = lean_usize_of_nat(v_start_504_);
v___x_515_ = lean_usize_of_nat(v___x_510_);
v___x_516_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(v_inst_500_, v_f_501_, v_as_503_, v___x_514_, v___x_515_, v_init_502_);
return v___x_516_;
}
}
else
{
size_t v___x_517_; size_t v___x_518_; lean_object* v___x_519_; 
v___x_517_ = lean_usize_of_nat(v_start_504_);
v___x_518_ = lean_usize_of_nat(v_stop_505_);
v___x_519_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(v_inst_500_, v_f_501_, v_as_503_, v___x_517_, v___x_518_, v_init_502_);
return v___x_519_;
}
}
}
}
LEAN_EXPORT lean_object* l_FloatArray_foldlMUnsafe___boxed(lean_object* v_00_u03b2_520_, lean_object* v_m_521_, lean_object* v_inst_522_, lean_object* v_f_523_, lean_object* v_init_524_, lean_object* v_as_525_, lean_object* v_start_526_, lean_object* v_stop_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_FloatArray_foldlMUnsafe(v_00_u03b2_520_, v_m_521_, v_inst_522_, v_f_523_, v_init_524_, v_as_525_, v_start_526_, v_stop_527_);
lean_dec(v_stop_527_);
lean_dec(v_start_526_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop___redArg___lam__0___boxed(lean_object* v_j_529_, lean_object* v_inst_530_, lean_object* v_f_531_, lean_object* v_as_532_, lean_object* v_stop_533_, lean_object* v_n_534_, lean_object* v_____do__lift_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop___redArg___lam__0(v_j_529_, v_inst_530_, v_f_531_, v_as_532_, v_stop_533_, v_n_534_, v_____do__lift_535_);
lean_dec(v_n_534_);
lean_dec(v_j_529_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop___redArg(lean_object* v_inst_537_, lean_object* v_f_538_, lean_object* v_as_539_, lean_object* v_stop_540_, lean_object* v_i_541_, lean_object* v_j_542_, lean_object* v_b_543_){
_start:
{
lean_object* v_toApplicative_544_; lean_object* v_toBind_545_; lean_object* v_toPure_546_; uint8_t v___x_547_; 
v_toApplicative_544_ = lean_ctor_get(v_inst_537_, 0);
v_toBind_545_ = lean_ctor_get(v_inst_537_, 1);
lean_inc(v_toBind_545_);
v_toPure_546_ = lean_ctor_get(v_toApplicative_544_, 1);
v___x_547_ = lean_nat_dec_lt(v_j_542_, v_stop_540_);
if (v___x_547_ == 0)
{
lean_object* v___x_548_; 
lean_inc(v_toPure_546_);
lean_dec(v_toBind_545_);
lean_dec(v_j_542_);
lean_dec(v_stop_540_);
lean_dec_ref(v_as_539_);
lean_dec(v_f_538_);
lean_dec_ref(v_inst_537_);
v___x_548_ = lean_apply_2(v_toPure_546_, lean_box(0), v_b_543_);
return v___x_548_;
}
else
{
lean_object* v_zero_549_; uint8_t v_isZero_550_; 
v_zero_549_ = lean_unsigned_to_nat(0u);
v_isZero_550_ = lean_nat_dec_eq(v_i_541_, v_zero_549_);
if (v_isZero_550_ == 1)
{
lean_object* v___x_551_; 
lean_inc(v_toPure_546_);
lean_dec(v_toBind_545_);
lean_dec(v_j_542_);
lean_dec(v_stop_540_);
lean_dec_ref(v_as_539_);
lean_dec(v_f_538_);
lean_dec_ref(v_inst_537_);
v___x_551_ = lean_apply_2(v_toPure_546_, lean_box(0), v_b_543_);
return v___x_551_;
}
else
{
lean_object* v_one_552_; lean_object* v_n_553_; lean_object* v___f_554_; double v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v_one_552_ = lean_unsigned_to_nat(1u);
v_n_553_ = lean_nat_sub(v_i_541_, v_one_552_);
lean_inc_ref(v_as_539_);
lean_inc(v_f_538_);
lean_inc(v_j_542_);
v___f_554_ = lean_alloc_closure((void*)(l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_554_, 0, v_j_542_);
lean_closure_set(v___f_554_, 1, v_inst_537_);
lean_closure_set(v___f_554_, 2, v_f_538_);
lean_closure_set(v___f_554_, 3, v_as_539_);
lean_closure_set(v___f_554_, 4, v_stop_540_);
lean_closure_set(v___f_554_, 5, v_n_553_);
v___x_555_ = lean_float_array_fget(v_as_539_, v_j_542_);
lean_dec(v_j_542_);
lean_dec_ref(v_as_539_);
v___x_556_ = lean_box_float(v___x_555_);
v___x_557_ = lean_apply_2(v_f_538_, v_b_543_, v___x_556_);
v___x_558_ = lean_apply_4(v_toBind_545_, lean_box(0), lean_box(0), v___x_557_, v___f_554_);
return v___x_558_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop___redArg___lam__0(lean_object* v_j_559_, lean_object* v_inst_560_, lean_object* v_f_561_, lean_object* v_as_562_, lean_object* v_stop_563_, lean_object* v_n_564_, lean_object* v_____do__lift_565_){
_start:
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_566_ = lean_unsigned_to_nat(1u);
v___x_567_ = lean_nat_add(v_j_559_, v___x_566_);
v___x_568_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop___redArg(v_inst_560_, v_f_561_, v_as_562_, v_stop_563_, v_n_564_, v___x_567_, v_____do__lift_565_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop___redArg___boxed(lean_object* v_inst_569_, lean_object* v_f_570_, lean_object* v_as_571_, lean_object* v_stop_572_, lean_object* v_i_573_, lean_object* v_j_574_, lean_object* v_b_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop___redArg(v_inst_569_, v_f_570_, v_as_571_, v_stop_572_, v_i_573_, v_j_574_, v_b_575_);
lean_dec(v_i_573_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop(lean_object* v_00_u03b2_577_, lean_object* v_m_578_, lean_object* v_inst_579_, lean_object* v_f_580_, lean_object* v_as_581_, lean_object* v_stop_582_, lean_object* v_h_583_, lean_object* v_i_584_, lean_object* v_j_585_, lean_object* v_b_586_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop___redArg(v_inst_579_, v_f_580_, v_as_581_, v_stop_582_, v_i_584_, v_j_585_, v_b_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop___boxed(lean_object* v_00_u03b2_588_, lean_object* v_m_589_, lean_object* v_inst_590_, lean_object* v_f_591_, lean_object* v_as_592_, lean_object* v_stop_593_, lean_object* v_h_594_, lean_object* v_i_595_, lean_object* v_j_596_, lean_object* v_b_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop(v_00_u03b2_588_, v_m_589_, v_inst_590_, v_f_591_, v_as_592_, v_stop_593_, v_h_594_, v_i_595_, v_j_596_, v_b_597_);
lean_dec(v_i_595_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_foldl___redArg___lam__0(lean_object* v_f_599_, lean_object* v_x1_600_, double v_x2_601_){
_start:
{
lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_602_ = lean_box_float(v_x2_601_);
v___x_603_ = lean_apply_2(v_f_599_, v_x1_600_, v___x_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_foldl___redArg___lam__0___boxed(lean_object* v_f_604_, lean_object* v_x1_605_, lean_object* v_x2_606_){
_start:
{
double v_x2_185__boxed_607_; lean_object* v_res_608_; 
v_x2_185__boxed_607_ = lean_unbox_float(v_x2_606_);
lean_dec_ref(v_x2_606_);
v_res_608_ = l_FloatArray_foldl___redArg___lam__0(v_f_604_, v_x1_605_, v_x2_185__boxed_607_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_foldl___redArg(lean_object* v_f_628_, lean_object* v_init_629_, lean_object* v_as_630_, lean_object* v_start_631_, lean_object* v_stop_632_){
_start:
{
lean_object* v___x_633_; uint8_t v___x_634_; 
v___x_633_ = ((lean_object*)(l_FloatArray_foldl___redArg___closed__9));
v___x_634_ = lean_nat_dec_lt(v_start_631_, v_stop_632_);
if (v___x_634_ == 0)
{
lean_dec_ref(v_as_630_);
lean_dec(v_f_628_);
return v_init_629_;
}
else
{
lean_object* v___f_635_; lean_object* v___x_636_; uint8_t v___x_637_; 
v___f_635_ = lean_alloc_closure((void*)(l_FloatArray_foldl___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_635_, 0, v_f_628_);
v___x_636_ = lean_float_array_size(v_as_630_);
v___x_637_ = lean_nat_dec_le(v_stop_632_, v___x_636_);
if (v___x_637_ == 0)
{
uint8_t v___x_638_; 
v___x_638_ = lean_nat_dec_lt(v_start_631_, v___x_636_);
if (v___x_638_ == 0)
{
lean_dec_ref(v___f_635_);
lean_dec_ref(v_as_630_);
return v_init_629_;
}
else
{
size_t v___x_639_; size_t v___x_640_; lean_object* v___x_641_; 
v___x_639_ = lean_usize_of_nat(v_start_631_);
v___x_640_ = lean_usize_of_nat(v___x_636_);
v___x_641_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(v___x_633_, v___f_635_, v_as_630_, v___x_639_, v___x_640_, v_init_629_);
return v___x_641_;
}
}
else
{
size_t v___x_642_; size_t v___x_643_; lean_object* v___x_644_; 
v___x_642_ = lean_usize_of_nat(v_start_631_);
v___x_643_ = lean_usize_of_nat(v_stop_632_);
v___x_644_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(v___x_633_, v___f_635_, v_as_630_, v___x_642_, v___x_643_, v_init_629_);
return v___x_644_;
}
}
}
}
LEAN_EXPORT lean_object* l_FloatArray_foldl___redArg___boxed(lean_object* v_f_645_, lean_object* v_init_646_, lean_object* v_as_647_, lean_object* v_start_648_, lean_object* v_stop_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l_FloatArray_foldl___redArg(v_f_645_, v_init_646_, v_as_647_, v_start_648_, v_stop_649_);
lean_dec(v_stop_649_);
lean_dec(v_start_648_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_foldl(lean_object* v_00_u03b2_651_, lean_object* v_f_652_, lean_object* v_init_653_, lean_object* v_as_654_, lean_object* v_start_655_, lean_object* v_stop_656_){
_start:
{
lean_object* v___x_657_; uint8_t v___x_658_; 
v___x_657_ = ((lean_object*)(l_FloatArray_foldl___redArg___closed__9));
v___x_658_ = lean_nat_dec_lt(v_start_655_, v_stop_656_);
if (v___x_658_ == 0)
{
lean_dec_ref(v_as_654_);
lean_dec(v_f_652_);
return v_init_653_;
}
else
{
lean_object* v___f_659_; lean_object* v___x_660_; uint8_t v___x_661_; 
v___f_659_ = lean_alloc_closure((void*)(l_FloatArray_foldl___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_659_, 0, v_f_652_);
v___x_660_ = lean_float_array_size(v_as_654_);
v___x_661_ = lean_nat_dec_le(v_stop_656_, v___x_660_);
if (v___x_661_ == 0)
{
uint8_t v___x_662_; 
v___x_662_ = lean_nat_dec_lt(v_start_655_, v___x_660_);
if (v___x_662_ == 0)
{
lean_dec_ref(v___f_659_);
lean_dec_ref(v_as_654_);
return v_init_653_;
}
else
{
size_t v___x_663_; size_t v___x_664_; lean_object* v___x_665_; 
v___x_663_ = lean_usize_of_nat(v_start_655_);
v___x_664_ = lean_usize_of_nat(v___x_660_);
v___x_665_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(v___x_657_, v___f_659_, v_as_654_, v___x_663_, v___x_664_, v_init_653_);
return v___x_665_;
}
}
else
{
size_t v___x_666_; size_t v___x_667_; lean_object* v___x_668_; 
v___x_666_ = lean_usize_of_nat(v_start_655_);
v___x_667_ = lean_usize_of_nat(v_stop_656_);
v___x_668_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(v___x_657_, v___f_659_, v_as_654_, v___x_666_, v___x_667_, v_init_653_);
return v___x_668_;
}
}
}
}
LEAN_EXPORT lean_object* l_FloatArray_foldl___boxed(lean_object* v_00_u03b2_669_, lean_object* v_f_670_, lean_object* v_init_671_, lean_object* v_as_672_, lean_object* v_start_673_, lean_object* v_stop_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_FloatArray_foldl(v_00_u03b2_669_, v_f_670_, v_init_671_, v_as_672_, v_start_673_, v_stop_674_);
lean_dec(v_stop_674_);
lean_dec(v_start_673_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__List_toFloatArray_loop(lean_object* v_x_676_, lean_object* v_x_677_){
_start:
{
if (lean_obj_tag(v_x_676_) == 0)
{
return v_x_677_;
}
else
{
lean_object* v_head_678_; lean_object* v_tail_679_; double v___x_680_; lean_object* v___x_681_; 
v_head_678_ = lean_ctor_get(v_x_676_, 0);
v_tail_679_ = lean_ctor_get(v_x_676_, 1);
v___x_680_ = lean_unbox_float(v_head_678_);
v___x_681_ = lean_float_array_push(v_x_677_, v___x_680_);
v_x_676_ = v_tail_679_;
v_x_677_ = v___x_681_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__List_toFloatArray_loop___boxed(lean_object* v_x_683_, lean_object* v_x_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l___private_Init_Data_FloatArray_Basic_0__List_toFloatArray_loop(v_x_683_, v_x_684_);
lean_dec(v_x_683_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_List_toFloatArray(lean_object* v_ds_686_){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = l_FloatArray_empty;
v___x_688_ = l___private_Init_Data_FloatArray_Basic_0__List_toFloatArray_loop(v_ds_686_, v___x_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_List_toFloatArray___boxed(lean_object* v_ds_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_List_toFloatArray(v_ds_689_);
lean_dec(v_ds_689_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_instToStringFloatArray___lam__0(lean_object* v___x_691_, lean_object* v_ds_692_){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = l_FloatArray_toList(v_ds_692_);
v___x_694_ = l_List_toString___redArg(v___x_691_, v___x_693_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_instToStringFloatArray___lam__0___boxed(lean_object* v___x_695_, lean_object* v_ds_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_instToStringFloatArray___lam__0(v___x_695_, v_ds_696_);
lean_dec_ref(v_ds_696_);
return v_res_697_;
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
