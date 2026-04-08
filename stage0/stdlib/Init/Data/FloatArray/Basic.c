// Lean compiler output
// Module: Init.Data.FloatArray.Basic
// Imports: public import Init.Data.Float import Init.Ext public import Init.GetElem public import Init.Data.ToString.Extra
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
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg___lam__0___boxed(lean_object* v_toApplicative_245_, lean_object* v_i_246_, lean_object* v_inst_247_, lean_object* v_as_248_, lean_object* v_f_249_, lean_object* v_sz_250_, lean_object* v_____do__lift_251_){
_start:
{
size_t v_i_boxed_252_; size_t v_sz_boxed_253_; lean_object* v_res_254_; 
v_i_boxed_252_ = lean_unbox_usize(v_i_246_);
lean_dec(v_i_246_);
v_sz_boxed_253_ = lean_unbox_usize(v_sz_250_);
lean_dec(v_sz_250_);
v_res_254_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg___lam__0(v_toApplicative_245_, v_i_boxed_252_, v_inst_247_, v_as_248_, v_f_249_, v_sz_boxed_253_, v_____do__lift_251_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg(lean_object* v_inst_255_, lean_object* v_as_256_, lean_object* v_f_257_, size_t v_sz_258_, size_t v_i_259_, lean_object* v_b_260_){
_start:
{
uint8_t v___x_261_; 
v___x_261_ = lean_usize_dec_lt(v_i_259_, v_sz_258_);
if (v___x_261_ == 0)
{
lean_object* v_toApplicative_262_; lean_object* v_toPure_263_; lean_object* v___x_264_; 
lean_dec(v_f_257_);
lean_dec_ref(v_as_256_);
v_toApplicative_262_ = lean_ctor_get(v_inst_255_, 0);
lean_inc_ref(v_toApplicative_262_);
lean_dec_ref(v_inst_255_);
v_toPure_263_ = lean_ctor_get(v_toApplicative_262_, 1);
lean_inc(v_toPure_263_);
lean_dec_ref(v_toApplicative_262_);
v___x_264_ = lean_apply_2(v_toPure_263_, lean_box(0), v_b_260_);
return v___x_264_;
}
else
{
lean_object* v_toApplicative_265_; lean_object* v_toBind_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___f_269_; double v_a_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v_toApplicative_265_ = lean_ctor_get(v_inst_255_, 0);
lean_inc_ref(v_toApplicative_265_);
v_toBind_266_ = lean_ctor_get(v_inst_255_, 1);
lean_inc(v_toBind_266_);
v___x_267_ = lean_box_usize(v_i_259_);
v___x_268_ = lean_box_usize(v_sz_258_);
lean_inc(v_f_257_);
lean_inc_ref(v_as_256_);
v___f_269_ = lean_alloc_closure((void*)(l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_269_, 0, v_toApplicative_265_);
lean_closure_set(v___f_269_, 1, v___x_267_);
lean_closure_set(v___f_269_, 2, v_inst_255_);
lean_closure_set(v___f_269_, 3, v_as_256_);
lean_closure_set(v___f_269_, 4, v_f_257_);
lean_closure_set(v___f_269_, 5, v___x_268_);
v_a_270_ = lean_float_array_uget(v_as_256_, v_i_259_);
lean_dec_ref(v_as_256_);
v___x_271_ = lean_box_float(v_a_270_);
v___x_272_ = lean_apply_2(v_f_257_, v___x_271_, v_b_260_);
v___x_273_ = lean_apply_4(v_toBind_266_, lean_box(0), lean_box(0), v___x_272_, v___f_269_);
return v___x_273_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg___lam__0(lean_object* v_toApplicative_274_, size_t v_i_275_, lean_object* v_inst_276_, lean_object* v_as_277_, lean_object* v_f_278_, size_t v_sz_279_, lean_object* v_____do__lift_280_){
_start:
{
if (lean_obj_tag(v_____do__lift_280_) == 0)
{
lean_object* v_a_281_; lean_object* v_toPure_282_; lean_object* v___x_283_; 
lean_dec(v_f_278_);
lean_dec_ref(v_as_277_);
lean_dec_ref(v_inst_276_);
v_a_281_ = lean_ctor_get(v_____do__lift_280_, 0);
lean_inc(v_a_281_);
lean_dec_ref(v_____do__lift_280_);
v_toPure_282_ = lean_ctor_get(v_toApplicative_274_, 1);
lean_inc(v_toPure_282_);
lean_dec_ref(v_toApplicative_274_);
v___x_283_ = lean_apply_2(v_toPure_282_, lean_box(0), v_a_281_);
return v___x_283_;
}
else
{
lean_object* v_a_284_; size_t v___x_285_; size_t v___x_286_; lean_object* v___x_287_; 
lean_dec_ref(v_toApplicative_274_);
v_a_284_ = lean_ctor_get(v_____do__lift_280_, 0);
lean_inc(v_a_284_);
lean_dec_ref(v_____do__lift_280_);
v___x_285_ = ((size_t)1ULL);
v___x_286_ = lean_usize_add(v_i_275_, v___x_285_);
v___x_287_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg(v_inst_276_, v_as_277_, v_f_278_, v_sz_279_, v___x_286_, v_a_284_);
return v___x_287_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg___boxed(lean_object* v_inst_288_, lean_object* v_as_289_, lean_object* v_f_290_, lean_object* v_sz_291_, lean_object* v_i_292_, lean_object* v_b_293_){
_start:
{
size_t v_sz_boxed_294_; size_t v_i_boxed_295_; lean_object* v_res_296_; 
v_sz_boxed_294_ = lean_unbox_usize(v_sz_291_);
lean_dec(v_sz_291_);
v_i_boxed_295_ = lean_unbox_usize(v_i_292_);
lean_dec(v_i_292_);
v_res_296_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg(v_inst_288_, v_as_289_, v_f_290_, v_sz_boxed_294_, v_i_boxed_295_, v_b_293_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop(lean_object* v_00_u03b2_297_, lean_object* v_m_298_, lean_object* v_inst_299_, lean_object* v_as_300_, lean_object* v_f_301_, size_t v_sz_302_, size_t v_i_303_, lean_object* v_b_304_){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg(v_inst_299_, v_as_300_, v_f_301_, v_sz_302_, v_i_303_, v_b_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___boxed(lean_object* v_00_u03b2_306_, lean_object* v_m_307_, lean_object* v_inst_308_, lean_object* v_as_309_, lean_object* v_f_310_, lean_object* v_sz_311_, lean_object* v_i_312_, lean_object* v_b_313_){
_start:
{
size_t v_sz_boxed_314_; size_t v_i_boxed_315_; lean_object* v_res_316_; 
v_sz_boxed_314_ = lean_unbox_usize(v_sz_311_);
lean_dec(v_sz_311_);
v_i_boxed_315_ = lean_unbox_usize(v_i_312_);
lean_dec(v_i_312_);
v_res_316_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop(v_00_u03b2_306_, v_m_307_, v_inst_308_, v_as_309_, v_f_310_, v_sz_boxed_314_, v_i_boxed_315_, v_b_313_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_forInUnsafe___redArg(lean_object* v_inst_317_, lean_object* v_as_318_, lean_object* v_b_319_, lean_object* v_f_320_){
_start:
{
size_t v_sz_321_; size_t v___x_322_; lean_object* v___x_323_; 
v_sz_321_ = lean_sarray_size(v_as_318_);
v___x_322_ = ((size_t)0ULL);
v___x_323_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg(v_inst_317_, v_as_318_, v_f_320_, v_sz_321_, v___x_322_, v_b_319_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_forInUnsafe(lean_object* v_00_u03b2_324_, lean_object* v_m_325_, lean_object* v_inst_326_, lean_object* v_as_327_, lean_object* v_b_328_, lean_object* v_f_329_){
_start:
{
size_t v_sz_330_; size_t v___x_331_; lean_object* v___x_332_; 
v_sz_330_ = lean_sarray_size(v_as_327_);
v___x_331_ = ((size_t)0ULL);
v___x_332_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg(v_inst_326_, v_as_327_, v_f_329_, v_sz_330_, v___x_331_, v_b_328_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop___redArg___lam__0___boxed(lean_object* v_toPure_333_, lean_object* v_inst_334_, lean_object* v_as_335_, lean_object* v_f_336_, lean_object* v_n_337_, lean_object* v_____do__lift_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop___redArg___lam__0(v_toPure_333_, v_inst_334_, v_as_335_, v_f_336_, v_n_337_, v_____do__lift_338_);
lean_dec(v_n_337_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop___redArg(lean_object* v_inst_340_, lean_object* v_as_341_, lean_object* v_f_342_, lean_object* v_i_343_, lean_object* v_b_344_){
_start:
{
lean_object* v_toApplicative_345_; lean_object* v_toBind_346_; lean_object* v_toPure_347_; lean_object* v_zero_348_; uint8_t v_isZero_349_; 
v_toApplicative_345_ = lean_ctor_get(v_inst_340_, 0);
v_toBind_346_ = lean_ctor_get(v_inst_340_, 1);
lean_inc(v_toBind_346_);
v_toPure_347_ = lean_ctor_get(v_toApplicative_345_, 1);
lean_inc(v_toPure_347_);
v_zero_348_ = lean_unsigned_to_nat(0u);
v_isZero_349_ = lean_nat_dec_eq(v_i_343_, v_zero_348_);
if (v_isZero_349_ == 1)
{
lean_object* v___x_350_; 
lean_dec(v_toBind_346_);
lean_dec(v_f_342_);
lean_dec_ref(v_as_341_);
lean_dec_ref(v_inst_340_);
v___x_350_ = lean_apply_2(v_toPure_347_, lean_box(0), v_b_344_);
return v___x_350_;
}
else
{
lean_object* v_one_351_; lean_object* v_n_352_; lean_object* v___f_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; double v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v_one_351_ = lean_unsigned_to_nat(1u);
v_n_352_ = lean_nat_sub(v_i_343_, v_one_351_);
lean_inc(v_n_352_);
lean_inc(v_f_342_);
lean_inc_ref(v_as_341_);
v___f_353_ = lean_alloc_closure((void*)(l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_353_, 0, v_toPure_347_);
lean_closure_set(v___f_353_, 1, v_inst_340_);
lean_closure_set(v___f_353_, 2, v_as_341_);
lean_closure_set(v___f_353_, 3, v_f_342_);
lean_closure_set(v___f_353_, 4, v_n_352_);
v___x_354_ = lean_float_array_size(v_as_341_);
v___x_355_ = lean_nat_sub(v___x_354_, v_one_351_);
v___x_356_ = lean_nat_sub(v___x_355_, v_n_352_);
lean_dec(v_n_352_);
lean_dec(v___x_355_);
v___x_357_ = lean_float_array_fget(v_as_341_, v___x_356_);
lean_dec(v___x_356_);
lean_dec_ref(v_as_341_);
v___x_358_ = lean_box_float(v___x_357_);
v___x_359_ = lean_apply_2(v_f_342_, v___x_358_, v_b_344_);
v___x_360_ = lean_apply_4(v_toBind_346_, lean_box(0), lean_box(0), v___x_359_, v___f_353_);
return v___x_360_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop___redArg___lam__0(lean_object* v_toPure_361_, lean_object* v_inst_362_, lean_object* v_as_363_, lean_object* v_f_364_, lean_object* v_n_365_, lean_object* v_____do__lift_366_){
_start:
{
if (lean_obj_tag(v_____do__lift_366_) == 0)
{
lean_object* v_a_367_; lean_object* v___x_368_; 
lean_dec(v_f_364_);
lean_dec_ref(v_as_363_);
lean_dec_ref(v_inst_362_);
v_a_367_ = lean_ctor_get(v_____do__lift_366_, 0);
lean_inc(v_a_367_);
lean_dec_ref(v_____do__lift_366_);
v___x_368_ = lean_apply_2(v_toPure_361_, lean_box(0), v_a_367_);
return v___x_368_;
}
else
{
lean_object* v_a_369_; lean_object* v___x_370_; 
lean_dec(v_toPure_361_);
v_a_369_ = lean_ctor_get(v_____do__lift_366_, 0);
lean_inc(v_a_369_);
lean_dec_ref(v_____do__lift_366_);
v___x_370_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop___redArg(v_inst_362_, v_as_363_, v_f_364_, v_n_365_, v_a_369_);
return v___x_370_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop___redArg___boxed(lean_object* v_inst_371_, lean_object* v_as_372_, lean_object* v_f_373_, lean_object* v_i_374_, lean_object* v_b_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop___redArg(v_inst_371_, v_as_372_, v_f_373_, v_i_374_, v_b_375_);
lean_dec(v_i_374_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop(lean_object* v_00_u03b2_377_, lean_object* v_m_378_, lean_object* v_inst_379_, lean_object* v_as_380_, lean_object* v_f_381_, lean_object* v_i_382_, lean_object* v_h_383_, lean_object* v_b_384_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop___redArg(v_inst_379_, v_as_380_, v_f_381_, v_i_382_, v_b_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop___boxed(lean_object* v_00_u03b2_386_, lean_object* v_m_387_, lean_object* v_inst_388_, lean_object* v_as_389_, lean_object* v_f_390_, lean_object* v_i_391_, lean_object* v_h_392_, lean_object* v_b_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop(v_00_u03b2_386_, v_m_387_, v_inst_388_, v_as_389_, v_f_390_, v_i_391_, v_h_392_, v_b_393_);
lean_dec(v_i_391_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_instForInFloatOfMonad___redArg___lam__0(lean_object* v_inst_395_, lean_object* v_00_u03b2_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
size_t v_sz_400_; size_t v___x_401_; lean_object* v___x_402_; 
v_sz_400_ = lean_sarray_size(v___y_397_);
v___x_401_ = ((size_t)0ULL);
v___x_402_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg(v_inst_395_, v___y_397_, v___y_399_, v_sz_400_, v___x_401_, v___y_398_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_instForInFloatOfMonad___redArg(lean_object* v_inst_403_){
_start:
{
lean_object* v___f_404_; 
v___f_404_ = lean_alloc_closure((void*)(l_FloatArray_instForInFloatOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_404_, 0, v_inst_403_);
return v___f_404_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_instForInFloatOfMonad(lean_object* v_m_405_, lean_object* v_inst_406_){
_start:
{
lean_object* v___f_407_; 
v___f_407_ = lean_alloc_closure((void*)(l_FloatArray_instForInFloatOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_407_, 0, v_inst_406_);
return v___f_407_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg___lam__0___boxed(lean_object* v_i_408_, lean_object* v_inst_409_, lean_object* v_f_410_, lean_object* v_as_411_, lean_object* v_stop_412_, lean_object* v_____do__lift_413_){
_start:
{
size_t v_i_boxed_414_; size_t v_stop_boxed_415_; lean_object* v_res_416_; 
v_i_boxed_414_ = lean_unbox_usize(v_i_408_);
lean_dec(v_i_408_);
v_stop_boxed_415_ = lean_unbox_usize(v_stop_412_);
lean_dec(v_stop_412_);
v_res_416_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg___lam__0(v_i_boxed_414_, v_inst_409_, v_f_410_, v_as_411_, v_stop_boxed_415_, v_____do__lift_413_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(lean_object* v_inst_417_, lean_object* v_f_418_, lean_object* v_as_419_, size_t v_i_420_, size_t v_stop_421_, lean_object* v_b_422_){
_start:
{
uint8_t v___x_423_; 
v___x_423_ = lean_usize_dec_eq(v_i_420_, v_stop_421_);
if (v___x_423_ == 0)
{
lean_object* v_toBind_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___f_427_; double v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v_toBind_424_ = lean_ctor_get(v_inst_417_, 1);
lean_inc(v_toBind_424_);
v___x_425_ = lean_box_usize(v_i_420_);
v___x_426_ = lean_box_usize(v_stop_421_);
lean_inc_ref(v_as_419_);
lean_inc(v_f_418_);
v___f_427_ = lean_alloc_closure((void*)(l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_427_, 0, v___x_425_);
lean_closure_set(v___f_427_, 1, v_inst_417_);
lean_closure_set(v___f_427_, 2, v_f_418_);
lean_closure_set(v___f_427_, 3, v_as_419_);
lean_closure_set(v___f_427_, 4, v___x_426_);
v___x_428_ = lean_float_array_uget(v_as_419_, v_i_420_);
lean_dec_ref(v_as_419_);
v___x_429_ = lean_box_float(v___x_428_);
v___x_430_ = lean_apply_2(v_f_418_, v_b_422_, v___x_429_);
v___x_431_ = lean_apply_4(v_toBind_424_, lean_box(0), lean_box(0), v___x_430_, v___f_427_);
return v___x_431_;
}
else
{
lean_object* v_toApplicative_432_; lean_object* v_toPure_433_; lean_object* v___x_434_; 
lean_dec_ref(v_as_419_);
lean_dec(v_f_418_);
v_toApplicative_432_ = lean_ctor_get(v_inst_417_, 0);
lean_inc_ref(v_toApplicative_432_);
lean_dec_ref(v_inst_417_);
v_toPure_433_ = lean_ctor_get(v_toApplicative_432_, 1);
lean_inc(v_toPure_433_);
lean_dec_ref(v_toApplicative_432_);
v___x_434_ = lean_apply_2(v_toPure_433_, lean_box(0), v_b_422_);
return v___x_434_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg___lam__0(size_t v_i_435_, lean_object* v_inst_436_, lean_object* v_f_437_, lean_object* v_as_438_, size_t v_stop_439_, lean_object* v_____do__lift_440_){
_start:
{
size_t v___x_441_; size_t v___x_442_; lean_object* v___x_443_; 
v___x_441_ = ((size_t)1ULL);
v___x_442_ = lean_usize_add(v_i_435_, v___x_441_);
v___x_443_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(v_inst_436_, v_f_437_, v_as_438_, v___x_442_, v_stop_439_, v_____do__lift_440_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg___boxed(lean_object* v_inst_444_, lean_object* v_f_445_, lean_object* v_as_446_, lean_object* v_i_447_, lean_object* v_stop_448_, lean_object* v_b_449_){
_start:
{
size_t v_i_boxed_450_; size_t v_stop_boxed_451_; lean_object* v_res_452_; 
v_i_boxed_450_ = lean_unbox_usize(v_i_447_);
lean_dec(v_i_447_);
v_stop_boxed_451_ = lean_unbox_usize(v_stop_448_);
lean_dec(v_stop_448_);
v_res_452_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(v_inst_444_, v_f_445_, v_as_446_, v_i_boxed_450_, v_stop_boxed_451_, v_b_449_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold(lean_object* v_00_u03b2_453_, lean_object* v_m_454_, lean_object* v_inst_455_, lean_object* v_f_456_, lean_object* v_as_457_, size_t v_i_458_, size_t v_stop_459_, lean_object* v_b_460_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(v_inst_455_, v_f_456_, v_as_457_, v_i_458_, v_stop_459_, v_b_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___boxed(lean_object* v_00_u03b2_462_, lean_object* v_m_463_, lean_object* v_inst_464_, lean_object* v_f_465_, lean_object* v_as_466_, lean_object* v_i_467_, lean_object* v_stop_468_, lean_object* v_b_469_){
_start:
{
size_t v_i_boxed_470_; size_t v_stop_boxed_471_; lean_object* v_res_472_; 
v_i_boxed_470_ = lean_unbox_usize(v_i_467_);
lean_dec(v_i_467_);
v_stop_boxed_471_ = lean_unbox_usize(v_stop_468_);
lean_dec(v_stop_468_);
v_res_472_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold(v_00_u03b2_462_, v_m_463_, v_inst_464_, v_f_465_, v_as_466_, v_i_boxed_470_, v_stop_boxed_471_, v_b_469_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_foldlMUnsafe___redArg(lean_object* v_inst_473_, lean_object* v_f_474_, lean_object* v_init_475_, lean_object* v_as_476_, lean_object* v_start_477_, lean_object* v_stop_478_){
_start:
{
uint8_t v___x_479_; 
v___x_479_ = lean_nat_dec_lt(v_start_477_, v_stop_478_);
if (v___x_479_ == 0)
{
lean_object* v_toApplicative_480_; lean_object* v_toPure_481_; lean_object* v___x_482_; 
lean_dec_ref(v_as_476_);
lean_dec(v_f_474_);
v_toApplicative_480_ = lean_ctor_get(v_inst_473_, 0);
lean_inc_ref(v_toApplicative_480_);
lean_dec_ref(v_inst_473_);
v_toPure_481_ = lean_ctor_get(v_toApplicative_480_, 1);
lean_inc(v_toPure_481_);
lean_dec_ref(v_toApplicative_480_);
v___x_482_ = lean_apply_2(v_toPure_481_, lean_box(0), v_init_475_);
return v___x_482_;
}
else
{
lean_object* v___x_483_; uint8_t v___x_484_; 
v___x_483_ = lean_float_array_size(v_as_476_);
v___x_484_ = lean_nat_dec_le(v_stop_478_, v___x_483_);
if (v___x_484_ == 0)
{
uint8_t v___x_485_; 
v___x_485_ = lean_nat_dec_lt(v_start_477_, v___x_483_);
if (v___x_485_ == 0)
{
lean_object* v_toApplicative_486_; lean_object* v_toPure_487_; lean_object* v___x_488_; 
lean_dec_ref(v_as_476_);
lean_dec(v_f_474_);
v_toApplicative_486_ = lean_ctor_get(v_inst_473_, 0);
lean_inc_ref(v_toApplicative_486_);
lean_dec_ref(v_inst_473_);
v_toPure_487_ = lean_ctor_get(v_toApplicative_486_, 1);
lean_inc(v_toPure_487_);
lean_dec_ref(v_toApplicative_486_);
v___x_488_ = lean_apply_2(v_toPure_487_, lean_box(0), v_init_475_);
return v___x_488_;
}
else
{
size_t v___x_489_; size_t v___x_490_; lean_object* v___x_491_; 
v___x_489_ = lean_usize_of_nat(v_start_477_);
v___x_490_ = lean_usize_of_nat(v___x_483_);
v___x_491_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(v_inst_473_, v_f_474_, v_as_476_, v___x_489_, v___x_490_, v_init_475_);
return v___x_491_;
}
}
else
{
size_t v___x_492_; size_t v___x_493_; lean_object* v___x_494_; 
v___x_492_ = lean_usize_of_nat(v_start_477_);
v___x_493_ = lean_usize_of_nat(v_stop_478_);
v___x_494_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(v_inst_473_, v_f_474_, v_as_476_, v___x_492_, v___x_493_, v_init_475_);
return v___x_494_;
}
}
}
}
LEAN_EXPORT lean_object* l_FloatArray_foldlMUnsafe___redArg___boxed(lean_object* v_inst_495_, lean_object* v_f_496_, lean_object* v_init_497_, lean_object* v_as_498_, lean_object* v_start_499_, lean_object* v_stop_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_FloatArray_foldlMUnsafe___redArg(v_inst_495_, v_f_496_, v_init_497_, v_as_498_, v_start_499_, v_stop_500_);
lean_dec(v_stop_500_);
lean_dec(v_start_499_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_FloatArray_foldlMUnsafe(lean_object* v_00_u03b2_502_, lean_object* v_m_503_, lean_object* v_inst_504_, lean_object* v_f_505_, lean_object* v_init_506_, lean_object* v_as_507_, lean_object* v_start_508_, lean_object* v_stop_509_){
_start:
{
uint8_t v___x_510_; 
v___x_510_ = lean_nat_dec_lt(v_start_508_, v_stop_509_);
if (v___x_510_ == 0)
{
lean_object* v_toApplicative_511_; lean_object* v_toPure_512_; lean_object* v___x_513_; 
lean_dec_ref(v_as_507_);
lean_dec(v_f_505_);
v_toApplicative_511_ = lean_ctor_get(v_inst_504_, 0);
lean_inc_ref(v_toApplicative_511_);
lean_dec_ref(v_inst_504_);
v_toPure_512_ = lean_ctor_get(v_toApplicative_511_, 1);
lean_inc(v_toPure_512_);
lean_dec_ref(v_toApplicative_511_);
v___x_513_ = lean_apply_2(v_toPure_512_, lean_box(0), v_init_506_);
return v___x_513_;
}
else
{
lean_object* v___x_514_; uint8_t v___x_515_; 
v___x_514_ = lean_float_array_size(v_as_507_);
v___x_515_ = lean_nat_dec_le(v_stop_509_, v___x_514_);
if (v___x_515_ == 0)
{
uint8_t v___x_516_; 
v___x_516_ = lean_nat_dec_lt(v_start_508_, v___x_514_);
if (v___x_516_ == 0)
{
lean_object* v_toApplicative_517_; lean_object* v_toPure_518_; lean_object* v___x_519_; 
lean_dec_ref(v_as_507_);
lean_dec(v_f_505_);
v_toApplicative_517_ = lean_ctor_get(v_inst_504_, 0);
lean_inc_ref(v_toApplicative_517_);
lean_dec_ref(v_inst_504_);
v_toPure_518_ = lean_ctor_get(v_toApplicative_517_, 1);
lean_inc(v_toPure_518_);
lean_dec_ref(v_toApplicative_517_);
v___x_519_ = lean_apply_2(v_toPure_518_, lean_box(0), v_init_506_);
return v___x_519_;
}
else
{
size_t v___x_520_; size_t v___x_521_; lean_object* v___x_522_; 
v___x_520_ = lean_usize_of_nat(v_start_508_);
v___x_521_ = lean_usize_of_nat(v___x_514_);
v___x_522_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(v_inst_504_, v_f_505_, v_as_507_, v___x_520_, v___x_521_, v_init_506_);
return v___x_522_;
}
}
else
{
size_t v___x_523_; size_t v___x_524_; lean_object* v___x_525_; 
v___x_523_ = lean_usize_of_nat(v_start_508_);
v___x_524_ = lean_usize_of_nat(v_stop_509_);
v___x_525_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(v_inst_504_, v_f_505_, v_as_507_, v___x_523_, v___x_524_, v_init_506_);
return v___x_525_;
}
}
}
}
LEAN_EXPORT lean_object* l_FloatArray_foldlMUnsafe___boxed(lean_object* v_00_u03b2_526_, lean_object* v_m_527_, lean_object* v_inst_528_, lean_object* v_f_529_, lean_object* v_init_530_, lean_object* v_as_531_, lean_object* v_start_532_, lean_object* v_stop_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_FloatArray_foldlMUnsafe(v_00_u03b2_526_, v_m_527_, v_inst_528_, v_f_529_, v_init_530_, v_as_531_, v_start_532_, v_stop_533_);
lean_dec(v_stop_533_);
lean_dec(v_start_532_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop___redArg___lam__0___boxed(lean_object* v_j_535_, lean_object* v_inst_536_, lean_object* v_f_537_, lean_object* v_as_538_, lean_object* v_stop_539_, lean_object* v_n_540_, lean_object* v_____do__lift_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop___redArg___lam__0(v_j_535_, v_inst_536_, v_f_537_, v_as_538_, v_stop_539_, v_n_540_, v_____do__lift_541_);
lean_dec(v_n_540_);
lean_dec(v_j_535_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop___redArg(lean_object* v_inst_543_, lean_object* v_f_544_, lean_object* v_as_545_, lean_object* v_stop_546_, lean_object* v_i_547_, lean_object* v_j_548_, lean_object* v_b_549_){
_start:
{
uint8_t v___x_550_; 
v___x_550_ = lean_nat_dec_lt(v_j_548_, v_stop_546_);
if (v___x_550_ == 0)
{
lean_object* v_toApplicative_551_; lean_object* v_toPure_552_; lean_object* v___x_553_; 
lean_dec(v_j_548_);
lean_dec(v_stop_546_);
lean_dec_ref(v_as_545_);
lean_dec(v_f_544_);
v_toApplicative_551_ = lean_ctor_get(v_inst_543_, 0);
lean_inc_ref(v_toApplicative_551_);
lean_dec_ref(v_inst_543_);
v_toPure_552_ = lean_ctor_get(v_toApplicative_551_, 1);
lean_inc(v_toPure_552_);
lean_dec_ref(v_toApplicative_551_);
v___x_553_ = lean_apply_2(v_toPure_552_, lean_box(0), v_b_549_);
return v___x_553_;
}
else
{
lean_object* v_zero_554_; uint8_t v_isZero_555_; 
v_zero_554_ = lean_unsigned_to_nat(0u);
v_isZero_555_ = lean_nat_dec_eq(v_i_547_, v_zero_554_);
if (v_isZero_555_ == 1)
{
lean_object* v_toApplicative_556_; lean_object* v_toPure_557_; lean_object* v___x_558_; 
lean_dec(v_j_548_);
lean_dec(v_stop_546_);
lean_dec_ref(v_as_545_);
lean_dec(v_f_544_);
v_toApplicative_556_ = lean_ctor_get(v_inst_543_, 0);
lean_inc_ref(v_toApplicative_556_);
lean_dec_ref(v_inst_543_);
v_toPure_557_ = lean_ctor_get(v_toApplicative_556_, 1);
lean_inc(v_toPure_557_);
lean_dec_ref(v_toApplicative_556_);
v___x_558_ = lean_apply_2(v_toPure_557_, lean_box(0), v_b_549_);
return v___x_558_;
}
else
{
lean_object* v_toBind_559_; lean_object* v_one_560_; lean_object* v_n_561_; lean_object* v___f_562_; double v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v_toBind_559_ = lean_ctor_get(v_inst_543_, 1);
lean_inc(v_toBind_559_);
v_one_560_ = lean_unsigned_to_nat(1u);
v_n_561_ = lean_nat_sub(v_i_547_, v_one_560_);
lean_inc_ref(v_as_545_);
lean_inc(v_f_544_);
lean_inc(v_j_548_);
v___f_562_ = lean_alloc_closure((void*)(l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_562_, 0, v_j_548_);
lean_closure_set(v___f_562_, 1, v_inst_543_);
lean_closure_set(v___f_562_, 2, v_f_544_);
lean_closure_set(v___f_562_, 3, v_as_545_);
lean_closure_set(v___f_562_, 4, v_stop_546_);
lean_closure_set(v___f_562_, 5, v_n_561_);
v___x_563_ = lean_float_array_fget(v_as_545_, v_j_548_);
lean_dec(v_j_548_);
lean_dec_ref(v_as_545_);
v___x_564_ = lean_box_float(v___x_563_);
v___x_565_ = lean_apply_2(v_f_544_, v_b_549_, v___x_564_);
v___x_566_ = lean_apply_4(v_toBind_559_, lean_box(0), lean_box(0), v___x_565_, v___f_562_);
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
double v_x2_190__boxed_615_; lean_object* v_res_616_; 
v_x2_190__boxed_615_ = lean_unbox_float(v_x2_614_);
lean_dec_ref(v_x2_614_);
v_res_616_ = l_FloatArray_foldl___redArg___lam__0(v_f_612_, v_x1_613_, v_x2_190__boxed_615_);
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
lean_object* runtime_initialize_Init_Data_Float(uint8_t builtin);
lean_object* runtime_initialize_Init_Ext(uint8_t builtin);
lean_object* runtime_initialize_Init_GetElem(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Extra(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_FloatArray_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Float(builtin);
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
lean_object* initialize_Init_Data_Float(uint8_t builtin);
lean_object* initialize_Init_Ext(uint8_t builtin);
lean_object* initialize_Init_GetElem(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Extra(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_FloatArray_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Float(builtin);
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
