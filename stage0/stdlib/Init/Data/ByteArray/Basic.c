// Lean compiler output
// Module: Init.Data.ByteArray.Basic
// Imports: import all Init.Data.UInt.BasicAux public import Init.Data.Array.DecidableEq public import Init.Data.List.Attach import Init.Data.Array.Bootstrap import Init.Data.Array.Lemmas import Init.Omega
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
lean_object* lean_byte_array_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_ByteArray_empty;
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_instDecidableEqUInt8___boxed(lean_object*, lean_object*);
lean_object* lean_byte_array_data(lean_object*);
uint8_t l_Array_instDecidableEqImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint8_of_nat(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00ByteArray_instBEq_beq_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00ByteArray_instBEq_beq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_ByteArray_instBEq_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_instBEq_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00ByteArray_instBEq_beq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00ByteArray_instBEq_beq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_ByteArray_instBEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ByteArray_instBEq_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ByteArray_instBEq___closed__0 = (const lean_object*)&l_ByteArray_instBEq___closed__0_value;
LEAN_EXPORT const lean_object* l_ByteArray_instBEq = (const lean_object*)&l_ByteArray_instBEq___closed__0_value;
LEAN_EXPORT uint8_t l_ByteArray_instDecidableEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_instDecidableEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_instInhabited;
LEAN_EXPORT lean_object* l_ByteArray_instEmptyCollection;
size_t lean_sarray_size(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_usize___boxed(lean_object*);
static const lean_string_object l_ByteArray_uget___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_ByteArray_uget___auto__1___closed__0 = (const lean_object*)&l_ByteArray_uget___auto__1___closed__0_value;
static const lean_string_object l_ByteArray_uget___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_ByteArray_uget___auto__1___closed__1 = (const lean_object*)&l_ByteArray_uget___auto__1___closed__1_value;
static const lean_string_object l_ByteArray_uget___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_ByteArray_uget___auto__1___closed__2 = (const lean_object*)&l_ByteArray_uget___auto__1___closed__2_value;
static const lean_string_object l_ByteArray_uget___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_ByteArray_uget___auto__1___closed__3 = (const lean_object*)&l_ByteArray_uget___auto__1___closed__3_value;
static const lean_ctor_object l_ByteArray_uget___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_ByteArray_uget___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_ByteArray_uget___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_ByteArray_uget___auto__1___closed__4_value_aux_0),((lean_object*)&l_ByteArray_uget___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_ByteArray_uget___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_ByteArray_uget___auto__1___closed__4_value_aux_1),((lean_object*)&l_ByteArray_uget___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_ByteArray_uget___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_ByteArray_uget___auto__1___closed__4_value_aux_2),((lean_object*)&l_ByteArray_uget___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_ByteArray_uget___auto__1___closed__4 = (const lean_object*)&l_ByteArray_uget___auto__1___closed__4_value;
static const lean_array_object l_ByteArray_uget___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_ByteArray_uget___auto__1___closed__5 = (const lean_object*)&l_ByteArray_uget___auto__1___closed__5_value;
static const lean_string_object l_ByteArray_uget___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_ByteArray_uget___auto__1___closed__6 = (const lean_object*)&l_ByteArray_uget___auto__1___closed__6_value;
static const lean_ctor_object l_ByteArray_uget___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_ByteArray_uget___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_ByteArray_uget___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_ByteArray_uget___auto__1___closed__7_value_aux_0),((lean_object*)&l_ByteArray_uget___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_ByteArray_uget___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_ByteArray_uget___auto__1___closed__7_value_aux_1),((lean_object*)&l_ByteArray_uget___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_ByteArray_uget___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_ByteArray_uget___auto__1___closed__7_value_aux_2),((lean_object*)&l_ByteArray_uget___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_ByteArray_uget___auto__1___closed__7 = (const lean_object*)&l_ByteArray_uget___auto__1___closed__7_value;
static const lean_string_object l_ByteArray_uget___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_ByteArray_uget___auto__1___closed__8 = (const lean_object*)&l_ByteArray_uget___auto__1___closed__8_value;
static const lean_ctor_object l_ByteArray_uget___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_ByteArray_uget___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_ByteArray_uget___auto__1___closed__9 = (const lean_object*)&l_ByteArray_uget___auto__1___closed__9_value;
static const lean_string_object l_ByteArray_uget___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "tacticGet_elem_tactic"};
static const lean_object* l_ByteArray_uget___auto__1___closed__10 = (const lean_object*)&l_ByteArray_uget___auto__1___closed__10_value;
static const lean_ctor_object l_ByteArray_uget___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_ByteArray_uget___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(141, 31, 109, 153, 11, 229, 201, 51)}};
static const lean_object* l_ByteArray_uget___auto__1___closed__11 = (const lean_object*)&l_ByteArray_uget___auto__1___closed__11_value;
static const lean_string_object l_ByteArray_uget___auto__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "get_elem_tactic"};
static const lean_object* l_ByteArray_uget___auto__1___closed__12 = (const lean_object*)&l_ByteArray_uget___auto__1___closed__12_value;
static lean_once_cell_t l_ByteArray_uget___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_ByteArray_uget___auto__1___closed__13;
static lean_once_cell_t l_ByteArray_uget___auto__1___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_ByteArray_uget___auto__1___closed__14;
static lean_once_cell_t l_ByteArray_uget___auto__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_ByteArray_uget___auto__1___closed__15;
static lean_once_cell_t l_ByteArray_uget___auto__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_ByteArray_uget___auto__1___closed__16;
static lean_once_cell_t l_ByteArray_uget___auto__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_ByteArray_uget___auto__1___closed__17;
static lean_once_cell_t l_ByteArray_uget___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_ByteArray_uget___auto__1___closed__18;
static lean_once_cell_t l_ByteArray_uget___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_ByteArray_uget___auto__1___closed__19;
static lean_once_cell_t l_ByteArray_uget___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_ByteArray_uget___auto__1___closed__20;
static lean_once_cell_t l_ByteArray_uget___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_ByteArray_uget___auto__1___closed__21;
LEAN_EXPORT lean_object* l_ByteArray_uget___auto__1;
uint8_t lean_byte_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_ByteArray_uget___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_byte_array_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_get_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_get___auto__1;
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_get___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_ByteArray_instGetElemNatUInt8LtSize___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_instGetElemNatUInt8LtSize___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_ByteArray_instGetElemNatUInt8LtSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ByteArray_instGetElemNatUInt8LtSize___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ByteArray_instGetElemNatUInt8LtSize___closed__0 = (const lean_object*)&l_ByteArray_instGetElemNatUInt8LtSize___closed__0_value;
LEAN_EXPORT const lean_object* l_ByteArray_instGetElemNatUInt8LtSize = (const lean_object*)&l_ByteArray_instGetElemNatUInt8LtSize___closed__0_value;
LEAN_EXPORT uint8_t l_ByteArray_instGetElemUSizeUInt8LtNatValToFinSize___lam__0(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_instGetElemUSizeUInt8LtNatValToFinSize___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_ByteArray_instGetElemUSizeUInt8LtNatValToFinSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ByteArray_instGetElemUSizeUInt8LtNatValToFinSize___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ByteArray_instGetElemUSizeUInt8LtNatValToFinSize___closed__0 = (const lean_object*)&l_ByteArray_instGetElemUSizeUInt8LtNatValToFinSize___closed__0_value;
LEAN_EXPORT const lean_object* l_ByteArray_instGetElemUSizeUInt8LtNatValToFinSize = (const lean_object*)&l_ByteArray_instGetElemUSizeUInt8LtNatValToFinSize___closed__0_value;
lean_object* lean_byte_array_set(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_ByteArray_set_x21___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_set___auto__1;
lean_object* lean_byte_array_fset(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_ByteArray_set___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_uset___auto__1;
lean_object* lean_byte_array_uset(lean_object*, size_t, uint8_t);
LEAN_EXPORT lean_object* l_ByteArray_uset___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_byte_array_hash(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_hash___boxed(lean_object*);
static const lean_closure_object l_ByteArray_instHashable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ByteArray_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ByteArray_instHashable___closed__0 = (const lean_object*)&l_ByteArray_instHashable___closed__0_value;
LEAN_EXPORT const lean_object* l_ByteArray_instHashable = (const lean_object*)&l_ByteArray_instHashable___closed__0_value;
LEAN_EXPORT uint8_t l_ByteArray_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_isEmpty___boxed(lean_object*);
lean_object* lean_byte_array_copy_slice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_ByteArray_copySlice___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_extract___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_fastAppend(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_fastAppend___boxed(lean_object*, lean_object*);
static const lean_closure_object l_ByteArray_instAppend___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ByteArray_fastAppend___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ByteArray_instAppend___closed__0 = (const lean_object*)&l_ByteArray_instAppend___closed__0_value;
LEAN_EXPORT const lean_object* l_ByteArray_instAppend = (const lean_object*)&l_ByteArray_instAppend___closed__0_value;
LEAN_EXPORT lean_object* l_ByteArray_toList_loop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_toList_loop___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_toList(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_toList___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_findFinIdx_x3f_loop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_findFinIdx_x3f_loop___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_findFinIdx_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_findFinIdx_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe_loop___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe_loop___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe_loop___redArg___lam__0(lean_object*, size_t, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe_loop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_forIn_loop___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_forIn_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_forIn_loop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_forIn_loop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_forIn_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_forIn_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_instForInUInt8OfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_instForInUInt8OfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_instForInUInt8OfMonad(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___redArg___lam__0(size_t, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_foldlM_loop___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_foldlM_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_foldlM_loop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_foldlM_loop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_foldlM_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_foldlM_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_foldl___redArg___lam__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_ByteArray_foldl___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_ByteArray_foldl___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ByteArray_foldl___redArg___closed__0 = (const lean_object*)&l_ByteArray_foldl___redArg___closed__0_value;
static const lean_closure_object l_ByteArray_foldl___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ByteArray_foldl___redArg___closed__1 = (const lean_object*)&l_ByteArray_foldl___redArg___closed__1_value;
static const lean_closure_object l_ByteArray_foldl___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ByteArray_foldl___redArg___closed__2 = (const lean_object*)&l_ByteArray_foldl___redArg___closed__2_value;
static const lean_closure_object l_ByteArray_foldl___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ByteArray_foldl___redArg___closed__3 = (const lean_object*)&l_ByteArray_foldl___redArg___closed__3_value;
static const lean_closure_object l_ByteArray_foldl___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ByteArray_foldl___redArg___closed__4 = (const lean_object*)&l_ByteArray_foldl___redArg___closed__4_value;
static const lean_closure_object l_ByteArray_foldl___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ByteArray_foldl___redArg___closed__5 = (const lean_object*)&l_ByteArray_foldl___redArg___closed__5_value;
static const lean_closure_object l_ByteArray_foldl___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ByteArray_foldl___redArg___closed__6 = (const lean_object*)&l_ByteArray_foldl___redArg___closed__6_value;
static const lean_ctor_object l_ByteArray_foldl___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_ByteArray_foldl___redArg___closed__0_value),((lean_object*)&l_ByteArray_foldl___redArg___closed__1_value)}};
static const lean_object* l_ByteArray_foldl___redArg___closed__7 = (const lean_object*)&l_ByteArray_foldl___redArg___closed__7_value;
static const lean_ctor_object l_ByteArray_foldl___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_ByteArray_foldl___redArg___closed__7_value),((lean_object*)&l_ByteArray_foldl___redArg___closed__2_value),((lean_object*)&l_ByteArray_foldl___redArg___closed__3_value),((lean_object*)&l_ByteArray_foldl___redArg___closed__4_value),((lean_object*)&l_ByteArray_foldl___redArg___closed__5_value)}};
static const lean_object* l_ByteArray_foldl___redArg___closed__8 = (const lean_object*)&l_ByteArray_foldl___redArg___closed__8_value;
static const lean_ctor_object l_ByteArray_foldl___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_ByteArray_foldl___redArg___closed__8_value),((lean_object*)&l_ByteArray_foldl___redArg___closed__6_value)}};
static const lean_object* l_ByteArray_foldl___redArg___closed__9 = (const lean_object*)&l_ByteArray_foldl___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_ByteArray_foldl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_foldl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_foldl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_foldl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_ByteArray_instInhabitedIterator_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_ByteArray_instInhabitedIterator_default___closed__0;
LEAN_EXPORT lean_object* l_ByteArray_instInhabitedIterator_default;
LEAN_EXPORT lean_object* l_ByteArray_instInhabitedIterator;
LEAN_EXPORT lean_object* l_ByteArray_mkIterator(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_iter(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_instSizeOfIterator___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_instSizeOfIterator___lam__0___boxed(lean_object*);
static const lean_closure_object l_ByteArray_instSizeOfIterator___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ByteArray_instSizeOfIterator___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ByteArray_instSizeOfIterator___closed__0 = (const lean_object*)&l_ByteArray_instSizeOfIterator___closed__0_value;
LEAN_EXPORT const lean_object* l_ByteArray_instSizeOfIterator = (const lean_object*)&l_ByteArray_instSizeOfIterator___closed__0_value;
LEAN_EXPORT lean_object* l_ByteArray_Iterator_remainingBytes(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_Iterator_remainingBytes___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_Iterator_pos(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_Iterator_pos___boxed(lean_object*);
LEAN_EXPORT uint8_t l_ByteArray_Iterator_atEnd(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_Iterator_atEnd___boxed(lean_object*);
static lean_once_cell_t l_ByteArray_Iterator_curr___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_ByteArray_Iterator_curr___closed__0;
LEAN_EXPORT uint8_t l_ByteArray_Iterator_curr(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_Iterator_curr___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_Iterator_next(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_Iterator_prev(lean_object*);
LEAN_EXPORT uint8_t l_ByteArray_Iterator_hasNext(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_Iterator_hasNext___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Basic_0__ByteArray_Iterator_remainingBytes_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Basic_0__ByteArray_Iterator_remainingBytes_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_ByteArray_Iterator_curr_x27___redArg(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_Iterator_curr_x27___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_ByteArray_Iterator_curr_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_Iterator_curr_x27___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_Iterator_next_x27___redArg(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_Iterator_next_x27(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_ByteArray_Iterator_hasPrev(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_Iterator_hasPrev___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_Iterator_toEnd(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_Iterator_forward(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_Iterator_forward___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_Iterator_nextn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_Iterator_nextn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_Iterator_prevn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_Iterator_prevn___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00ByteArray_instBEq_beq_spec__0___redArg(lean_object* v_xs_1_, lean_object* v_ys_2_, lean_object* v_x_3_){
_start:
{
lean_object* v_zero_4_; uint8_t v_isZero_5_; 
v_zero_4_ = lean_unsigned_to_nat(0u);
v_isZero_5_ = lean_nat_dec_eq(v_x_3_, v_zero_4_);
if (v_isZero_5_ == 1)
{
lean_dec(v_x_3_);
return v_isZero_5_;
}
else
{
lean_object* v_one_6_; lean_object* v_n_7_; lean_object* v___x_8_; lean_object* v___x_9_; uint8_t v___x_10_; uint8_t v___x_11_; uint8_t v___x_12_; 
v_one_6_ = lean_unsigned_to_nat(1u);
v_n_7_ = lean_nat_sub(v_x_3_, v_one_6_);
lean_dec(v_x_3_);
v___x_8_ = lean_array_fget_borrowed(v_xs_1_, v_n_7_);
v___x_9_ = lean_array_fget_borrowed(v_ys_2_, v_n_7_);
v___x_10_ = lean_unbox(v___x_8_);
v___x_11_ = lean_unbox(v___x_9_);
v___x_12_ = lean_uint8_dec_eq(v___x_10_, v___x_11_);
if (v___x_12_ == 0)
{
lean_dec(v_n_7_);
return v___x_12_;
}
else
{
v_x_3_ = v_n_7_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00ByteArray_instBEq_beq_spec__0___redArg___boxed(lean_object* v_xs_14_, lean_object* v_ys_15_, lean_object* v_x_16_){
_start:
{
uint8_t v_res_17_; lean_object* v_r_18_; 
v_res_17_ = l_Array_isEqvAux___at___00ByteArray_instBEq_beq_spec__0___redArg(v_xs_14_, v_ys_15_, v_x_16_);
lean_dec_ref(v_ys_15_);
lean_dec_ref(v_xs_14_);
v_r_18_ = lean_box(v_res_17_);
return v_r_18_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_instBEq_beq(lean_object* v_x_19_, lean_object* v_x_20_){
_start:
{
lean_object* v_data_21_; lean_object* v_data_22_; lean_object* v___x_23_; lean_object* v___x_24_; uint8_t v___x_25_; 
v_data_21_ = lean_byte_array_data(v_x_19_);
v_data_22_ = lean_byte_array_data(v_x_20_);
v___x_23_ = lean_array_get_size(v_data_21_);
v___x_24_ = lean_array_get_size(v_data_22_);
v___x_25_ = lean_nat_dec_eq(v___x_23_, v___x_24_);
if (v___x_25_ == 0)
{
lean_dec_ref(v_data_22_);
lean_dec_ref(v_data_21_);
return v___x_25_;
}
else
{
uint8_t v___x_26_; 
v___x_26_ = l_Array_isEqvAux___at___00ByteArray_instBEq_beq_spec__0___redArg(v_data_21_, v_data_22_, v___x_23_);
lean_dec_ref(v_data_22_);
lean_dec_ref(v_data_21_);
return v___x_26_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_instBEq_beq___boxed(lean_object* v_x_27_, lean_object* v_x_28_){
_start:
{
uint8_t v_res_29_; lean_object* v_r_30_; 
v_res_29_ = l_ByteArray_instBEq_beq(v_x_27_, v_x_28_);
v_r_30_ = lean_box(v_res_29_);
return v_r_30_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00ByteArray_instBEq_beq_spec__0(lean_object* v_xs_31_, lean_object* v_ys_32_, lean_object* v_hsz_33_, lean_object* v_x_34_, lean_object* v_x_35_){
_start:
{
uint8_t v___x_36_; 
v___x_36_ = l_Array_isEqvAux___at___00ByteArray_instBEq_beq_spec__0___redArg(v_xs_31_, v_ys_32_, v_x_34_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00ByteArray_instBEq_beq_spec__0___boxed(lean_object* v_xs_37_, lean_object* v_ys_38_, lean_object* v_hsz_39_, lean_object* v_x_40_, lean_object* v_x_41_){
_start:
{
uint8_t v_res_42_; lean_object* v_r_43_; 
v_res_42_ = l_Array_isEqvAux___at___00ByteArray_instBEq_beq_spec__0(v_xs_37_, v_ys_38_, v_hsz_39_, v_x_40_, v_x_41_);
lean_dec_ref(v_ys_38_);
lean_dec_ref(v_xs_37_);
v_r_43_ = lean_box(v_res_42_);
return v_r_43_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_instDecidableEq(lean_object* v_x_46_, lean_object* v_x_47_){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; uint8_t v___x_51_; 
v___x_48_ = lean_alloc_closure((void*)(l_instDecidableEqUInt8___boxed), 2, 0);
v___x_49_ = lean_byte_array_data(v_x_46_);
v___x_50_ = lean_byte_array_data(v_x_47_);
v___x_51_ = l_Array_instDecidableEqImpl___redArg(v___x_48_, v___x_49_, v___x_50_);
lean_dec_ref(v___x_50_);
lean_dec_ref(v___x_49_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_instDecidableEq___boxed(lean_object* v_x_52_, lean_object* v_x_53_){
_start:
{
uint8_t v_res_54_; lean_object* v_r_55_; 
v_res_54_ = l_ByteArray_instDecidableEq(v_x_52_, v_x_53_);
v_r_55_ = lean_box(v_res_54_);
return v_r_55_;
}
}
static lean_object* _init_l_ByteArray_instInhabited(void){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_ByteArray_empty;
return v___x_56_;
}
}
static lean_object* _init_l_ByteArray_instEmptyCollection(void){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l_ByteArray_empty;
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_usize___boxed(lean_object* v_a_59_){
_start:
{
size_t v_res_60_; lean_object* v_r_61_; 
v_res_60_ = lean_sarray_size(v_a_59_);
lean_dec_ref(v_a_59_);
v_r_61_ = lean_box_usize(v_res_60_);
return v_r_61_;
}
}
static lean_object* _init_l_ByteArray_uget___auto__1___closed__13(void){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_86_ = ((lean_object*)(l_ByteArray_uget___auto__1___closed__12));
v___x_87_ = l_Lean_mkAtom(v___x_86_);
return v___x_87_;
}
}
static lean_object* _init_l_ByteArray_uget___auto__1___closed__14(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_88_ = lean_obj_once(&l_ByteArray_uget___auto__1___closed__13, &l_ByteArray_uget___auto__1___closed__13_once, _init_l_ByteArray_uget___auto__1___closed__13);
v___x_89_ = ((lean_object*)(l_ByteArray_uget___auto__1___closed__5));
v___x_90_ = lean_array_push(v___x_89_, v___x_88_);
return v___x_90_;
}
}
static lean_object* _init_l_ByteArray_uget___auto__1___closed__15(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_91_ = lean_obj_once(&l_ByteArray_uget___auto__1___closed__14, &l_ByteArray_uget___auto__1___closed__14_once, _init_l_ByteArray_uget___auto__1___closed__14);
v___x_92_ = ((lean_object*)(l_ByteArray_uget___auto__1___closed__11));
v___x_93_ = lean_box(2);
v___x_94_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_94_, 0, v___x_93_);
lean_ctor_set(v___x_94_, 1, v___x_92_);
lean_ctor_set(v___x_94_, 2, v___x_91_);
return v___x_94_;
}
}
static lean_object* _init_l_ByteArray_uget___auto__1___closed__16(void){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_95_ = lean_obj_once(&l_ByteArray_uget___auto__1___closed__15, &l_ByteArray_uget___auto__1___closed__15_once, _init_l_ByteArray_uget___auto__1___closed__15);
v___x_96_ = ((lean_object*)(l_ByteArray_uget___auto__1___closed__5));
v___x_97_ = lean_array_push(v___x_96_, v___x_95_);
return v___x_97_;
}
}
static lean_object* _init_l_ByteArray_uget___auto__1___closed__17(void){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_98_ = lean_obj_once(&l_ByteArray_uget___auto__1___closed__16, &l_ByteArray_uget___auto__1___closed__16_once, _init_l_ByteArray_uget___auto__1___closed__16);
v___x_99_ = ((lean_object*)(l_ByteArray_uget___auto__1___closed__9));
v___x_100_ = lean_box(2);
v___x_101_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
lean_ctor_set(v___x_101_, 1, v___x_99_);
lean_ctor_set(v___x_101_, 2, v___x_98_);
return v___x_101_;
}
}
static lean_object* _init_l_ByteArray_uget___auto__1___closed__18(void){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_102_ = lean_obj_once(&l_ByteArray_uget___auto__1___closed__17, &l_ByteArray_uget___auto__1___closed__17_once, _init_l_ByteArray_uget___auto__1___closed__17);
v___x_103_ = ((lean_object*)(l_ByteArray_uget___auto__1___closed__5));
v___x_104_ = lean_array_push(v___x_103_, v___x_102_);
return v___x_104_;
}
}
static lean_object* _init_l_ByteArray_uget___auto__1___closed__19(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_105_ = lean_obj_once(&l_ByteArray_uget___auto__1___closed__18, &l_ByteArray_uget___auto__1___closed__18_once, _init_l_ByteArray_uget___auto__1___closed__18);
v___x_106_ = ((lean_object*)(l_ByteArray_uget___auto__1___closed__7));
v___x_107_ = lean_box(2);
v___x_108_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
lean_ctor_set(v___x_108_, 1, v___x_106_);
lean_ctor_set(v___x_108_, 2, v___x_105_);
return v___x_108_;
}
}
static lean_object* _init_l_ByteArray_uget___auto__1___closed__20(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_109_ = lean_obj_once(&l_ByteArray_uget___auto__1___closed__19, &l_ByteArray_uget___auto__1___closed__19_once, _init_l_ByteArray_uget___auto__1___closed__19);
v___x_110_ = ((lean_object*)(l_ByteArray_uget___auto__1___closed__5));
v___x_111_ = lean_array_push(v___x_110_, v___x_109_);
return v___x_111_;
}
}
static lean_object* _init_l_ByteArray_uget___auto__1___closed__21(void){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_112_ = lean_obj_once(&l_ByteArray_uget___auto__1___closed__20, &l_ByteArray_uget___auto__1___closed__20_once, _init_l_ByteArray_uget___auto__1___closed__20);
v___x_113_ = ((lean_object*)(l_ByteArray_uget___auto__1___closed__4));
v___x_114_ = lean_box(2);
v___x_115_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
lean_ctor_set(v___x_115_, 1, v___x_113_);
lean_ctor_set(v___x_115_, 2, v___x_112_);
return v___x_115_;
}
}
static lean_object* _init_l_ByteArray_uget___auto__1(void){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = lean_obj_once(&l_ByteArray_uget___auto__1___closed__21, &l_ByteArray_uget___auto__1___closed__21_once, _init_l_ByteArray_uget___auto__1___closed__21);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_uget___boxed(lean_object* v_a_120_, lean_object* v_i_121_, lean_object* v_h_122_){
_start:
{
size_t v_i_boxed_123_; uint8_t v_res_124_; lean_object* v_r_125_; 
v_i_boxed_123_ = lean_unbox_usize(v_i_121_);
lean_dec(v_i_121_);
v_res_124_ = lean_byte_array_uget(v_a_120_, v_i_boxed_123_);
lean_dec_ref(v_a_120_);
v_r_125_ = lean_box(v_res_124_);
return v_r_125_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_get_x21___boxed(lean_object* v_a_00___x40___internal___hyg_128_, lean_object* v_a_00___x40___internal___hyg_129_){
_start:
{
uint8_t v_res_130_; lean_object* v_r_131_; 
v_res_130_ = lean_byte_array_get(v_a_00___x40___internal___hyg_128_, v_a_00___x40___internal___hyg_129_);
lean_dec(v_a_00___x40___internal___hyg_129_);
lean_dec_ref(v_a_00___x40___internal___hyg_128_);
v_r_131_ = lean_box(v_res_130_);
return v_r_131_;
}
}
static lean_object* _init_l_ByteArray_get___auto__1(void){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = lean_obj_once(&l_ByteArray_uget___auto__1___closed__21, &l_ByteArray_uget___auto__1___closed__21_once, _init_l_ByteArray_uget___auto__1___closed__21);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_get___boxed(lean_object* v_a_136_, lean_object* v_i_137_, lean_object* v_h_138_){
_start:
{
uint8_t v_res_139_; lean_object* v_r_140_; 
v_res_139_ = lean_byte_array_fget(v_a_136_, v_i_137_);
lean_dec(v_i_137_);
lean_dec_ref(v_a_136_);
v_r_140_ = lean_box(v_res_139_);
return v_r_140_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_instGetElemNatUInt8LtSize___lam__0(lean_object* v_xs_141_, lean_object* v_i_142_, lean_object* v_h_143_){
_start:
{
uint8_t v___x_144_; 
v___x_144_ = lean_byte_array_fget(v_xs_141_, v_i_142_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_instGetElemNatUInt8LtSize___lam__0___boxed(lean_object* v_xs_145_, lean_object* v_i_146_, lean_object* v_h_147_){
_start:
{
uint8_t v_res_148_; lean_object* v_r_149_; 
v_res_148_ = l_ByteArray_instGetElemNatUInt8LtSize___lam__0(v_xs_145_, v_i_146_, v_h_147_);
lean_dec(v_i_146_);
lean_dec_ref(v_xs_145_);
v_r_149_ = lean_box(v_res_148_);
return v_r_149_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_instGetElemUSizeUInt8LtNatValToFinSize___lam__0(lean_object* v_xs_152_, size_t v_i_153_, lean_object* v_h_154_){
_start:
{
uint8_t v___x_155_; 
v___x_155_ = lean_byte_array_uget(v_xs_152_, v_i_153_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_instGetElemUSizeUInt8LtNatValToFinSize___lam__0___boxed(lean_object* v_xs_156_, lean_object* v_i_157_, lean_object* v_h_158_){
_start:
{
size_t v_i_boxed_159_; uint8_t v_res_160_; lean_object* v_r_161_; 
v_i_boxed_159_ = lean_unbox_usize(v_i_157_);
lean_dec(v_i_157_);
v_res_160_ = l_ByteArray_instGetElemUSizeUInt8LtNatValToFinSize___lam__0(v_xs_156_, v_i_boxed_159_, v_h_158_);
lean_dec_ref(v_xs_156_);
v_r_161_ = lean_box(v_res_160_);
return v_r_161_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_set_x21___boxed(lean_object* v_a_00___x40___internal___hyg_167_, lean_object* v_a_00___x40___internal___hyg_168_, lean_object* v_a_00___x40___internal___hyg_169_){
_start:
{
uint8_t v_a_00___x40___internal___hyg_3__boxed_170_; lean_object* v_res_171_; 
v_a_00___x40___internal___hyg_3__boxed_170_ = lean_unbox(v_a_00___x40___internal___hyg_169_);
v_res_171_ = lean_byte_array_set(v_a_00___x40___internal___hyg_167_, v_a_00___x40___internal___hyg_168_, v_a_00___x40___internal___hyg_3__boxed_170_);
lean_dec(v_a_00___x40___internal___hyg_168_);
return v_res_171_;
}
}
static lean_object* _init_l_ByteArray_set___auto__1(void){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = lean_obj_once(&l_ByteArray_uget___auto__1___closed__21, &l_ByteArray_uget___auto__1___closed__21_once, _init_l_ByteArray_uget___auto__1___closed__21);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_set___boxed(lean_object* v_a_177_, lean_object* v_i_178_, lean_object* v_a_00___x40___internal___hyg_179_, lean_object* v_h_180_){
_start:
{
uint8_t v_a_00___x40___internal___hyg_1__boxed_181_; lean_object* v_res_182_; 
v_a_00___x40___internal___hyg_1__boxed_181_ = lean_unbox(v_a_00___x40___internal___hyg_179_);
v_res_182_ = lean_byte_array_fset(v_a_177_, v_i_178_, v_a_00___x40___internal___hyg_1__boxed_181_);
lean_dec(v_i_178_);
return v_res_182_;
}
}
static lean_object* _init_l_ByteArray_uset___auto__1(void){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = lean_obj_once(&l_ByteArray_uget___auto__1___closed__21, &l_ByteArray_uget___auto__1___closed__21_once, _init_l_ByteArray_uget___auto__1___closed__21);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_uset___boxed(lean_object* v_a_188_, lean_object* v_i_189_, lean_object* v_a_00___x40___internal___hyg_190_, lean_object* v_h_191_){
_start:
{
size_t v_i_boxed_192_; uint8_t v_a_00___x40___internal___hyg_1__boxed_193_; lean_object* v_res_194_; 
v_i_boxed_192_ = lean_unbox_usize(v_i_189_);
lean_dec(v_i_189_);
v_a_00___x40___internal___hyg_1__boxed_193_ = lean_unbox(v_a_00___x40___internal___hyg_190_);
v_res_194_ = lean_byte_array_uset(v_a_188_, v_i_boxed_192_, v_a_00___x40___internal___hyg_1__boxed_193_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_hash___boxed(lean_object* v_a_196_){
_start:
{
uint64_t v_res_197_; lean_object* v_r_198_; 
v_res_197_ = lean_byte_array_hash(v_a_196_);
lean_dec_ref(v_a_196_);
v_r_198_ = lean_box_uint64(v_res_197_);
return v_r_198_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_isEmpty(lean_object* v_s_201_){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; uint8_t v___x_204_; 
v___x_202_ = lean_byte_array_size(v_s_201_);
v___x_203_ = lean_unsigned_to_nat(0u);
v___x_204_ = lean_nat_dec_eq(v___x_202_, v___x_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_isEmpty___boxed(lean_object* v_s_205_){
_start:
{
uint8_t v_res_206_; lean_object* v_r_207_; 
v_res_206_ = l_ByteArray_isEmpty(v_s_205_);
lean_dec_ref(v_s_205_);
v_r_207_ = lean_box(v_res_206_);
return v_r_207_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_copySlice___boxed(lean_object* v_src_214_, lean_object* v_srcOff_215_, lean_object* v_dest_216_, lean_object* v_destOff_217_, lean_object* v_len_218_, lean_object* v_exact_219_){
_start:
{
uint8_t v_exact_boxed_220_; lean_object* v_res_221_; 
v_exact_boxed_220_ = lean_unbox(v_exact_219_);
v_res_221_ = lean_byte_array_copy_slice(v_src_214_, v_srcOff_215_, v_dest_216_, v_destOff_217_, v_len_218_, v_exact_boxed_220_);
lean_dec_ref(v_src_214_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_extract(lean_object* v_a_222_, lean_object* v_b_223_, lean_object* v_e_224_){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; uint8_t v___x_228_; lean_object* v___x_229_; 
v___x_225_ = l_ByteArray_empty;
v___x_226_ = lean_unsigned_to_nat(0u);
v___x_227_ = lean_nat_sub(v_e_224_, v_b_223_);
v___x_228_ = 1;
v___x_229_ = lean_byte_array_copy_slice(v_a_222_, v_b_223_, v___x_225_, v___x_226_, v___x_227_, v___x_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_extract___boxed(lean_object* v_a_230_, lean_object* v_b_231_, lean_object* v_e_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_ByteArray_extract(v_a_230_, v_b_231_, v_e_232_);
lean_dec(v_e_232_);
lean_dec_ref(v_a_230_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_fastAppend(lean_object* v_a_234_, lean_object* v_b_235_){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; uint8_t v___x_239_; lean_object* v___x_240_; 
v___x_236_ = lean_unsigned_to_nat(0u);
v___x_237_ = lean_byte_array_size(v_a_234_);
v___x_238_ = lean_byte_array_size(v_b_235_);
v___x_239_ = 0;
v___x_240_ = lean_byte_array_copy_slice(v_b_235_, v___x_236_, v_a_234_, v___x_237_, v___x_238_, v___x_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_fastAppend___boxed(lean_object* v_a_241_, lean_object* v_b_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_ByteArray_fastAppend(v_a_241_, v_b_242_);
lean_dec_ref(v_b_242_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_toList_loop(lean_object* v_bs_246_, lean_object* v_i_247_, lean_object* v_r_248_){
_start:
{
lean_object* v___x_249_; uint8_t v___x_250_; 
v___x_249_ = lean_byte_array_size(v_bs_246_);
v___x_250_ = lean_nat_dec_lt(v_i_247_, v___x_249_);
if (v___x_250_ == 0)
{
lean_object* v___x_251_; 
lean_dec(v_i_247_);
v___x_251_ = l_List_reverse___redArg(v_r_248_);
return v___x_251_;
}
else
{
lean_object* v___x_252_; lean_object* v___x_253_; uint8_t v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_252_ = lean_unsigned_to_nat(1u);
v___x_253_ = lean_nat_add(v_i_247_, v___x_252_);
v___x_254_ = lean_byte_array_get(v_bs_246_, v_i_247_);
lean_dec(v_i_247_);
v___x_255_ = lean_box(v___x_254_);
v___x_256_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_255_);
lean_ctor_set(v___x_256_, 1, v_r_248_);
v_i_247_ = v___x_253_;
v_r_248_ = v___x_256_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_toList_loop___boxed(lean_object* v_bs_258_, lean_object* v_i_259_, lean_object* v_r_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_ByteArray_toList_loop(v_bs_258_, v_i_259_, v_r_260_);
lean_dec_ref(v_bs_258_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_toList(lean_object* v_bs_262_){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_263_ = lean_unsigned_to_nat(0u);
v___x_264_ = lean_box(0);
v___x_265_ = l_ByteArray_toList_loop(v_bs_262_, v___x_263_, v___x_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_toList___boxed(lean_object* v_bs_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_ByteArray_toList(v_bs_266_);
lean_dec_ref(v_bs_266_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findFinIdx_x3f_loop(lean_object* v_a_268_, lean_object* v_p_269_, lean_object* v_i_270_){
_start:
{
lean_object* v___x_271_; uint8_t v___x_272_; 
v___x_271_ = lean_byte_array_size(v_a_268_);
v___x_272_ = lean_nat_dec_lt(v_i_270_, v___x_271_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; 
lean_dec(v_i_270_);
lean_dec_ref(v_p_269_);
v___x_273_ = lean_box(0);
return v___x_273_;
}
else
{
uint8_t v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; uint8_t v___x_277_; 
v___x_274_ = lean_byte_array_fget(v_a_268_, v_i_270_);
v___x_275_ = lean_box(v___x_274_);
lean_inc_ref(v_p_269_);
v___x_276_ = lean_apply_1(v_p_269_, v___x_275_);
v___x_277_ = lean_unbox(v___x_276_);
if (v___x_277_ == 0)
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = lean_unsigned_to_nat(1u);
v___x_279_ = lean_nat_add(v_i_270_, v___x_278_);
lean_dec(v_i_270_);
v_i_270_ = v___x_279_;
goto _start;
}
else
{
lean_object* v___x_281_; 
lean_dec_ref(v_p_269_);
v___x_281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_281_, 0, v_i_270_);
return v___x_281_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_findFinIdx_x3f_loop___boxed(lean_object* v_a_282_, lean_object* v_p_283_, lean_object* v_i_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_ByteArray_findFinIdx_x3f_loop(v_a_282_, v_p_283_, v_i_284_);
lean_dec_ref(v_a_282_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findFinIdx_x3f(lean_object* v_a_286_, lean_object* v_p_287_, lean_object* v_start_288_){
_start:
{
lean_object* v___x_289_; 
v___x_289_ = l_ByteArray_findFinIdx_x3f_loop(v_a_286_, v_p_287_, v_start_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findFinIdx_x3f___boxed(lean_object* v_a_290_, lean_object* v_p_291_, lean_object* v_start_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_ByteArray_findFinIdx_x3f(v_a_290_, v_p_291_, v_start_292_);
lean_dec_ref(v_a_290_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop(lean_object* v_a_294_, lean_object* v_p_295_, lean_object* v_i_296_){
_start:
{
lean_object* v___x_297_; uint8_t v___x_298_; 
v___x_297_ = lean_byte_array_size(v_a_294_);
v___x_298_ = lean_nat_dec_lt(v_i_296_, v___x_297_);
if (v___x_298_ == 0)
{
lean_object* v___x_299_; 
lean_dec(v_i_296_);
lean_dec_ref(v_p_295_);
v___x_299_ = lean_box(0);
return v___x_299_;
}
else
{
uint8_t v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; uint8_t v___x_303_; 
v___x_300_ = lean_byte_array_fget(v_a_294_, v_i_296_);
v___x_301_ = lean_box(v___x_300_);
lean_inc_ref(v_p_295_);
v___x_302_ = lean_apply_1(v_p_295_, v___x_301_);
v___x_303_ = lean_unbox(v___x_302_);
if (v___x_303_ == 0)
{
lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_304_ = lean_unsigned_to_nat(1u);
v___x_305_ = lean_nat_add(v_i_296_, v___x_304_);
lean_dec(v_i_296_);
v_i_296_ = v___x_305_;
goto _start;
}
else
{
lean_object* v___x_307_; 
lean_dec_ref(v_p_295_);
v___x_307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_307_, 0, v_i_296_);
return v___x_307_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___boxed(lean_object* v_a_308_, lean_object* v_p_309_, lean_object* v_i_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l_ByteArray_findIdx_x3f_loop(v_a_308_, v_p_309_, v_i_310_);
lean_dec_ref(v_a_308_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f(lean_object* v_a_312_, lean_object* v_p_313_, lean_object* v_start_314_){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = l_ByteArray_findIdx_x3f_loop(v_a_312_, v_p_313_, v_start_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f___boxed(lean_object* v_a_316_, lean_object* v_p_317_, lean_object* v_start_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_ByteArray_findIdx_x3f(v_a_316_, v_p_317_, v_start_318_);
lean_dec_ref(v_a_316_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe_loop___redArg___lam__0___boxed(lean_object* v_toApplicative_320_, lean_object* v_i_321_, lean_object* v_inst_322_, lean_object* v_as_323_, lean_object* v_f_324_, lean_object* v_sz_325_, lean_object* v_____do__lift_326_){
_start:
{
size_t v_i_boxed_327_; size_t v_sz_boxed_328_; lean_object* v_res_329_; 
v_i_boxed_327_ = lean_unbox_usize(v_i_321_);
lean_dec(v_i_321_);
v_sz_boxed_328_ = lean_unbox_usize(v_sz_325_);
lean_dec(v_sz_325_);
v_res_329_ = l_ByteArray_forInUnsafe_loop___redArg___lam__0(v_toApplicative_320_, v_i_boxed_327_, v_inst_322_, v_as_323_, v_f_324_, v_sz_boxed_328_, v_____do__lift_326_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe_loop___redArg(lean_object* v_inst_330_, lean_object* v_as_331_, lean_object* v_f_332_, size_t v_sz_333_, size_t v_i_334_, lean_object* v_b_335_){
_start:
{
uint8_t v___x_336_; 
v___x_336_ = lean_usize_dec_lt(v_i_334_, v_sz_333_);
if (v___x_336_ == 0)
{
lean_object* v_toApplicative_337_; lean_object* v_toPure_338_; lean_object* v___x_339_; 
lean_dec(v_f_332_);
lean_dec_ref(v_as_331_);
v_toApplicative_337_ = lean_ctor_get(v_inst_330_, 0);
lean_inc_ref(v_toApplicative_337_);
lean_dec_ref(v_inst_330_);
v_toPure_338_ = lean_ctor_get(v_toApplicative_337_, 1);
lean_inc(v_toPure_338_);
lean_dec_ref(v_toApplicative_337_);
v___x_339_ = lean_apply_2(v_toPure_338_, lean_box(0), v_b_335_);
return v___x_339_;
}
else
{
lean_object* v_toApplicative_340_; lean_object* v_toBind_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___f_344_; uint8_t v_a_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v_toApplicative_340_ = lean_ctor_get(v_inst_330_, 0);
lean_inc_ref(v_toApplicative_340_);
v_toBind_341_ = lean_ctor_get(v_inst_330_, 1);
lean_inc(v_toBind_341_);
v___x_342_ = lean_box_usize(v_i_334_);
v___x_343_ = lean_box_usize(v_sz_333_);
lean_inc(v_f_332_);
lean_inc_ref(v_as_331_);
v___f_344_ = lean_alloc_closure((void*)(l_ByteArray_forInUnsafe_loop___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_344_, 0, v_toApplicative_340_);
lean_closure_set(v___f_344_, 1, v___x_342_);
lean_closure_set(v___f_344_, 2, v_inst_330_);
lean_closure_set(v___f_344_, 3, v_as_331_);
lean_closure_set(v___f_344_, 4, v_f_332_);
lean_closure_set(v___f_344_, 5, v___x_343_);
v_a_345_ = lean_byte_array_uget(v_as_331_, v_i_334_);
lean_dec_ref(v_as_331_);
v___x_346_ = lean_box(v_a_345_);
v___x_347_ = lean_apply_2(v_f_332_, v___x_346_, v_b_335_);
v___x_348_ = lean_apply_4(v_toBind_341_, lean_box(0), lean_box(0), v___x_347_, v___f_344_);
return v___x_348_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe_loop___redArg___lam__0(lean_object* v_toApplicative_349_, size_t v_i_350_, lean_object* v_inst_351_, lean_object* v_as_352_, lean_object* v_f_353_, size_t v_sz_354_, lean_object* v_____do__lift_355_){
_start:
{
if (lean_obj_tag(v_____do__lift_355_) == 0)
{
lean_object* v_a_356_; lean_object* v_toPure_357_; lean_object* v___x_358_; 
lean_dec(v_f_353_);
lean_dec_ref(v_as_352_);
lean_dec_ref(v_inst_351_);
v_a_356_ = lean_ctor_get(v_____do__lift_355_, 0);
lean_inc(v_a_356_);
lean_dec_ref(v_____do__lift_355_);
v_toPure_357_ = lean_ctor_get(v_toApplicative_349_, 1);
lean_inc(v_toPure_357_);
lean_dec_ref(v_toApplicative_349_);
v___x_358_ = lean_apply_2(v_toPure_357_, lean_box(0), v_a_356_);
return v___x_358_;
}
else
{
lean_object* v_a_359_; size_t v___x_360_; size_t v___x_361_; lean_object* v___x_362_; 
lean_dec_ref(v_toApplicative_349_);
v_a_359_ = lean_ctor_get(v_____do__lift_355_, 0);
lean_inc(v_a_359_);
lean_dec_ref(v_____do__lift_355_);
v___x_360_ = ((size_t)1ULL);
v___x_361_ = lean_usize_add(v_i_350_, v___x_360_);
v___x_362_ = l_ByteArray_forInUnsafe_loop___redArg(v_inst_351_, v_as_352_, v_f_353_, v_sz_354_, v___x_361_, v_a_359_);
return v___x_362_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe_loop___redArg___boxed(lean_object* v_inst_363_, lean_object* v_as_364_, lean_object* v_f_365_, lean_object* v_sz_366_, lean_object* v_i_367_, lean_object* v_b_368_){
_start:
{
size_t v_sz_boxed_369_; size_t v_i_boxed_370_; lean_object* v_res_371_; 
v_sz_boxed_369_ = lean_unbox_usize(v_sz_366_);
lean_dec(v_sz_366_);
v_i_boxed_370_ = lean_unbox_usize(v_i_367_);
lean_dec(v_i_367_);
v_res_371_ = l_ByteArray_forInUnsafe_loop___redArg(v_inst_363_, v_as_364_, v_f_365_, v_sz_boxed_369_, v_i_boxed_370_, v_b_368_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe_loop(lean_object* v_00_u03b2_372_, lean_object* v_m_373_, lean_object* v_inst_374_, lean_object* v_as_375_, lean_object* v_f_376_, size_t v_sz_377_, size_t v_i_378_, lean_object* v_b_379_){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = l_ByteArray_forInUnsafe_loop___redArg(v_inst_374_, v_as_375_, v_f_376_, v_sz_377_, v_i_378_, v_b_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe_loop___boxed(lean_object* v_00_u03b2_381_, lean_object* v_m_382_, lean_object* v_inst_383_, lean_object* v_as_384_, lean_object* v_f_385_, lean_object* v_sz_386_, lean_object* v_i_387_, lean_object* v_b_388_){
_start:
{
size_t v_sz_boxed_389_; size_t v_i_boxed_390_; lean_object* v_res_391_; 
v_sz_boxed_389_ = lean_unbox_usize(v_sz_386_);
lean_dec(v_sz_386_);
v_i_boxed_390_ = lean_unbox_usize(v_i_387_);
lean_dec(v_i_387_);
v_res_391_ = l_ByteArray_forInUnsafe_loop(v_00_u03b2_381_, v_m_382_, v_inst_383_, v_as_384_, v_f_385_, v_sz_boxed_389_, v_i_boxed_390_, v_b_388_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe___redArg(lean_object* v_inst_392_, lean_object* v_as_393_, lean_object* v_b_394_, lean_object* v_f_395_){
_start:
{
size_t v_sz_396_; size_t v___x_397_; lean_object* v___x_398_; 
v_sz_396_ = lean_sarray_size(v_as_393_);
v___x_397_ = ((size_t)0ULL);
v___x_398_ = l_ByteArray_forInUnsafe_loop___redArg(v_inst_392_, v_as_393_, v_f_395_, v_sz_396_, v___x_397_, v_b_394_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe(lean_object* v_00_u03b2_399_, lean_object* v_m_400_, lean_object* v_inst_401_, lean_object* v_as_402_, lean_object* v_b_403_, lean_object* v_f_404_){
_start:
{
size_t v_sz_405_; size_t v___x_406_; lean_object* v___x_407_; 
v_sz_405_ = lean_sarray_size(v_as_402_);
v___x_406_ = ((size_t)0ULL);
v___x_407_ = l_ByteArray_forInUnsafe_loop___redArg(v_inst_401_, v_as_402_, v_f_404_, v_sz_405_, v___x_406_, v_b_403_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_forIn_loop___redArg___lam__0___boxed(lean_object* v_toPure_408_, lean_object* v_inst_409_, lean_object* v_as_410_, lean_object* v_f_411_, lean_object* v_n_412_, lean_object* v_____do__lift_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_ByteArray_forIn_loop___redArg___lam__0(v_toPure_408_, v_inst_409_, v_as_410_, v_f_411_, v_n_412_, v_____do__lift_413_);
lean_dec(v_n_412_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_forIn_loop___redArg(lean_object* v_inst_415_, lean_object* v_as_416_, lean_object* v_f_417_, lean_object* v_i_418_, lean_object* v_b_419_){
_start:
{
lean_object* v_toApplicative_420_; lean_object* v_toBind_421_; lean_object* v_toPure_422_; lean_object* v_zero_423_; uint8_t v_isZero_424_; 
v_toApplicative_420_ = lean_ctor_get(v_inst_415_, 0);
v_toBind_421_ = lean_ctor_get(v_inst_415_, 1);
lean_inc(v_toBind_421_);
v_toPure_422_ = lean_ctor_get(v_toApplicative_420_, 1);
lean_inc(v_toPure_422_);
v_zero_423_ = lean_unsigned_to_nat(0u);
v_isZero_424_ = lean_nat_dec_eq(v_i_418_, v_zero_423_);
if (v_isZero_424_ == 1)
{
lean_object* v___x_425_; 
lean_dec(v_toBind_421_);
lean_dec(v_f_417_);
lean_dec_ref(v_as_416_);
lean_dec_ref(v_inst_415_);
v___x_425_ = lean_apply_2(v_toPure_422_, lean_box(0), v_b_419_);
return v___x_425_;
}
else
{
lean_object* v_one_426_; lean_object* v_n_427_; lean_object* v___f_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; uint8_t v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
v_one_426_ = lean_unsigned_to_nat(1u);
v_n_427_ = lean_nat_sub(v_i_418_, v_one_426_);
lean_inc(v_n_427_);
lean_inc(v_f_417_);
lean_inc_ref(v_as_416_);
v___f_428_ = lean_alloc_closure((void*)(l_ByteArray_forIn_loop___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_428_, 0, v_toPure_422_);
lean_closure_set(v___f_428_, 1, v_inst_415_);
lean_closure_set(v___f_428_, 2, v_as_416_);
lean_closure_set(v___f_428_, 3, v_f_417_);
lean_closure_set(v___f_428_, 4, v_n_427_);
v___x_429_ = lean_byte_array_size(v_as_416_);
v___x_430_ = lean_nat_sub(v___x_429_, v_one_426_);
v___x_431_ = lean_nat_sub(v___x_430_, v_n_427_);
lean_dec(v_n_427_);
lean_dec(v___x_430_);
v___x_432_ = lean_byte_array_fget(v_as_416_, v___x_431_);
lean_dec(v___x_431_);
lean_dec_ref(v_as_416_);
v___x_433_ = lean_box(v___x_432_);
v___x_434_ = lean_apply_2(v_f_417_, v___x_433_, v_b_419_);
v___x_435_ = lean_apply_4(v_toBind_421_, lean_box(0), lean_box(0), v___x_434_, v___f_428_);
return v___x_435_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_forIn_loop___redArg___lam__0(lean_object* v_toPure_436_, lean_object* v_inst_437_, lean_object* v_as_438_, lean_object* v_f_439_, lean_object* v_n_440_, lean_object* v_____do__lift_441_){
_start:
{
if (lean_obj_tag(v_____do__lift_441_) == 0)
{
lean_object* v_a_442_; lean_object* v___x_443_; 
lean_dec(v_f_439_);
lean_dec_ref(v_as_438_);
lean_dec_ref(v_inst_437_);
v_a_442_ = lean_ctor_get(v_____do__lift_441_, 0);
lean_inc(v_a_442_);
lean_dec_ref(v_____do__lift_441_);
v___x_443_ = lean_apply_2(v_toPure_436_, lean_box(0), v_a_442_);
return v___x_443_;
}
else
{
lean_object* v_a_444_; lean_object* v___x_445_; 
lean_dec(v_toPure_436_);
v_a_444_ = lean_ctor_get(v_____do__lift_441_, 0);
lean_inc(v_a_444_);
lean_dec_ref(v_____do__lift_441_);
v___x_445_ = l_ByteArray_forIn_loop___redArg(v_inst_437_, v_as_438_, v_f_439_, v_n_440_, v_a_444_);
return v___x_445_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_forIn_loop___redArg___boxed(lean_object* v_inst_446_, lean_object* v_as_447_, lean_object* v_f_448_, lean_object* v_i_449_, lean_object* v_b_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_ByteArray_forIn_loop___redArg(v_inst_446_, v_as_447_, v_f_448_, v_i_449_, v_b_450_);
lean_dec(v_i_449_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_forIn_loop(lean_object* v_00_u03b2_452_, lean_object* v_m_453_, lean_object* v_inst_454_, lean_object* v_as_455_, lean_object* v_f_456_, lean_object* v_i_457_, lean_object* v_h_458_, lean_object* v_b_459_){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = l_ByteArray_forIn_loop___redArg(v_inst_454_, v_as_455_, v_f_456_, v_i_457_, v_b_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_forIn_loop___boxed(lean_object* v_00_u03b2_461_, lean_object* v_m_462_, lean_object* v_inst_463_, lean_object* v_as_464_, lean_object* v_f_465_, lean_object* v_i_466_, lean_object* v_h_467_, lean_object* v_b_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_ByteArray_forIn_loop(v_00_u03b2_461_, v_m_462_, v_inst_463_, v_as_464_, v_f_465_, v_i_466_, v_h_467_, v_b_468_);
lean_dec(v_i_466_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_instForInUInt8OfMonad___redArg___lam__0(lean_object* v_inst_470_, lean_object* v_00_u03b2_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_){
_start:
{
size_t v_sz_475_; size_t v___x_476_; lean_object* v___x_477_; 
v_sz_475_ = lean_sarray_size(v___y_472_);
v___x_476_ = ((size_t)0ULL);
v___x_477_ = l_ByteArray_forInUnsafe_loop___redArg(v_inst_470_, v___y_472_, v___y_474_, v_sz_475_, v___x_476_, v___y_473_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_instForInUInt8OfMonad___redArg(lean_object* v_inst_478_){
_start:
{
lean_object* v___f_479_; 
v___f_479_ = lean_alloc_closure((void*)(l_ByteArray_instForInUInt8OfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_479_, 0, v_inst_478_);
return v___f_479_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_instForInUInt8OfMonad(lean_object* v_m_480_, lean_object* v_inst_481_){
_start:
{
lean_object* v___f_482_; 
v___f_482_ = lean_alloc_closure((void*)(l_ByteArray_instForInUInt8OfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_482_, 0, v_inst_481_);
return v___f_482_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___redArg___lam__0___boxed(lean_object* v_i_483_, lean_object* v_inst_484_, lean_object* v_f_485_, lean_object* v_as_486_, lean_object* v_stop_487_, lean_object* v_____do__lift_488_){
_start:
{
size_t v_i_boxed_489_; size_t v_stop_boxed_490_; lean_object* v_res_491_; 
v_i_boxed_489_ = lean_unbox_usize(v_i_483_);
lean_dec(v_i_483_);
v_stop_boxed_490_ = lean_unbox_usize(v_stop_487_);
lean_dec(v_stop_487_);
v_res_491_ = l_ByteArray_foldlMUnsafe_fold___redArg___lam__0(v_i_boxed_489_, v_inst_484_, v_f_485_, v_as_486_, v_stop_boxed_490_, v_____do__lift_488_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___redArg(lean_object* v_inst_492_, lean_object* v_f_493_, lean_object* v_as_494_, size_t v_i_495_, size_t v_stop_496_, lean_object* v_b_497_){
_start:
{
uint8_t v___x_498_; 
v___x_498_ = lean_usize_dec_eq(v_i_495_, v_stop_496_);
if (v___x_498_ == 0)
{
lean_object* v_toBind_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___f_502_; uint8_t v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v_toBind_499_ = lean_ctor_get(v_inst_492_, 1);
lean_inc(v_toBind_499_);
v___x_500_ = lean_box_usize(v_i_495_);
v___x_501_ = lean_box_usize(v_stop_496_);
lean_inc_ref(v_as_494_);
lean_inc(v_f_493_);
v___f_502_ = lean_alloc_closure((void*)(l_ByteArray_foldlMUnsafe_fold___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_502_, 0, v___x_500_);
lean_closure_set(v___f_502_, 1, v_inst_492_);
lean_closure_set(v___f_502_, 2, v_f_493_);
lean_closure_set(v___f_502_, 3, v_as_494_);
lean_closure_set(v___f_502_, 4, v___x_501_);
v___x_503_ = lean_byte_array_uget(v_as_494_, v_i_495_);
lean_dec_ref(v_as_494_);
v___x_504_ = lean_box(v___x_503_);
v___x_505_ = lean_apply_2(v_f_493_, v_b_497_, v___x_504_);
v___x_506_ = lean_apply_4(v_toBind_499_, lean_box(0), lean_box(0), v___x_505_, v___f_502_);
return v___x_506_;
}
else
{
lean_object* v_toApplicative_507_; lean_object* v_toPure_508_; lean_object* v___x_509_; 
lean_dec_ref(v_as_494_);
lean_dec(v_f_493_);
v_toApplicative_507_ = lean_ctor_get(v_inst_492_, 0);
lean_inc_ref(v_toApplicative_507_);
lean_dec_ref(v_inst_492_);
v_toPure_508_ = lean_ctor_get(v_toApplicative_507_, 1);
lean_inc(v_toPure_508_);
lean_dec_ref(v_toApplicative_507_);
v___x_509_ = lean_apply_2(v_toPure_508_, lean_box(0), v_b_497_);
return v___x_509_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___redArg___lam__0(size_t v_i_510_, lean_object* v_inst_511_, lean_object* v_f_512_, lean_object* v_as_513_, size_t v_stop_514_, lean_object* v_____do__lift_515_){
_start:
{
size_t v___x_516_; size_t v___x_517_; lean_object* v___x_518_; 
v___x_516_ = ((size_t)1ULL);
v___x_517_ = lean_usize_add(v_i_510_, v___x_516_);
v___x_518_ = l_ByteArray_foldlMUnsafe_fold___redArg(v_inst_511_, v_f_512_, v_as_513_, v___x_517_, v_stop_514_, v_____do__lift_515_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___redArg___boxed(lean_object* v_inst_519_, lean_object* v_f_520_, lean_object* v_as_521_, lean_object* v_i_522_, lean_object* v_stop_523_, lean_object* v_b_524_){
_start:
{
size_t v_i_boxed_525_; size_t v_stop_boxed_526_; lean_object* v_res_527_; 
v_i_boxed_525_ = lean_unbox_usize(v_i_522_);
lean_dec(v_i_522_);
v_stop_boxed_526_ = lean_unbox_usize(v_stop_523_);
lean_dec(v_stop_523_);
v_res_527_ = l_ByteArray_foldlMUnsafe_fold___redArg(v_inst_519_, v_f_520_, v_as_521_, v_i_boxed_525_, v_stop_boxed_526_, v_b_524_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold(lean_object* v_00_u03b2_528_, lean_object* v_m_529_, lean_object* v_inst_530_, lean_object* v_f_531_, lean_object* v_as_532_, size_t v_i_533_, size_t v_stop_534_, lean_object* v_b_535_){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = l_ByteArray_foldlMUnsafe_fold___redArg(v_inst_530_, v_f_531_, v_as_532_, v_i_533_, v_stop_534_, v_b_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___boxed(lean_object* v_00_u03b2_537_, lean_object* v_m_538_, lean_object* v_inst_539_, lean_object* v_f_540_, lean_object* v_as_541_, lean_object* v_i_542_, lean_object* v_stop_543_, lean_object* v_b_544_){
_start:
{
size_t v_i_boxed_545_; size_t v_stop_boxed_546_; lean_object* v_res_547_; 
v_i_boxed_545_ = lean_unbox_usize(v_i_542_);
lean_dec(v_i_542_);
v_stop_boxed_546_ = lean_unbox_usize(v_stop_543_);
lean_dec(v_stop_543_);
v_res_547_ = l_ByteArray_foldlMUnsafe_fold(v_00_u03b2_537_, v_m_538_, v_inst_539_, v_f_540_, v_as_541_, v_i_boxed_545_, v_stop_boxed_546_, v_b_544_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe___redArg(lean_object* v_inst_548_, lean_object* v_f_549_, lean_object* v_init_550_, lean_object* v_as_551_, lean_object* v_start_552_, lean_object* v_stop_553_){
_start:
{
uint8_t v___x_554_; 
v___x_554_ = lean_nat_dec_lt(v_start_552_, v_stop_553_);
if (v___x_554_ == 0)
{
lean_object* v_toApplicative_555_; lean_object* v_toPure_556_; lean_object* v___x_557_; 
lean_dec_ref(v_as_551_);
lean_dec(v_f_549_);
v_toApplicative_555_ = lean_ctor_get(v_inst_548_, 0);
lean_inc_ref(v_toApplicative_555_);
lean_dec_ref(v_inst_548_);
v_toPure_556_ = lean_ctor_get(v_toApplicative_555_, 1);
lean_inc(v_toPure_556_);
lean_dec_ref(v_toApplicative_555_);
v___x_557_ = lean_apply_2(v_toPure_556_, lean_box(0), v_init_550_);
return v___x_557_;
}
else
{
lean_object* v___x_558_; uint8_t v___x_559_; 
v___x_558_ = lean_byte_array_size(v_as_551_);
v___x_559_ = lean_nat_dec_le(v_stop_553_, v___x_558_);
if (v___x_559_ == 0)
{
uint8_t v___x_560_; 
v___x_560_ = lean_nat_dec_lt(v_start_552_, v___x_558_);
if (v___x_560_ == 0)
{
lean_object* v_toApplicative_561_; lean_object* v_toPure_562_; lean_object* v___x_563_; 
lean_dec_ref(v_as_551_);
lean_dec(v_f_549_);
v_toApplicative_561_ = lean_ctor_get(v_inst_548_, 0);
lean_inc_ref(v_toApplicative_561_);
lean_dec_ref(v_inst_548_);
v_toPure_562_ = lean_ctor_get(v_toApplicative_561_, 1);
lean_inc(v_toPure_562_);
lean_dec_ref(v_toApplicative_561_);
v___x_563_ = lean_apply_2(v_toPure_562_, lean_box(0), v_init_550_);
return v___x_563_;
}
else
{
size_t v___x_564_; size_t v___x_565_; lean_object* v___x_566_; 
v___x_564_ = lean_usize_of_nat(v_start_552_);
v___x_565_ = lean_usize_of_nat(v___x_558_);
v___x_566_ = l_ByteArray_foldlMUnsafe_fold___redArg(v_inst_548_, v_f_549_, v_as_551_, v___x_564_, v___x_565_, v_init_550_);
return v___x_566_;
}
}
else
{
size_t v___x_567_; size_t v___x_568_; lean_object* v___x_569_; 
v___x_567_ = lean_usize_of_nat(v_start_552_);
v___x_568_ = lean_usize_of_nat(v_stop_553_);
v___x_569_ = l_ByteArray_foldlMUnsafe_fold___redArg(v_inst_548_, v_f_549_, v_as_551_, v___x_567_, v___x_568_, v_init_550_);
return v___x_569_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe___redArg___boxed(lean_object* v_inst_570_, lean_object* v_f_571_, lean_object* v_init_572_, lean_object* v_as_573_, lean_object* v_start_574_, lean_object* v_stop_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_ByteArray_foldlMUnsafe___redArg(v_inst_570_, v_f_571_, v_init_572_, v_as_573_, v_start_574_, v_stop_575_);
lean_dec(v_stop_575_);
lean_dec(v_start_574_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe(lean_object* v_00_u03b2_577_, lean_object* v_m_578_, lean_object* v_inst_579_, lean_object* v_f_580_, lean_object* v_init_581_, lean_object* v_as_582_, lean_object* v_start_583_, lean_object* v_stop_584_){
_start:
{
uint8_t v___x_585_; 
v___x_585_ = lean_nat_dec_lt(v_start_583_, v_stop_584_);
if (v___x_585_ == 0)
{
lean_object* v_toApplicative_586_; lean_object* v_toPure_587_; lean_object* v___x_588_; 
lean_dec_ref(v_as_582_);
lean_dec(v_f_580_);
v_toApplicative_586_ = lean_ctor_get(v_inst_579_, 0);
lean_inc_ref(v_toApplicative_586_);
lean_dec_ref(v_inst_579_);
v_toPure_587_ = lean_ctor_get(v_toApplicative_586_, 1);
lean_inc(v_toPure_587_);
lean_dec_ref(v_toApplicative_586_);
v___x_588_ = lean_apply_2(v_toPure_587_, lean_box(0), v_init_581_);
return v___x_588_;
}
else
{
lean_object* v___x_589_; uint8_t v___x_590_; 
v___x_589_ = lean_byte_array_size(v_as_582_);
v___x_590_ = lean_nat_dec_le(v_stop_584_, v___x_589_);
if (v___x_590_ == 0)
{
uint8_t v___x_591_; 
v___x_591_ = lean_nat_dec_lt(v_start_583_, v___x_589_);
if (v___x_591_ == 0)
{
lean_object* v_toApplicative_592_; lean_object* v_toPure_593_; lean_object* v___x_594_; 
lean_dec_ref(v_as_582_);
lean_dec(v_f_580_);
v_toApplicative_592_ = lean_ctor_get(v_inst_579_, 0);
lean_inc_ref(v_toApplicative_592_);
lean_dec_ref(v_inst_579_);
v_toPure_593_ = lean_ctor_get(v_toApplicative_592_, 1);
lean_inc(v_toPure_593_);
lean_dec_ref(v_toApplicative_592_);
v___x_594_ = lean_apply_2(v_toPure_593_, lean_box(0), v_init_581_);
return v___x_594_;
}
else
{
size_t v___x_595_; size_t v___x_596_; lean_object* v___x_597_; 
v___x_595_ = lean_usize_of_nat(v_start_583_);
v___x_596_ = lean_usize_of_nat(v___x_589_);
v___x_597_ = l_ByteArray_foldlMUnsafe_fold___redArg(v_inst_579_, v_f_580_, v_as_582_, v___x_595_, v___x_596_, v_init_581_);
return v___x_597_;
}
}
else
{
size_t v___x_598_; size_t v___x_599_; lean_object* v___x_600_; 
v___x_598_ = lean_usize_of_nat(v_start_583_);
v___x_599_ = lean_usize_of_nat(v_stop_584_);
v___x_600_ = l_ByteArray_foldlMUnsafe_fold___redArg(v_inst_579_, v_f_580_, v_as_582_, v___x_598_, v___x_599_, v_init_581_);
return v___x_600_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe___boxed(lean_object* v_00_u03b2_601_, lean_object* v_m_602_, lean_object* v_inst_603_, lean_object* v_f_604_, lean_object* v_init_605_, lean_object* v_as_606_, lean_object* v_start_607_, lean_object* v_stop_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_ByteArray_foldlMUnsafe(v_00_u03b2_601_, v_m_602_, v_inst_603_, v_f_604_, v_init_605_, v_as_606_, v_start_607_, v_stop_608_);
lean_dec(v_stop_608_);
lean_dec(v_start_607_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlM_loop___redArg___lam__0___boxed(lean_object* v_j_610_, lean_object* v_inst_611_, lean_object* v_f_612_, lean_object* v_as_613_, lean_object* v_stop_614_, lean_object* v_n_615_, lean_object* v_____do__lift_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_ByteArray_foldlM_loop___redArg___lam__0(v_j_610_, v_inst_611_, v_f_612_, v_as_613_, v_stop_614_, v_n_615_, v_____do__lift_616_);
lean_dec(v_n_615_);
lean_dec(v_j_610_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlM_loop___redArg(lean_object* v_inst_618_, lean_object* v_f_619_, lean_object* v_as_620_, lean_object* v_stop_621_, lean_object* v_i_622_, lean_object* v_j_623_, lean_object* v_b_624_){
_start:
{
uint8_t v___x_625_; 
v___x_625_ = lean_nat_dec_lt(v_j_623_, v_stop_621_);
if (v___x_625_ == 0)
{
lean_object* v_toApplicative_626_; lean_object* v_toPure_627_; lean_object* v___x_628_; 
lean_dec(v_j_623_);
lean_dec(v_stop_621_);
lean_dec_ref(v_as_620_);
lean_dec(v_f_619_);
v_toApplicative_626_ = lean_ctor_get(v_inst_618_, 0);
lean_inc_ref(v_toApplicative_626_);
lean_dec_ref(v_inst_618_);
v_toPure_627_ = lean_ctor_get(v_toApplicative_626_, 1);
lean_inc(v_toPure_627_);
lean_dec_ref(v_toApplicative_626_);
v___x_628_ = lean_apply_2(v_toPure_627_, lean_box(0), v_b_624_);
return v___x_628_;
}
else
{
lean_object* v_zero_629_; uint8_t v_isZero_630_; 
v_zero_629_ = lean_unsigned_to_nat(0u);
v_isZero_630_ = lean_nat_dec_eq(v_i_622_, v_zero_629_);
if (v_isZero_630_ == 1)
{
lean_object* v_toApplicative_631_; lean_object* v_toPure_632_; lean_object* v___x_633_; 
lean_dec(v_j_623_);
lean_dec(v_stop_621_);
lean_dec_ref(v_as_620_);
lean_dec(v_f_619_);
v_toApplicative_631_ = lean_ctor_get(v_inst_618_, 0);
lean_inc_ref(v_toApplicative_631_);
lean_dec_ref(v_inst_618_);
v_toPure_632_ = lean_ctor_get(v_toApplicative_631_, 1);
lean_inc(v_toPure_632_);
lean_dec_ref(v_toApplicative_631_);
v___x_633_ = lean_apply_2(v_toPure_632_, lean_box(0), v_b_624_);
return v___x_633_;
}
else
{
lean_object* v_toBind_634_; lean_object* v_one_635_; lean_object* v_n_636_; lean_object* v___f_637_; uint8_t v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v_toBind_634_ = lean_ctor_get(v_inst_618_, 1);
lean_inc(v_toBind_634_);
v_one_635_ = lean_unsigned_to_nat(1u);
v_n_636_ = lean_nat_sub(v_i_622_, v_one_635_);
lean_inc_ref(v_as_620_);
lean_inc(v_f_619_);
lean_inc(v_j_623_);
v___f_637_ = lean_alloc_closure((void*)(l_ByteArray_foldlM_loop___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_637_, 0, v_j_623_);
lean_closure_set(v___f_637_, 1, v_inst_618_);
lean_closure_set(v___f_637_, 2, v_f_619_);
lean_closure_set(v___f_637_, 3, v_as_620_);
lean_closure_set(v___f_637_, 4, v_stop_621_);
lean_closure_set(v___f_637_, 5, v_n_636_);
v___x_638_ = lean_byte_array_fget(v_as_620_, v_j_623_);
lean_dec(v_j_623_);
lean_dec_ref(v_as_620_);
v___x_639_ = lean_box(v___x_638_);
v___x_640_ = lean_apply_2(v_f_619_, v_b_624_, v___x_639_);
v___x_641_ = lean_apply_4(v_toBind_634_, lean_box(0), lean_box(0), v___x_640_, v___f_637_);
return v___x_641_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlM_loop___redArg___lam__0(lean_object* v_j_642_, lean_object* v_inst_643_, lean_object* v_f_644_, lean_object* v_as_645_, lean_object* v_stop_646_, lean_object* v_n_647_, lean_object* v_____do__lift_648_){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_649_ = lean_unsigned_to_nat(1u);
v___x_650_ = lean_nat_add(v_j_642_, v___x_649_);
v___x_651_ = l_ByteArray_foldlM_loop___redArg(v_inst_643_, v_f_644_, v_as_645_, v_stop_646_, v_n_647_, v___x_650_, v_____do__lift_648_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlM_loop___redArg___boxed(lean_object* v_inst_652_, lean_object* v_f_653_, lean_object* v_as_654_, lean_object* v_stop_655_, lean_object* v_i_656_, lean_object* v_j_657_, lean_object* v_b_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_ByteArray_foldlM_loop___redArg(v_inst_652_, v_f_653_, v_as_654_, v_stop_655_, v_i_656_, v_j_657_, v_b_658_);
lean_dec(v_i_656_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlM_loop(lean_object* v_00_u03b2_660_, lean_object* v_m_661_, lean_object* v_inst_662_, lean_object* v_f_663_, lean_object* v_as_664_, lean_object* v_stop_665_, lean_object* v_h_666_, lean_object* v_i_667_, lean_object* v_j_668_, lean_object* v_b_669_){
_start:
{
lean_object* v___x_670_; 
v___x_670_ = l_ByteArray_foldlM_loop___redArg(v_inst_662_, v_f_663_, v_as_664_, v_stop_665_, v_i_667_, v_j_668_, v_b_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlM_loop___boxed(lean_object* v_00_u03b2_671_, lean_object* v_m_672_, lean_object* v_inst_673_, lean_object* v_f_674_, lean_object* v_as_675_, lean_object* v_stop_676_, lean_object* v_h_677_, lean_object* v_i_678_, lean_object* v_j_679_, lean_object* v_b_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_ByteArray_foldlM_loop(v_00_u03b2_671_, v_m_672_, v_inst_673_, v_f_674_, v_as_675_, v_stop_676_, v_h_677_, v_i_678_, v_j_679_, v_b_680_);
lean_dec(v_i_678_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldl___redArg___lam__0(lean_object* v_f_682_, lean_object* v_x1_683_, uint8_t v_x2_684_){
_start:
{
lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_685_ = lean_box(v_x2_684_);
v___x_686_ = lean_apply_2(v_f_682_, v_x1_683_, v___x_685_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldl___redArg___lam__0___boxed(lean_object* v_f_687_, lean_object* v_x1_688_, lean_object* v_x2_689_){
_start:
{
uint8_t v_x2_190__boxed_690_; lean_object* v_res_691_; 
v_x2_190__boxed_690_ = lean_unbox(v_x2_689_);
v_res_691_ = l_ByteArray_foldl___redArg___lam__0(v_f_687_, v_x1_688_, v_x2_190__boxed_690_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldl___redArg(lean_object* v_f_711_, lean_object* v_init_712_, lean_object* v_as_713_, lean_object* v_start_714_, lean_object* v_stop_715_){
_start:
{
lean_object* v___x_716_; uint8_t v___x_717_; 
v___x_716_ = ((lean_object*)(l_ByteArray_foldl___redArg___closed__9));
v___x_717_ = lean_nat_dec_lt(v_start_714_, v_stop_715_);
if (v___x_717_ == 0)
{
lean_dec_ref(v_as_713_);
lean_dec(v_f_711_);
return v_init_712_;
}
else
{
lean_object* v___f_718_; lean_object* v___x_719_; uint8_t v___x_720_; 
v___f_718_ = lean_alloc_closure((void*)(l_ByteArray_foldl___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_718_, 0, v_f_711_);
v___x_719_ = lean_byte_array_size(v_as_713_);
v___x_720_ = lean_nat_dec_le(v_stop_715_, v___x_719_);
if (v___x_720_ == 0)
{
uint8_t v___x_721_; 
v___x_721_ = lean_nat_dec_lt(v_start_714_, v___x_719_);
if (v___x_721_ == 0)
{
lean_dec_ref(v___f_718_);
lean_dec_ref(v_as_713_);
return v_init_712_;
}
else
{
size_t v___x_722_; size_t v___x_723_; lean_object* v___x_724_; 
v___x_722_ = lean_usize_of_nat(v_start_714_);
v___x_723_ = lean_usize_of_nat(v___x_719_);
v___x_724_ = l_ByteArray_foldlMUnsafe_fold___redArg(v___x_716_, v___f_718_, v_as_713_, v___x_722_, v___x_723_, v_init_712_);
return v___x_724_;
}
}
else
{
size_t v___x_725_; size_t v___x_726_; lean_object* v___x_727_; 
v___x_725_ = lean_usize_of_nat(v_start_714_);
v___x_726_ = lean_usize_of_nat(v_stop_715_);
v___x_727_ = l_ByteArray_foldlMUnsafe_fold___redArg(v___x_716_, v___f_718_, v_as_713_, v___x_725_, v___x_726_, v_init_712_);
return v___x_727_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldl___redArg___boxed(lean_object* v_f_728_, lean_object* v_init_729_, lean_object* v_as_730_, lean_object* v_start_731_, lean_object* v_stop_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l_ByteArray_foldl___redArg(v_f_728_, v_init_729_, v_as_730_, v_start_731_, v_stop_732_);
lean_dec(v_stop_732_);
lean_dec(v_start_731_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldl(lean_object* v_00_u03b2_734_, lean_object* v_f_735_, lean_object* v_init_736_, lean_object* v_as_737_, lean_object* v_start_738_, lean_object* v_stop_739_){
_start:
{
lean_object* v___x_740_; uint8_t v___x_741_; 
v___x_740_ = ((lean_object*)(l_ByteArray_foldl___redArg___closed__9));
v___x_741_ = lean_nat_dec_lt(v_start_738_, v_stop_739_);
if (v___x_741_ == 0)
{
lean_dec_ref(v_as_737_);
lean_dec(v_f_735_);
return v_init_736_;
}
else
{
lean_object* v___f_742_; lean_object* v___x_743_; uint8_t v___x_744_; 
v___f_742_ = lean_alloc_closure((void*)(l_ByteArray_foldl___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_742_, 0, v_f_735_);
v___x_743_ = lean_byte_array_size(v_as_737_);
v___x_744_ = lean_nat_dec_le(v_stop_739_, v___x_743_);
if (v___x_744_ == 0)
{
uint8_t v___x_745_; 
v___x_745_ = lean_nat_dec_lt(v_start_738_, v___x_743_);
if (v___x_745_ == 0)
{
lean_dec_ref(v___f_742_);
lean_dec_ref(v_as_737_);
return v_init_736_;
}
else
{
size_t v___x_746_; size_t v___x_747_; lean_object* v___x_748_; 
v___x_746_ = lean_usize_of_nat(v_start_738_);
v___x_747_ = lean_usize_of_nat(v___x_743_);
v___x_748_ = l_ByteArray_foldlMUnsafe_fold___redArg(v___x_740_, v___f_742_, v_as_737_, v___x_746_, v___x_747_, v_init_736_);
return v___x_748_;
}
}
else
{
size_t v___x_749_; size_t v___x_750_; lean_object* v___x_751_; 
v___x_749_ = lean_usize_of_nat(v_start_738_);
v___x_750_ = lean_usize_of_nat(v_stop_739_);
v___x_751_ = l_ByteArray_foldlMUnsafe_fold___redArg(v___x_740_, v___f_742_, v_as_737_, v___x_749_, v___x_750_, v_init_736_);
return v___x_751_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldl___boxed(lean_object* v_00_u03b2_752_, lean_object* v_f_753_, lean_object* v_init_754_, lean_object* v_as_755_, lean_object* v_start_756_, lean_object* v_stop_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_ByteArray_foldl(v_00_u03b2_752_, v_f_753_, v_init_754_, v_as_755_, v_start_756_, v_stop_757_);
lean_dec(v_stop_757_);
lean_dec(v_start_756_);
return v_res_758_;
}
}
static lean_object* _init_l_ByteArray_instInhabitedIterator_default___closed__0(void){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_759_ = lean_unsigned_to_nat(0u);
v___x_760_ = l_ByteArray_empty;
v___x_761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_761_, 0, v___x_760_);
lean_ctor_set(v___x_761_, 1, v___x_759_);
return v___x_761_;
}
}
static lean_object* _init_l_ByteArray_instInhabitedIterator_default(void){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = lean_obj_once(&l_ByteArray_instInhabitedIterator_default___closed__0, &l_ByteArray_instInhabitedIterator_default___closed__0_once, _init_l_ByteArray_instInhabitedIterator_default___closed__0);
return v___x_762_;
}
}
static lean_object* _init_l_ByteArray_instInhabitedIterator(void){
_start:
{
lean_object* v___x_763_; 
v___x_763_ = l_ByteArray_instInhabitedIterator_default;
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_mkIterator(lean_object* v_arr_764_){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_765_ = lean_unsigned_to_nat(0u);
v___x_766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_766_, 0, v_arr_764_);
lean_ctor_set(v___x_766_, 1, v___x_765_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_iter(lean_object* v_arr_767_){
_start:
{
lean_object* v___x_768_; 
v___x_768_ = l_ByteArray_mkIterator(v_arr_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_instSizeOfIterator___lam__0(lean_object* v_i_769_){
_start:
{
lean_object* v_array_770_; lean_object* v_idx_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v_array_770_ = lean_ctor_get(v_i_769_, 0);
v_idx_771_ = lean_ctor_get(v_i_769_, 1);
v___x_772_ = lean_byte_array_size(v_array_770_);
v___x_773_ = lean_nat_sub(v___x_772_, v_idx_771_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_instSizeOfIterator___lam__0___boxed(lean_object* v_i_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_ByteArray_instSizeOfIterator___lam__0(v_i_774_);
lean_dec_ref(v_i_774_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_remainingBytes(lean_object* v_x_778_){
_start:
{
lean_object* v_array_779_; lean_object* v_idx_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v_array_779_ = lean_ctor_get(v_x_778_, 0);
v_idx_780_ = lean_ctor_get(v_x_778_, 1);
v___x_781_ = lean_byte_array_size(v_array_779_);
v___x_782_ = lean_nat_sub(v___x_781_, v_idx_780_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_remainingBytes___boxed(lean_object* v_x_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_ByteArray_Iterator_remainingBytes(v_x_783_);
lean_dec_ref(v_x_783_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_pos(lean_object* v_self_785_){
_start:
{
lean_object* v_idx_786_; 
v_idx_786_ = lean_ctor_get(v_self_785_, 1);
lean_inc(v_idx_786_);
return v_idx_786_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_pos___boxed(lean_object* v_self_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_ByteArray_Iterator_pos(v_self_787_);
lean_dec_ref(v_self_787_);
return v_res_788_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_Iterator_atEnd(lean_object* v_x_789_){
_start:
{
lean_object* v_array_790_; lean_object* v_idx_791_; lean_object* v___x_792_; uint8_t v___x_793_; 
v_array_790_ = lean_ctor_get(v_x_789_, 0);
v_idx_791_ = lean_ctor_get(v_x_789_, 1);
v___x_792_ = lean_byte_array_size(v_array_790_);
v___x_793_ = lean_nat_dec_le(v___x_792_, v_idx_791_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_atEnd___boxed(lean_object* v_x_794_){
_start:
{
uint8_t v_res_795_; lean_object* v_r_796_; 
v_res_795_ = l_ByteArray_Iterator_atEnd(v_x_794_);
lean_dec_ref(v_x_794_);
v_r_796_ = lean_box(v_res_795_);
return v_r_796_;
}
}
static uint8_t _init_l_ByteArray_Iterator_curr___closed__0(void){
_start:
{
lean_object* v___x_797_; uint8_t v___x_798_; 
v___x_797_ = lean_unsigned_to_nat(0u);
v___x_798_ = lean_uint8_of_nat(v___x_797_);
return v___x_798_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_Iterator_curr(lean_object* v_x_799_){
_start:
{
lean_object* v_array_800_; lean_object* v_idx_801_; lean_object* v___x_802_; uint8_t v___x_803_; 
v_array_800_ = lean_ctor_get(v_x_799_, 0);
v_idx_801_ = lean_ctor_get(v_x_799_, 1);
v___x_802_ = lean_byte_array_size(v_array_800_);
v___x_803_ = lean_nat_dec_lt(v_idx_801_, v___x_802_);
if (v___x_803_ == 0)
{
uint8_t v___x_804_; 
v___x_804_ = lean_uint8_once(&l_ByteArray_Iterator_curr___closed__0, &l_ByteArray_Iterator_curr___closed__0_once, _init_l_ByteArray_Iterator_curr___closed__0);
return v___x_804_;
}
else
{
uint8_t v___x_805_; 
v___x_805_ = lean_byte_array_fget(v_array_800_, v_idx_801_);
return v___x_805_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_curr___boxed(lean_object* v_x_806_){
_start:
{
uint8_t v_res_807_; lean_object* v_r_808_; 
v_res_807_ = l_ByteArray_Iterator_curr(v_x_806_);
lean_dec_ref(v_x_806_);
v_r_808_ = lean_box(v_res_807_);
return v_r_808_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_next(lean_object* v_x_809_){
_start:
{
lean_object* v_array_810_; lean_object* v_idx_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_820_; 
v_array_810_ = lean_ctor_get(v_x_809_, 0);
v_idx_811_ = lean_ctor_get(v_x_809_, 1);
v_isSharedCheck_820_ = !lean_is_exclusive(v_x_809_);
if (v_isSharedCheck_820_ == 0)
{
v___x_813_ = v_x_809_;
v_isShared_814_ = v_isSharedCheck_820_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_idx_811_);
lean_inc(v_array_810_);
lean_dec(v_x_809_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_820_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_818_; 
v___x_815_ = lean_unsigned_to_nat(1u);
v___x_816_ = lean_nat_add(v_idx_811_, v___x_815_);
lean_dec(v_idx_811_);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 1, v___x_816_);
v___x_818_ = v___x_813_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_array_810_);
lean_ctor_set(v_reuseFailAlloc_819_, 1, v___x_816_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_prev(lean_object* v_x_821_){
_start:
{
lean_object* v_array_822_; lean_object* v_idx_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_832_; 
v_array_822_ = lean_ctor_get(v_x_821_, 0);
v_idx_823_ = lean_ctor_get(v_x_821_, 1);
v_isSharedCheck_832_ = !lean_is_exclusive(v_x_821_);
if (v_isSharedCheck_832_ == 0)
{
v___x_825_ = v_x_821_;
v_isShared_826_ = v_isSharedCheck_832_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_idx_823_);
lean_inc(v_array_822_);
lean_dec(v_x_821_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_832_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_830_; 
v___x_827_ = lean_unsigned_to_nat(1u);
v___x_828_ = lean_nat_sub(v_idx_823_, v___x_827_);
lean_dec(v_idx_823_);
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 1, v___x_828_);
v___x_830_ = v___x_825_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_array_822_);
lean_ctor_set(v_reuseFailAlloc_831_, 1, v___x_828_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
}
}
LEAN_EXPORT uint8_t l_ByteArray_Iterator_hasNext(lean_object* v_x_833_){
_start:
{
lean_object* v_array_834_; lean_object* v_idx_835_; lean_object* v___x_836_; uint8_t v___x_837_; 
v_array_834_ = lean_ctor_get(v_x_833_, 0);
v_idx_835_ = lean_ctor_get(v_x_833_, 1);
v___x_836_ = lean_byte_array_size(v_array_834_);
v___x_837_ = lean_nat_dec_lt(v_idx_835_, v___x_836_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_hasNext___boxed(lean_object* v_x_838_){
_start:
{
uint8_t v_res_839_; lean_object* v_r_840_; 
v_res_839_ = l_ByteArray_Iterator_hasNext(v_x_838_);
lean_dec_ref(v_x_838_);
v_r_840_ = lean_box(v_res_839_);
return v_r_840_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Basic_0__ByteArray_Iterator_remainingBytes_match__1_splitter___redArg(lean_object* v_x_841_, lean_object* v_h__1_842_){
_start:
{
lean_object* v_array_843_; lean_object* v_idx_844_; lean_object* v___x_845_; 
v_array_843_ = lean_ctor_get(v_x_841_, 0);
lean_inc_ref(v_array_843_);
v_idx_844_ = lean_ctor_get(v_x_841_, 1);
lean_inc(v_idx_844_);
lean_dec_ref(v_x_841_);
v___x_845_ = lean_apply_2(v_h__1_842_, v_array_843_, v_idx_844_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Basic_0__ByteArray_Iterator_remainingBytes_match__1_splitter(lean_object* v_motive_846_, lean_object* v_x_847_, lean_object* v_h__1_848_){
_start:
{
lean_object* v_array_849_; lean_object* v_idx_850_; lean_object* v___x_851_; 
v_array_849_ = lean_ctor_get(v_x_847_, 0);
lean_inc_ref(v_array_849_);
v_idx_850_ = lean_ctor_get(v_x_847_, 1);
lean_inc(v_idx_850_);
lean_dec_ref(v_x_847_);
v___x_851_ = lean_apply_2(v_h__1_848_, v_array_849_, v_idx_850_);
return v___x_851_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_Iterator_curr_x27___redArg(lean_object* v_it_852_){
_start:
{
lean_object* v_array_853_; lean_object* v_idx_854_; uint8_t v___x_855_; 
v_array_853_ = lean_ctor_get(v_it_852_, 0);
v_idx_854_ = lean_ctor_get(v_it_852_, 1);
v___x_855_ = lean_byte_array_fget(v_array_853_, v_idx_854_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_curr_x27___redArg___boxed(lean_object* v_it_856_){
_start:
{
uint8_t v_res_857_; lean_object* v_r_858_; 
v_res_857_ = l_ByteArray_Iterator_curr_x27___redArg(v_it_856_);
lean_dec_ref(v_it_856_);
v_r_858_ = lean_box(v_res_857_);
return v_r_858_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_Iterator_curr_x27(lean_object* v_it_859_, lean_object* v_h_860_){
_start:
{
lean_object* v_array_861_; lean_object* v_idx_862_; uint8_t v___x_863_; 
v_array_861_ = lean_ctor_get(v_it_859_, 0);
v_idx_862_ = lean_ctor_get(v_it_859_, 1);
v___x_863_ = lean_byte_array_fget(v_array_861_, v_idx_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_curr_x27___boxed(lean_object* v_it_864_, lean_object* v_h_865_){
_start:
{
uint8_t v_res_866_; lean_object* v_r_867_; 
v_res_866_ = l_ByteArray_Iterator_curr_x27(v_it_864_, v_h_865_);
lean_dec_ref(v_it_864_);
v_r_867_ = lean_box(v_res_866_);
return v_r_867_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_next_x27___redArg(lean_object* v_it_868_){
_start:
{
lean_object* v_array_869_; lean_object* v_idx_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_879_; 
v_array_869_ = lean_ctor_get(v_it_868_, 0);
v_idx_870_ = lean_ctor_get(v_it_868_, 1);
v_isSharedCheck_879_ = !lean_is_exclusive(v_it_868_);
if (v_isSharedCheck_879_ == 0)
{
v___x_872_ = v_it_868_;
v_isShared_873_ = v_isSharedCheck_879_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_idx_870_);
lean_inc(v_array_869_);
lean_dec(v_it_868_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_879_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_877_; 
v___x_874_ = lean_unsigned_to_nat(1u);
v___x_875_ = lean_nat_add(v_idx_870_, v___x_874_);
lean_dec(v_idx_870_);
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 1, v___x_875_);
v___x_877_ = v___x_872_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_array_869_);
lean_ctor_set(v_reuseFailAlloc_878_, 1, v___x_875_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_next_x27(lean_object* v_it_880_, lean_object* v___h_881_){
_start:
{
lean_object* v_array_882_; lean_object* v_idx_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_892_; 
v_array_882_ = lean_ctor_get(v_it_880_, 0);
v_idx_883_ = lean_ctor_get(v_it_880_, 1);
v_isSharedCheck_892_ = !lean_is_exclusive(v_it_880_);
if (v_isSharedCheck_892_ == 0)
{
v___x_885_ = v_it_880_;
v_isShared_886_ = v_isSharedCheck_892_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_idx_883_);
lean_inc(v_array_882_);
lean_dec(v_it_880_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_892_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_890_; 
v___x_887_ = lean_unsigned_to_nat(1u);
v___x_888_ = lean_nat_add(v_idx_883_, v___x_887_);
lean_dec(v_idx_883_);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 1, v___x_888_);
v___x_890_ = v___x_885_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_array_882_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v___x_888_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
}
LEAN_EXPORT uint8_t l_ByteArray_Iterator_hasPrev(lean_object* v_x_893_){
_start:
{
lean_object* v_idx_894_; lean_object* v___x_895_; uint8_t v___x_896_; 
v_idx_894_ = lean_ctor_get(v_x_893_, 1);
v___x_895_ = lean_unsigned_to_nat(0u);
v___x_896_ = lean_nat_dec_lt(v___x_895_, v_idx_894_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_hasPrev___boxed(lean_object* v_x_897_){
_start:
{
uint8_t v_res_898_; lean_object* v_r_899_; 
v_res_898_ = l_ByteArray_Iterator_hasPrev(v_x_897_);
lean_dec_ref(v_x_897_);
v_r_899_ = lean_box(v_res_898_);
return v_r_899_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_toEnd(lean_object* v_x_900_){
_start:
{
lean_object* v_array_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_909_; 
v_array_901_ = lean_ctor_get(v_x_900_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v_x_900_);
if (v_isSharedCheck_909_ == 0)
{
lean_object* v_unused_910_; 
v_unused_910_ = lean_ctor_get(v_x_900_, 1);
lean_dec(v_unused_910_);
v___x_903_ = v_x_900_;
v_isShared_904_ = v_isSharedCheck_909_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_array_901_);
lean_dec(v_x_900_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_909_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_905_; lean_object* v___x_907_; 
v___x_905_ = lean_byte_array_size(v_array_901_);
if (v_isShared_904_ == 0)
{
lean_ctor_set(v___x_903_, 1, v___x_905_);
v___x_907_ = v___x_903_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_array_901_);
lean_ctor_set(v_reuseFailAlloc_908_, 1, v___x_905_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_forward(lean_object* v_x_911_, lean_object* v_x_912_){
_start:
{
lean_object* v_array_913_; lean_object* v_idx_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_922_; 
v_array_913_ = lean_ctor_get(v_x_911_, 0);
v_idx_914_ = lean_ctor_get(v_x_911_, 1);
v_isSharedCheck_922_ = !lean_is_exclusive(v_x_911_);
if (v_isSharedCheck_922_ == 0)
{
v___x_916_ = v_x_911_;
v_isShared_917_ = v_isSharedCheck_922_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_idx_914_);
lean_inc(v_array_913_);
lean_dec(v_x_911_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_922_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_918_; lean_object* v___x_920_; 
v___x_918_ = lean_nat_add(v_idx_914_, v_x_912_);
lean_dec(v_idx_914_);
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 1, v___x_918_);
v___x_920_ = v___x_916_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_array_913_);
lean_ctor_set(v_reuseFailAlloc_921_, 1, v___x_918_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_forward___boxed(lean_object* v_x_923_, lean_object* v_x_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_ByteArray_Iterator_forward(v_x_923_, v_x_924_);
lean_dec(v_x_924_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_nextn(lean_object* v_a_926_, lean_object* v_a_927_){
_start:
{
lean_object* v_array_928_; lean_object* v_idx_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_937_; 
v_array_928_ = lean_ctor_get(v_a_926_, 0);
v_idx_929_ = lean_ctor_get(v_a_926_, 1);
v_isSharedCheck_937_ = !lean_is_exclusive(v_a_926_);
if (v_isSharedCheck_937_ == 0)
{
v___x_931_ = v_a_926_;
v_isShared_932_ = v_isSharedCheck_937_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_idx_929_);
lean_inc(v_array_928_);
lean_dec(v_a_926_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_937_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_933_; lean_object* v___x_935_; 
v___x_933_ = lean_nat_add(v_idx_929_, v_a_927_);
lean_dec(v_idx_929_);
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 1, v___x_933_);
v___x_935_ = v___x_931_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_array_928_);
lean_ctor_set(v_reuseFailAlloc_936_, 1, v___x_933_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_nextn___boxed(lean_object* v_a_938_, lean_object* v_a_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_ByteArray_Iterator_nextn(v_a_938_, v_a_939_);
lean_dec(v_a_939_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_prevn(lean_object* v_x_941_, lean_object* v_x_942_){
_start:
{
lean_object* v_array_943_; lean_object* v_idx_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_952_; 
v_array_943_ = lean_ctor_get(v_x_941_, 0);
v_idx_944_ = lean_ctor_get(v_x_941_, 1);
v_isSharedCheck_952_ = !lean_is_exclusive(v_x_941_);
if (v_isSharedCheck_952_ == 0)
{
v___x_946_ = v_x_941_;
v_isShared_947_ = v_isSharedCheck_952_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_idx_944_);
lean_inc(v_array_943_);
lean_dec(v_x_941_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_952_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_948_; lean_object* v___x_950_; 
v___x_948_ = lean_nat_sub(v_idx_944_, v_x_942_);
lean_dec(v_idx_944_);
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 1, v___x_948_);
v___x_950_ = v___x_946_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_array_943_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v___x_948_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_prevn___boxed(lean_object* v_x_953_, lean_object* v_x_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l_ByteArray_Iterator_prevn(v_x_953_, v_x_954_);
lean_dec(v_x_954_);
return v_res_955_;
}
}
lean_object* runtime_initialize_Init_Data_UInt_BasicAux(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_DecidableEq(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Attach(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_ByteArray_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_UInt_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_DecidableEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_ByteArray_instInhabited = _init_l_ByteArray_instInhabited();
lean_mark_persistent(l_ByteArray_instInhabited);
l_ByteArray_instEmptyCollection = _init_l_ByteArray_instEmptyCollection();
lean_mark_persistent(l_ByteArray_instEmptyCollection);
l_ByteArray_instInhabitedIterator_default = _init_l_ByteArray_instInhabitedIterator_default();
lean_mark_persistent(l_ByteArray_instInhabitedIterator_default);
l_ByteArray_instInhabitedIterator = _init_l_ByteArray_instInhabitedIterator();
lean_mark_persistent(l_ByteArray_instInhabitedIterator);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_ByteArray_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_ByteArray_uget___auto__1 = _init_l_ByteArray_uget___auto__1();
lean_mark_persistent(l_ByteArray_uget___auto__1);
l_ByteArray_get___auto__1 = _init_l_ByteArray_get___auto__1();
lean_mark_persistent(l_ByteArray_get___auto__1);
l_ByteArray_set___auto__1 = _init_l_ByteArray_set___auto__1();
lean_mark_persistent(l_ByteArray_set___auto__1);
l_ByteArray_uset___auto__1 = _init_l_ByteArray_uset___auto__1();
lean_mark_persistent(l_ByteArray_uset___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_UInt_BasicAux(uint8_t builtin);
lean_object* initialize_Init_Data_Array_DecidableEq(uint8_t builtin);
lean_object* initialize_Init_Data_List_Attach(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_ByteArray_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_UInt_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_DecidableEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ByteArray_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_ByteArray_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_ByteArray_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
