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
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint8_of_nat(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_sarray_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_ByteArray_instBEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ByteArray_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ByteArray_instBEq___closed__0 = (const lean_object*)&l_ByteArray_instBEq___closed__0_value;
LEAN_EXPORT const lean_object* l_ByteArray_instBEq = (const lean_object*)&l_ByteArray_instBEq___closed__0_value;
uint8_t lean_sarray_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_decEq___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_ByteArray_beq___boxed(lean_object* v_lhs_3_, lean_object* v_rhs_4_){
_start:
{
uint8_t v_res_5_; lean_object* v_r_6_; 
v_res_5_ = lean_sarray_dec_eq(v_lhs_3_, v_rhs_4_);
lean_dec_ref(v_rhs_4_);
lean_dec_ref(v_lhs_3_);
v_r_6_ = lean_box(v_res_5_);
return v_r_6_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_decEq___boxed(lean_object* v_lhs_11_, lean_object* v_rhs_12_){
_start:
{
uint8_t v_res_13_; lean_object* v_r_14_; 
v_res_13_ = lean_sarray_dec_eq(v_lhs_11_, v_rhs_12_);
lean_dec_ref(v_rhs_12_);
lean_dec_ref(v_lhs_11_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_instDecidableEq(lean_object* v_lhs_15_, lean_object* v_rhs_16_){
_start:
{
uint8_t v___x_17_; 
v___x_17_ = lean_sarray_dec_eq(v_lhs_15_, v_rhs_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_instDecidableEq___boxed(lean_object* v_lhs_18_, lean_object* v_rhs_19_){
_start:
{
uint8_t v_res_20_; lean_object* v_r_21_; 
v_res_20_ = l_ByteArray_instDecidableEq(v_lhs_18_, v_rhs_19_);
lean_dec_ref(v_rhs_19_);
lean_dec_ref(v_lhs_18_);
v_r_21_ = lean_box(v_res_20_);
return v_r_21_;
}
}
static lean_object* _init_l_ByteArray_instInhabited(void){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = l_ByteArray_empty;
return v___x_22_;
}
}
static lean_object* _init_l_ByteArray_instEmptyCollection(void){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l_ByteArray_empty;
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_usize___boxed(lean_object* v_a_25_){
_start:
{
size_t v_res_26_; lean_object* v_r_27_; 
v_res_26_ = lean_sarray_size(v_a_25_);
lean_dec_ref(v_a_25_);
v_r_27_ = lean_box_usize(v_res_26_);
return v_r_27_;
}
}
static lean_object* _init_l_ByteArray_uget___auto__1___closed__13(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = ((lean_object*)(l_ByteArray_uget___auto__1___closed__12));
v___x_53_ = l_Lean_mkAtom(v___x_52_);
return v___x_53_;
}
}
static lean_object* _init_l_ByteArray_uget___auto__1___closed__14(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_54_ = lean_obj_once(&l_ByteArray_uget___auto__1___closed__13, &l_ByteArray_uget___auto__1___closed__13_once, _init_l_ByteArray_uget___auto__1___closed__13);
v___x_55_ = ((lean_object*)(l_ByteArray_uget___auto__1___closed__5));
v___x_56_ = lean_array_push(v___x_55_, v___x_54_);
return v___x_56_;
}
}
static lean_object* _init_l_ByteArray_uget___auto__1___closed__15(void){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_57_ = lean_obj_once(&l_ByteArray_uget___auto__1___closed__14, &l_ByteArray_uget___auto__1___closed__14_once, _init_l_ByteArray_uget___auto__1___closed__14);
v___x_58_ = ((lean_object*)(l_ByteArray_uget___auto__1___closed__11));
v___x_59_ = lean_box(2);
v___x_60_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_60_, 0, v___x_59_);
lean_ctor_set(v___x_60_, 1, v___x_58_);
lean_ctor_set(v___x_60_, 2, v___x_57_);
return v___x_60_;
}
}
static lean_object* _init_l_ByteArray_uget___auto__1___closed__16(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_61_ = lean_obj_once(&l_ByteArray_uget___auto__1___closed__15, &l_ByteArray_uget___auto__1___closed__15_once, _init_l_ByteArray_uget___auto__1___closed__15);
v___x_62_ = ((lean_object*)(l_ByteArray_uget___auto__1___closed__5));
v___x_63_ = lean_array_push(v___x_62_, v___x_61_);
return v___x_63_;
}
}
static lean_object* _init_l_ByteArray_uget___auto__1___closed__17(void){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_64_ = lean_obj_once(&l_ByteArray_uget___auto__1___closed__16, &l_ByteArray_uget___auto__1___closed__16_once, _init_l_ByteArray_uget___auto__1___closed__16);
v___x_65_ = ((lean_object*)(l_ByteArray_uget___auto__1___closed__9));
v___x_66_ = lean_box(2);
v___x_67_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_67_, 0, v___x_66_);
lean_ctor_set(v___x_67_, 1, v___x_65_);
lean_ctor_set(v___x_67_, 2, v___x_64_);
return v___x_67_;
}
}
static lean_object* _init_l_ByteArray_uget___auto__1___closed__18(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_68_ = lean_obj_once(&l_ByteArray_uget___auto__1___closed__17, &l_ByteArray_uget___auto__1___closed__17_once, _init_l_ByteArray_uget___auto__1___closed__17);
v___x_69_ = ((lean_object*)(l_ByteArray_uget___auto__1___closed__5));
v___x_70_ = lean_array_push(v___x_69_, v___x_68_);
return v___x_70_;
}
}
static lean_object* _init_l_ByteArray_uget___auto__1___closed__19(void){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_71_ = lean_obj_once(&l_ByteArray_uget___auto__1___closed__18, &l_ByteArray_uget___auto__1___closed__18_once, _init_l_ByteArray_uget___auto__1___closed__18);
v___x_72_ = ((lean_object*)(l_ByteArray_uget___auto__1___closed__7));
v___x_73_ = lean_box(2);
v___x_74_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_74_, 0, v___x_73_);
lean_ctor_set(v___x_74_, 1, v___x_72_);
lean_ctor_set(v___x_74_, 2, v___x_71_);
return v___x_74_;
}
}
static lean_object* _init_l_ByteArray_uget___auto__1___closed__20(void){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_75_ = lean_obj_once(&l_ByteArray_uget___auto__1___closed__19, &l_ByteArray_uget___auto__1___closed__19_once, _init_l_ByteArray_uget___auto__1___closed__19);
v___x_76_ = ((lean_object*)(l_ByteArray_uget___auto__1___closed__5));
v___x_77_ = lean_array_push(v___x_76_, v___x_75_);
return v___x_77_;
}
}
static lean_object* _init_l_ByteArray_uget___auto__1___closed__21(void){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_78_ = lean_obj_once(&l_ByteArray_uget___auto__1___closed__20, &l_ByteArray_uget___auto__1___closed__20_once, _init_l_ByteArray_uget___auto__1___closed__20);
v___x_79_ = ((lean_object*)(l_ByteArray_uget___auto__1___closed__4));
v___x_80_ = lean_box(2);
v___x_81_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
lean_ctor_set(v___x_81_, 1, v___x_79_);
lean_ctor_set(v___x_81_, 2, v___x_78_);
return v___x_81_;
}
}
static lean_object* _init_l_ByteArray_uget___auto__1(void){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = lean_obj_once(&l_ByteArray_uget___auto__1___closed__21, &l_ByteArray_uget___auto__1___closed__21_once, _init_l_ByteArray_uget___auto__1___closed__21);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_uget___boxed(lean_object* v_a_86_, lean_object* v_i_87_, lean_object* v_h_88_){
_start:
{
size_t v_i_boxed_89_; uint8_t v_res_90_; lean_object* v_r_91_; 
v_i_boxed_89_ = lean_unbox_usize(v_i_87_);
lean_dec(v_i_87_);
v_res_90_ = lean_byte_array_uget(v_a_86_, v_i_boxed_89_);
lean_dec_ref(v_a_86_);
v_r_91_ = lean_box(v_res_90_);
return v_r_91_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_get_x21___boxed(lean_object* v_a_00___x40___internal___hyg_94_, lean_object* v_a_00___x40___internal___hyg_95_){
_start:
{
uint8_t v_res_96_; lean_object* v_r_97_; 
v_res_96_ = lean_byte_array_get(v_a_00___x40___internal___hyg_94_, v_a_00___x40___internal___hyg_95_);
lean_dec(v_a_00___x40___internal___hyg_95_);
lean_dec_ref(v_a_00___x40___internal___hyg_94_);
v_r_97_ = lean_box(v_res_96_);
return v_r_97_;
}
}
static lean_object* _init_l_ByteArray_get___auto__1(void){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = lean_obj_once(&l_ByteArray_uget___auto__1___closed__21, &l_ByteArray_uget___auto__1___closed__21_once, _init_l_ByteArray_uget___auto__1___closed__21);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_get___boxed(lean_object* v_a_102_, lean_object* v_i_103_, lean_object* v_h_104_){
_start:
{
uint8_t v_res_105_; lean_object* v_r_106_; 
v_res_105_ = lean_byte_array_fget(v_a_102_, v_i_103_);
lean_dec(v_i_103_);
lean_dec_ref(v_a_102_);
v_r_106_ = lean_box(v_res_105_);
return v_r_106_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_instGetElemNatUInt8LtSize___lam__0(lean_object* v_xs_107_, lean_object* v_i_108_, lean_object* v_h_109_){
_start:
{
uint8_t v___x_110_; 
v___x_110_ = lean_byte_array_fget(v_xs_107_, v_i_108_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_instGetElemNatUInt8LtSize___lam__0___boxed(lean_object* v_xs_111_, lean_object* v_i_112_, lean_object* v_h_113_){
_start:
{
uint8_t v_res_114_; lean_object* v_r_115_; 
v_res_114_ = l_ByteArray_instGetElemNatUInt8LtSize___lam__0(v_xs_111_, v_i_112_, v_h_113_);
lean_dec(v_i_112_);
lean_dec_ref(v_xs_111_);
v_r_115_ = lean_box(v_res_114_);
return v_r_115_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_instGetElemUSizeUInt8LtNatValToFinSize___lam__0(lean_object* v_xs_118_, size_t v_i_119_, lean_object* v_h_120_){
_start:
{
uint8_t v___x_121_; 
v___x_121_ = lean_byte_array_uget(v_xs_118_, v_i_119_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_instGetElemUSizeUInt8LtNatValToFinSize___lam__0___boxed(lean_object* v_xs_122_, lean_object* v_i_123_, lean_object* v_h_124_){
_start:
{
size_t v_i_boxed_125_; uint8_t v_res_126_; lean_object* v_r_127_; 
v_i_boxed_125_ = lean_unbox_usize(v_i_123_);
lean_dec(v_i_123_);
v_res_126_ = l_ByteArray_instGetElemUSizeUInt8LtNatValToFinSize___lam__0(v_xs_122_, v_i_boxed_125_, v_h_124_);
lean_dec_ref(v_xs_122_);
v_r_127_ = lean_box(v_res_126_);
return v_r_127_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_set_x21___boxed(lean_object* v_a_00___x40___internal___hyg_133_, lean_object* v_a_00___x40___internal___hyg_134_, lean_object* v_a_00___x40___internal___hyg_135_){
_start:
{
uint8_t v_a_00___x40___internal___hyg_3__boxed_136_; lean_object* v_res_137_; 
v_a_00___x40___internal___hyg_3__boxed_136_ = lean_unbox(v_a_00___x40___internal___hyg_135_);
v_res_137_ = lean_byte_array_set(v_a_00___x40___internal___hyg_133_, v_a_00___x40___internal___hyg_134_, v_a_00___x40___internal___hyg_3__boxed_136_);
lean_dec(v_a_00___x40___internal___hyg_134_);
return v_res_137_;
}
}
static lean_object* _init_l_ByteArray_set___auto__1(void){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = lean_obj_once(&l_ByteArray_uget___auto__1___closed__21, &l_ByteArray_uget___auto__1___closed__21_once, _init_l_ByteArray_uget___auto__1___closed__21);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_set___boxed(lean_object* v_a_143_, lean_object* v_i_144_, lean_object* v_a_00___x40___internal___hyg_145_, lean_object* v_h_146_){
_start:
{
uint8_t v_a_00___x40___internal___hyg_1__boxed_147_; lean_object* v_res_148_; 
v_a_00___x40___internal___hyg_1__boxed_147_ = lean_unbox(v_a_00___x40___internal___hyg_145_);
v_res_148_ = lean_byte_array_fset(v_a_143_, v_i_144_, v_a_00___x40___internal___hyg_1__boxed_147_);
lean_dec(v_i_144_);
return v_res_148_;
}
}
static lean_object* _init_l_ByteArray_uset___auto__1(void){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = lean_obj_once(&l_ByteArray_uget___auto__1___closed__21, &l_ByteArray_uget___auto__1___closed__21_once, _init_l_ByteArray_uget___auto__1___closed__21);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_uset___boxed(lean_object* v_a_154_, lean_object* v_i_155_, lean_object* v_a_00___x40___internal___hyg_156_, lean_object* v_h_157_){
_start:
{
size_t v_i_boxed_158_; uint8_t v_a_00___x40___internal___hyg_1__boxed_159_; lean_object* v_res_160_; 
v_i_boxed_158_ = lean_unbox_usize(v_i_155_);
lean_dec(v_i_155_);
v_a_00___x40___internal___hyg_1__boxed_159_ = lean_unbox(v_a_00___x40___internal___hyg_156_);
v_res_160_ = lean_byte_array_uset(v_a_154_, v_i_boxed_158_, v_a_00___x40___internal___hyg_1__boxed_159_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_hash___boxed(lean_object* v_a_162_){
_start:
{
uint64_t v_res_163_; lean_object* v_r_164_; 
v_res_163_ = lean_byte_array_hash(v_a_162_);
lean_dec_ref(v_a_162_);
v_r_164_ = lean_box_uint64(v_res_163_);
return v_r_164_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_isEmpty(lean_object* v_s_167_){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; uint8_t v___x_170_; 
v___x_168_ = lean_byte_array_size(v_s_167_);
v___x_169_ = lean_unsigned_to_nat(0u);
v___x_170_ = lean_nat_dec_eq(v___x_168_, v___x_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_isEmpty___boxed(lean_object* v_s_171_){
_start:
{
uint8_t v_res_172_; lean_object* v_r_173_; 
v_res_172_ = l_ByteArray_isEmpty(v_s_171_);
lean_dec_ref(v_s_171_);
v_r_173_ = lean_box(v_res_172_);
return v_r_173_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_copySlice___boxed(lean_object* v_src_180_, lean_object* v_srcOff_181_, lean_object* v_dest_182_, lean_object* v_destOff_183_, lean_object* v_len_184_, lean_object* v_exact_185_){
_start:
{
uint8_t v_exact_boxed_186_; lean_object* v_res_187_; 
v_exact_boxed_186_ = lean_unbox(v_exact_185_);
v_res_187_ = lean_byte_array_copy_slice(v_src_180_, v_srcOff_181_, v_dest_182_, v_destOff_183_, v_len_184_, v_exact_boxed_186_);
lean_dec_ref(v_src_180_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_extract(lean_object* v_a_188_, lean_object* v_b_189_, lean_object* v_e_190_){
_start:
{
lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; uint8_t v___x_194_; lean_object* v___x_195_; 
v___x_191_ = l_ByteArray_empty;
v___x_192_ = lean_unsigned_to_nat(0u);
v___x_193_ = lean_nat_sub(v_e_190_, v_b_189_);
v___x_194_ = 1;
v___x_195_ = lean_byte_array_copy_slice(v_a_188_, v_b_189_, v___x_191_, v___x_192_, v___x_193_, v___x_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_extract___boxed(lean_object* v_a_196_, lean_object* v_b_197_, lean_object* v_e_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_ByteArray_extract(v_a_196_, v_b_197_, v_e_198_);
lean_dec(v_e_198_);
lean_dec_ref(v_a_196_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_fastAppend(lean_object* v_a_200_, lean_object* v_b_201_){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; uint8_t v___x_205_; lean_object* v___x_206_; 
v___x_202_ = lean_unsigned_to_nat(0u);
v___x_203_ = lean_byte_array_size(v_a_200_);
v___x_204_ = lean_byte_array_size(v_b_201_);
v___x_205_ = 0;
v___x_206_ = lean_byte_array_copy_slice(v_b_201_, v___x_202_, v_a_200_, v___x_203_, v___x_204_, v___x_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_fastAppend___boxed(lean_object* v_a_207_, lean_object* v_b_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_ByteArray_fastAppend(v_a_207_, v_b_208_);
lean_dec_ref(v_b_208_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_toList_loop(lean_object* v_bs_212_, lean_object* v_i_213_, lean_object* v_r_214_){
_start:
{
lean_object* v___x_215_; uint8_t v___x_216_; 
v___x_215_ = lean_byte_array_size(v_bs_212_);
v___x_216_ = lean_nat_dec_lt(v_i_213_, v___x_215_);
if (v___x_216_ == 0)
{
lean_object* v___x_217_; 
lean_dec(v_i_213_);
v___x_217_ = l_List_reverse___redArg(v_r_214_);
return v___x_217_;
}
else
{
lean_object* v___x_218_; lean_object* v___x_219_; uint8_t v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_218_ = lean_unsigned_to_nat(1u);
v___x_219_ = lean_nat_add(v_i_213_, v___x_218_);
v___x_220_ = lean_byte_array_get(v_bs_212_, v_i_213_);
lean_dec(v_i_213_);
v___x_221_ = lean_box(v___x_220_);
v___x_222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
lean_ctor_set(v___x_222_, 1, v_r_214_);
v_i_213_ = v___x_219_;
v_r_214_ = v___x_222_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_toList_loop___boxed(lean_object* v_bs_224_, lean_object* v_i_225_, lean_object* v_r_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_ByteArray_toList_loop(v_bs_224_, v_i_225_, v_r_226_);
lean_dec_ref(v_bs_224_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_toList(lean_object* v_bs_228_){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_229_ = lean_unsigned_to_nat(0u);
v___x_230_ = lean_box(0);
v___x_231_ = l_ByteArray_toList_loop(v_bs_228_, v___x_229_, v___x_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_toList___boxed(lean_object* v_bs_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_ByteArray_toList(v_bs_232_);
lean_dec_ref(v_bs_232_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findFinIdx_x3f_loop(lean_object* v_a_234_, lean_object* v_p_235_, lean_object* v_i_236_){
_start:
{
lean_object* v___x_237_; uint8_t v___x_238_; 
v___x_237_ = lean_byte_array_size(v_a_234_);
v___x_238_ = lean_nat_dec_lt(v_i_236_, v___x_237_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; 
lean_dec(v_i_236_);
lean_dec_ref(v_p_235_);
v___x_239_ = lean_box(0);
return v___x_239_;
}
else
{
uint8_t v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; uint8_t v___x_243_; 
v___x_240_ = lean_byte_array_fget(v_a_234_, v_i_236_);
v___x_241_ = lean_box(v___x_240_);
lean_inc_ref(v_p_235_);
v___x_242_ = lean_apply_1(v_p_235_, v___x_241_);
v___x_243_ = lean_unbox(v___x_242_);
if (v___x_243_ == 0)
{
lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_244_ = lean_unsigned_to_nat(1u);
v___x_245_ = lean_nat_add(v_i_236_, v___x_244_);
lean_dec(v_i_236_);
v_i_236_ = v___x_245_;
goto _start;
}
else
{
lean_object* v___x_247_; 
lean_dec_ref(v_p_235_);
v___x_247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_247_, 0, v_i_236_);
return v___x_247_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_findFinIdx_x3f_loop___boxed(lean_object* v_a_248_, lean_object* v_p_249_, lean_object* v_i_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_ByteArray_findFinIdx_x3f_loop(v_a_248_, v_p_249_, v_i_250_);
lean_dec_ref(v_a_248_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findFinIdx_x3f(lean_object* v_a_252_, lean_object* v_p_253_, lean_object* v_start_254_){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = l_ByteArray_findFinIdx_x3f_loop(v_a_252_, v_p_253_, v_start_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findFinIdx_x3f___boxed(lean_object* v_a_256_, lean_object* v_p_257_, lean_object* v_start_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_ByteArray_findFinIdx_x3f(v_a_256_, v_p_257_, v_start_258_);
lean_dec_ref(v_a_256_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop(lean_object* v_a_260_, lean_object* v_p_261_, lean_object* v_i_262_){
_start:
{
lean_object* v___x_263_; uint8_t v___x_264_; 
v___x_263_ = lean_byte_array_size(v_a_260_);
v___x_264_ = lean_nat_dec_lt(v_i_262_, v___x_263_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; 
lean_dec(v_i_262_);
lean_dec_ref(v_p_261_);
v___x_265_ = lean_box(0);
return v___x_265_;
}
else
{
uint8_t v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; uint8_t v___x_269_; 
v___x_266_ = lean_byte_array_fget(v_a_260_, v_i_262_);
v___x_267_ = lean_box(v___x_266_);
lean_inc_ref(v_p_261_);
v___x_268_ = lean_apply_1(v_p_261_, v___x_267_);
v___x_269_ = lean_unbox(v___x_268_);
if (v___x_269_ == 0)
{
lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_270_ = lean_unsigned_to_nat(1u);
v___x_271_ = lean_nat_add(v_i_262_, v___x_270_);
lean_dec(v_i_262_);
v_i_262_ = v___x_271_;
goto _start;
}
else
{
lean_object* v___x_273_; 
lean_dec_ref(v_p_261_);
v___x_273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_273_, 0, v_i_262_);
return v___x_273_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___boxed(lean_object* v_a_274_, lean_object* v_p_275_, lean_object* v_i_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_ByteArray_findIdx_x3f_loop(v_a_274_, v_p_275_, v_i_276_);
lean_dec_ref(v_a_274_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f(lean_object* v_a_278_, lean_object* v_p_279_, lean_object* v_start_280_){
_start:
{
lean_object* v___x_281_; 
v___x_281_ = l_ByteArray_findIdx_x3f_loop(v_a_278_, v_p_279_, v_start_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f___boxed(lean_object* v_a_282_, lean_object* v_p_283_, lean_object* v_start_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_ByteArray_findIdx_x3f(v_a_282_, v_p_283_, v_start_284_);
lean_dec_ref(v_a_282_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe_loop___redArg___lam__0___boxed(lean_object* v_toApplicative_286_, lean_object* v_i_287_, lean_object* v_inst_288_, lean_object* v_as_289_, lean_object* v_f_290_, lean_object* v_sz_291_, lean_object* v_____do__lift_292_){
_start:
{
size_t v_i_boxed_293_; size_t v_sz_boxed_294_; lean_object* v_res_295_; 
v_i_boxed_293_ = lean_unbox_usize(v_i_287_);
lean_dec(v_i_287_);
v_sz_boxed_294_ = lean_unbox_usize(v_sz_291_);
lean_dec(v_sz_291_);
v_res_295_ = l_ByteArray_forInUnsafe_loop___redArg___lam__0(v_toApplicative_286_, v_i_boxed_293_, v_inst_288_, v_as_289_, v_f_290_, v_sz_boxed_294_, v_____do__lift_292_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe_loop___redArg(lean_object* v_inst_296_, lean_object* v_as_297_, lean_object* v_f_298_, size_t v_sz_299_, size_t v_i_300_, lean_object* v_b_301_){
_start:
{
uint8_t v___x_302_; 
v___x_302_ = lean_usize_dec_lt(v_i_300_, v_sz_299_);
if (v___x_302_ == 0)
{
lean_object* v_toApplicative_303_; lean_object* v_toPure_304_; lean_object* v___x_305_; 
lean_dec(v_f_298_);
lean_dec_ref(v_as_297_);
v_toApplicative_303_ = lean_ctor_get(v_inst_296_, 0);
lean_inc_ref(v_toApplicative_303_);
lean_dec_ref(v_inst_296_);
v_toPure_304_ = lean_ctor_get(v_toApplicative_303_, 1);
lean_inc(v_toPure_304_);
lean_dec_ref(v_toApplicative_303_);
v___x_305_ = lean_apply_2(v_toPure_304_, lean_box(0), v_b_301_);
return v___x_305_;
}
else
{
lean_object* v_toApplicative_306_; lean_object* v_toBind_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___f_310_; uint8_t v_a_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v_toApplicative_306_ = lean_ctor_get(v_inst_296_, 0);
lean_inc_ref(v_toApplicative_306_);
v_toBind_307_ = lean_ctor_get(v_inst_296_, 1);
lean_inc(v_toBind_307_);
v___x_308_ = lean_box_usize(v_i_300_);
v___x_309_ = lean_box_usize(v_sz_299_);
lean_inc(v_f_298_);
lean_inc_ref(v_as_297_);
v___f_310_ = lean_alloc_closure((void*)(l_ByteArray_forInUnsafe_loop___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_310_, 0, v_toApplicative_306_);
lean_closure_set(v___f_310_, 1, v___x_308_);
lean_closure_set(v___f_310_, 2, v_inst_296_);
lean_closure_set(v___f_310_, 3, v_as_297_);
lean_closure_set(v___f_310_, 4, v_f_298_);
lean_closure_set(v___f_310_, 5, v___x_309_);
v_a_311_ = lean_byte_array_uget(v_as_297_, v_i_300_);
lean_dec_ref(v_as_297_);
v___x_312_ = lean_box(v_a_311_);
v___x_313_ = lean_apply_2(v_f_298_, v___x_312_, v_b_301_);
v___x_314_ = lean_apply_4(v_toBind_307_, lean_box(0), lean_box(0), v___x_313_, v___f_310_);
return v___x_314_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe_loop___redArg___lam__0(lean_object* v_toApplicative_315_, size_t v_i_316_, lean_object* v_inst_317_, lean_object* v_as_318_, lean_object* v_f_319_, size_t v_sz_320_, lean_object* v_____do__lift_321_){
_start:
{
if (lean_obj_tag(v_____do__lift_321_) == 0)
{
lean_object* v_a_322_; lean_object* v_toPure_323_; lean_object* v___x_324_; 
lean_dec(v_f_319_);
lean_dec_ref(v_as_318_);
lean_dec_ref(v_inst_317_);
v_a_322_ = lean_ctor_get(v_____do__lift_321_, 0);
lean_inc(v_a_322_);
lean_dec_ref(v_____do__lift_321_);
v_toPure_323_ = lean_ctor_get(v_toApplicative_315_, 1);
lean_inc(v_toPure_323_);
lean_dec_ref(v_toApplicative_315_);
v___x_324_ = lean_apply_2(v_toPure_323_, lean_box(0), v_a_322_);
return v___x_324_;
}
else
{
lean_object* v_a_325_; size_t v___x_326_; size_t v___x_327_; lean_object* v___x_328_; 
lean_dec_ref(v_toApplicative_315_);
v_a_325_ = lean_ctor_get(v_____do__lift_321_, 0);
lean_inc(v_a_325_);
lean_dec_ref(v_____do__lift_321_);
v___x_326_ = ((size_t)1ULL);
v___x_327_ = lean_usize_add(v_i_316_, v___x_326_);
v___x_328_ = l_ByteArray_forInUnsafe_loop___redArg(v_inst_317_, v_as_318_, v_f_319_, v_sz_320_, v___x_327_, v_a_325_);
return v___x_328_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe_loop___redArg___boxed(lean_object* v_inst_329_, lean_object* v_as_330_, lean_object* v_f_331_, lean_object* v_sz_332_, lean_object* v_i_333_, lean_object* v_b_334_){
_start:
{
size_t v_sz_boxed_335_; size_t v_i_boxed_336_; lean_object* v_res_337_; 
v_sz_boxed_335_ = lean_unbox_usize(v_sz_332_);
lean_dec(v_sz_332_);
v_i_boxed_336_ = lean_unbox_usize(v_i_333_);
lean_dec(v_i_333_);
v_res_337_ = l_ByteArray_forInUnsafe_loop___redArg(v_inst_329_, v_as_330_, v_f_331_, v_sz_boxed_335_, v_i_boxed_336_, v_b_334_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe_loop(lean_object* v_00_u03b2_338_, lean_object* v_m_339_, lean_object* v_inst_340_, lean_object* v_as_341_, lean_object* v_f_342_, size_t v_sz_343_, size_t v_i_344_, lean_object* v_b_345_){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = l_ByteArray_forInUnsafe_loop___redArg(v_inst_340_, v_as_341_, v_f_342_, v_sz_343_, v_i_344_, v_b_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe_loop___boxed(lean_object* v_00_u03b2_347_, lean_object* v_m_348_, lean_object* v_inst_349_, lean_object* v_as_350_, lean_object* v_f_351_, lean_object* v_sz_352_, lean_object* v_i_353_, lean_object* v_b_354_){
_start:
{
size_t v_sz_boxed_355_; size_t v_i_boxed_356_; lean_object* v_res_357_; 
v_sz_boxed_355_ = lean_unbox_usize(v_sz_352_);
lean_dec(v_sz_352_);
v_i_boxed_356_ = lean_unbox_usize(v_i_353_);
lean_dec(v_i_353_);
v_res_357_ = l_ByteArray_forInUnsafe_loop(v_00_u03b2_347_, v_m_348_, v_inst_349_, v_as_350_, v_f_351_, v_sz_boxed_355_, v_i_boxed_356_, v_b_354_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe___redArg(lean_object* v_inst_358_, lean_object* v_as_359_, lean_object* v_b_360_, lean_object* v_f_361_){
_start:
{
size_t v_sz_362_; size_t v___x_363_; lean_object* v___x_364_; 
v_sz_362_ = lean_sarray_size(v_as_359_);
v___x_363_ = ((size_t)0ULL);
v___x_364_ = l_ByteArray_forInUnsafe_loop___redArg(v_inst_358_, v_as_359_, v_f_361_, v_sz_362_, v___x_363_, v_b_360_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe(lean_object* v_00_u03b2_365_, lean_object* v_m_366_, lean_object* v_inst_367_, lean_object* v_as_368_, lean_object* v_b_369_, lean_object* v_f_370_){
_start:
{
size_t v_sz_371_; size_t v___x_372_; lean_object* v___x_373_; 
v_sz_371_ = lean_sarray_size(v_as_368_);
v___x_372_ = ((size_t)0ULL);
v___x_373_ = l_ByteArray_forInUnsafe_loop___redArg(v_inst_367_, v_as_368_, v_f_370_, v_sz_371_, v___x_372_, v_b_369_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_forIn_loop___redArg___lam__0___boxed(lean_object* v_toPure_374_, lean_object* v_inst_375_, lean_object* v_as_376_, lean_object* v_f_377_, lean_object* v_n_378_, lean_object* v_____do__lift_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_ByteArray_forIn_loop___redArg___lam__0(v_toPure_374_, v_inst_375_, v_as_376_, v_f_377_, v_n_378_, v_____do__lift_379_);
lean_dec(v_n_378_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_forIn_loop___redArg(lean_object* v_inst_381_, lean_object* v_as_382_, lean_object* v_f_383_, lean_object* v_i_384_, lean_object* v_b_385_){
_start:
{
lean_object* v_toApplicative_386_; lean_object* v_toBind_387_; lean_object* v_toPure_388_; lean_object* v_zero_389_; uint8_t v_isZero_390_; 
v_toApplicative_386_ = lean_ctor_get(v_inst_381_, 0);
v_toBind_387_ = lean_ctor_get(v_inst_381_, 1);
lean_inc(v_toBind_387_);
v_toPure_388_ = lean_ctor_get(v_toApplicative_386_, 1);
lean_inc(v_toPure_388_);
v_zero_389_ = lean_unsigned_to_nat(0u);
v_isZero_390_ = lean_nat_dec_eq(v_i_384_, v_zero_389_);
if (v_isZero_390_ == 1)
{
lean_object* v___x_391_; 
lean_dec(v_toBind_387_);
lean_dec(v_f_383_);
lean_dec_ref(v_as_382_);
lean_dec_ref(v_inst_381_);
v___x_391_ = lean_apply_2(v_toPure_388_, lean_box(0), v_b_385_);
return v___x_391_;
}
else
{
lean_object* v_one_392_; lean_object* v_n_393_; lean_object* v___f_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; uint8_t v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v_one_392_ = lean_unsigned_to_nat(1u);
v_n_393_ = lean_nat_sub(v_i_384_, v_one_392_);
lean_inc(v_n_393_);
lean_inc(v_f_383_);
lean_inc_ref(v_as_382_);
v___f_394_ = lean_alloc_closure((void*)(l_ByteArray_forIn_loop___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_394_, 0, v_toPure_388_);
lean_closure_set(v___f_394_, 1, v_inst_381_);
lean_closure_set(v___f_394_, 2, v_as_382_);
lean_closure_set(v___f_394_, 3, v_f_383_);
lean_closure_set(v___f_394_, 4, v_n_393_);
v___x_395_ = lean_byte_array_size(v_as_382_);
v___x_396_ = lean_nat_sub(v___x_395_, v_one_392_);
v___x_397_ = lean_nat_sub(v___x_396_, v_n_393_);
lean_dec(v_n_393_);
lean_dec(v___x_396_);
v___x_398_ = lean_byte_array_fget(v_as_382_, v___x_397_);
lean_dec(v___x_397_);
lean_dec_ref(v_as_382_);
v___x_399_ = lean_box(v___x_398_);
v___x_400_ = lean_apply_2(v_f_383_, v___x_399_, v_b_385_);
v___x_401_ = lean_apply_4(v_toBind_387_, lean_box(0), lean_box(0), v___x_400_, v___f_394_);
return v___x_401_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_forIn_loop___redArg___lam__0(lean_object* v_toPure_402_, lean_object* v_inst_403_, lean_object* v_as_404_, lean_object* v_f_405_, lean_object* v_n_406_, lean_object* v_____do__lift_407_){
_start:
{
if (lean_obj_tag(v_____do__lift_407_) == 0)
{
lean_object* v_a_408_; lean_object* v___x_409_; 
lean_dec(v_f_405_);
lean_dec_ref(v_as_404_);
lean_dec_ref(v_inst_403_);
v_a_408_ = lean_ctor_get(v_____do__lift_407_, 0);
lean_inc(v_a_408_);
lean_dec_ref(v_____do__lift_407_);
v___x_409_ = lean_apply_2(v_toPure_402_, lean_box(0), v_a_408_);
return v___x_409_;
}
else
{
lean_object* v_a_410_; lean_object* v___x_411_; 
lean_dec(v_toPure_402_);
v_a_410_ = lean_ctor_get(v_____do__lift_407_, 0);
lean_inc(v_a_410_);
lean_dec_ref(v_____do__lift_407_);
v___x_411_ = l_ByteArray_forIn_loop___redArg(v_inst_403_, v_as_404_, v_f_405_, v_n_406_, v_a_410_);
return v___x_411_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_forIn_loop___redArg___boxed(lean_object* v_inst_412_, lean_object* v_as_413_, lean_object* v_f_414_, lean_object* v_i_415_, lean_object* v_b_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_ByteArray_forIn_loop___redArg(v_inst_412_, v_as_413_, v_f_414_, v_i_415_, v_b_416_);
lean_dec(v_i_415_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_forIn_loop(lean_object* v_00_u03b2_418_, lean_object* v_m_419_, lean_object* v_inst_420_, lean_object* v_as_421_, lean_object* v_f_422_, lean_object* v_i_423_, lean_object* v_h_424_, lean_object* v_b_425_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l_ByteArray_forIn_loop___redArg(v_inst_420_, v_as_421_, v_f_422_, v_i_423_, v_b_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_forIn_loop___boxed(lean_object* v_00_u03b2_427_, lean_object* v_m_428_, lean_object* v_inst_429_, lean_object* v_as_430_, lean_object* v_f_431_, lean_object* v_i_432_, lean_object* v_h_433_, lean_object* v_b_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_ByteArray_forIn_loop(v_00_u03b2_427_, v_m_428_, v_inst_429_, v_as_430_, v_f_431_, v_i_432_, v_h_433_, v_b_434_);
lean_dec(v_i_432_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_instForInUInt8OfMonad___redArg___lam__0(lean_object* v_inst_436_, lean_object* v_00_u03b2_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
size_t v_sz_441_; size_t v___x_442_; lean_object* v___x_443_; 
v_sz_441_ = lean_sarray_size(v___y_438_);
v___x_442_ = ((size_t)0ULL);
v___x_443_ = l_ByteArray_forInUnsafe_loop___redArg(v_inst_436_, v___y_438_, v___y_440_, v_sz_441_, v___x_442_, v___y_439_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_instForInUInt8OfMonad___redArg(lean_object* v_inst_444_){
_start:
{
lean_object* v___f_445_; 
v___f_445_ = lean_alloc_closure((void*)(l_ByteArray_instForInUInt8OfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_445_, 0, v_inst_444_);
return v___f_445_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_instForInUInt8OfMonad(lean_object* v_m_446_, lean_object* v_inst_447_){
_start:
{
lean_object* v___f_448_; 
v___f_448_ = lean_alloc_closure((void*)(l_ByteArray_instForInUInt8OfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_448_, 0, v_inst_447_);
return v___f_448_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___redArg___lam__0___boxed(lean_object* v_i_449_, lean_object* v_inst_450_, lean_object* v_f_451_, lean_object* v_as_452_, lean_object* v_stop_453_, lean_object* v_____do__lift_454_){
_start:
{
size_t v_i_boxed_455_; size_t v_stop_boxed_456_; lean_object* v_res_457_; 
v_i_boxed_455_ = lean_unbox_usize(v_i_449_);
lean_dec(v_i_449_);
v_stop_boxed_456_ = lean_unbox_usize(v_stop_453_);
lean_dec(v_stop_453_);
v_res_457_ = l_ByteArray_foldlMUnsafe_fold___redArg___lam__0(v_i_boxed_455_, v_inst_450_, v_f_451_, v_as_452_, v_stop_boxed_456_, v_____do__lift_454_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___redArg(lean_object* v_inst_458_, lean_object* v_f_459_, lean_object* v_as_460_, size_t v_i_461_, size_t v_stop_462_, lean_object* v_b_463_){
_start:
{
uint8_t v___x_464_; 
v___x_464_ = lean_usize_dec_eq(v_i_461_, v_stop_462_);
if (v___x_464_ == 0)
{
lean_object* v_toBind_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___f_468_; uint8_t v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v_toBind_465_ = lean_ctor_get(v_inst_458_, 1);
lean_inc(v_toBind_465_);
v___x_466_ = lean_box_usize(v_i_461_);
v___x_467_ = lean_box_usize(v_stop_462_);
lean_inc_ref(v_as_460_);
lean_inc(v_f_459_);
v___f_468_ = lean_alloc_closure((void*)(l_ByteArray_foldlMUnsafe_fold___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_468_, 0, v___x_466_);
lean_closure_set(v___f_468_, 1, v_inst_458_);
lean_closure_set(v___f_468_, 2, v_f_459_);
lean_closure_set(v___f_468_, 3, v_as_460_);
lean_closure_set(v___f_468_, 4, v___x_467_);
v___x_469_ = lean_byte_array_uget(v_as_460_, v_i_461_);
lean_dec_ref(v_as_460_);
v___x_470_ = lean_box(v___x_469_);
v___x_471_ = lean_apply_2(v_f_459_, v_b_463_, v___x_470_);
v___x_472_ = lean_apply_4(v_toBind_465_, lean_box(0), lean_box(0), v___x_471_, v___f_468_);
return v___x_472_;
}
else
{
lean_object* v_toApplicative_473_; lean_object* v_toPure_474_; lean_object* v___x_475_; 
lean_dec_ref(v_as_460_);
lean_dec(v_f_459_);
v_toApplicative_473_ = lean_ctor_get(v_inst_458_, 0);
lean_inc_ref(v_toApplicative_473_);
lean_dec_ref(v_inst_458_);
v_toPure_474_ = lean_ctor_get(v_toApplicative_473_, 1);
lean_inc(v_toPure_474_);
lean_dec_ref(v_toApplicative_473_);
v___x_475_ = lean_apply_2(v_toPure_474_, lean_box(0), v_b_463_);
return v___x_475_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___redArg___lam__0(size_t v_i_476_, lean_object* v_inst_477_, lean_object* v_f_478_, lean_object* v_as_479_, size_t v_stop_480_, lean_object* v_____do__lift_481_){
_start:
{
size_t v___x_482_; size_t v___x_483_; lean_object* v___x_484_; 
v___x_482_ = ((size_t)1ULL);
v___x_483_ = lean_usize_add(v_i_476_, v___x_482_);
v___x_484_ = l_ByteArray_foldlMUnsafe_fold___redArg(v_inst_477_, v_f_478_, v_as_479_, v___x_483_, v_stop_480_, v_____do__lift_481_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___redArg___boxed(lean_object* v_inst_485_, lean_object* v_f_486_, lean_object* v_as_487_, lean_object* v_i_488_, lean_object* v_stop_489_, lean_object* v_b_490_){
_start:
{
size_t v_i_boxed_491_; size_t v_stop_boxed_492_; lean_object* v_res_493_; 
v_i_boxed_491_ = lean_unbox_usize(v_i_488_);
lean_dec(v_i_488_);
v_stop_boxed_492_ = lean_unbox_usize(v_stop_489_);
lean_dec(v_stop_489_);
v_res_493_ = l_ByteArray_foldlMUnsafe_fold___redArg(v_inst_485_, v_f_486_, v_as_487_, v_i_boxed_491_, v_stop_boxed_492_, v_b_490_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold(lean_object* v_00_u03b2_494_, lean_object* v_m_495_, lean_object* v_inst_496_, lean_object* v_f_497_, lean_object* v_as_498_, size_t v_i_499_, size_t v_stop_500_, lean_object* v_b_501_){
_start:
{
lean_object* v___x_502_; 
v___x_502_ = l_ByteArray_foldlMUnsafe_fold___redArg(v_inst_496_, v_f_497_, v_as_498_, v_i_499_, v_stop_500_, v_b_501_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___boxed(lean_object* v_00_u03b2_503_, lean_object* v_m_504_, lean_object* v_inst_505_, lean_object* v_f_506_, lean_object* v_as_507_, lean_object* v_i_508_, lean_object* v_stop_509_, lean_object* v_b_510_){
_start:
{
size_t v_i_boxed_511_; size_t v_stop_boxed_512_; lean_object* v_res_513_; 
v_i_boxed_511_ = lean_unbox_usize(v_i_508_);
lean_dec(v_i_508_);
v_stop_boxed_512_ = lean_unbox_usize(v_stop_509_);
lean_dec(v_stop_509_);
v_res_513_ = l_ByteArray_foldlMUnsafe_fold(v_00_u03b2_503_, v_m_504_, v_inst_505_, v_f_506_, v_as_507_, v_i_boxed_511_, v_stop_boxed_512_, v_b_510_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe___redArg(lean_object* v_inst_514_, lean_object* v_f_515_, lean_object* v_init_516_, lean_object* v_as_517_, lean_object* v_start_518_, lean_object* v_stop_519_){
_start:
{
uint8_t v___x_520_; 
v___x_520_ = lean_nat_dec_lt(v_start_518_, v_stop_519_);
if (v___x_520_ == 0)
{
lean_object* v_toApplicative_521_; lean_object* v_toPure_522_; lean_object* v___x_523_; 
lean_dec_ref(v_as_517_);
lean_dec(v_f_515_);
v_toApplicative_521_ = lean_ctor_get(v_inst_514_, 0);
lean_inc_ref(v_toApplicative_521_);
lean_dec_ref(v_inst_514_);
v_toPure_522_ = lean_ctor_get(v_toApplicative_521_, 1);
lean_inc(v_toPure_522_);
lean_dec_ref(v_toApplicative_521_);
v___x_523_ = lean_apply_2(v_toPure_522_, lean_box(0), v_init_516_);
return v___x_523_;
}
else
{
lean_object* v___x_524_; uint8_t v___x_525_; 
v___x_524_ = lean_byte_array_size(v_as_517_);
v___x_525_ = lean_nat_dec_le(v_stop_519_, v___x_524_);
if (v___x_525_ == 0)
{
uint8_t v___x_526_; 
v___x_526_ = lean_nat_dec_lt(v_start_518_, v___x_524_);
if (v___x_526_ == 0)
{
lean_object* v_toApplicative_527_; lean_object* v_toPure_528_; lean_object* v___x_529_; 
lean_dec_ref(v_as_517_);
lean_dec(v_f_515_);
v_toApplicative_527_ = lean_ctor_get(v_inst_514_, 0);
lean_inc_ref(v_toApplicative_527_);
lean_dec_ref(v_inst_514_);
v_toPure_528_ = lean_ctor_get(v_toApplicative_527_, 1);
lean_inc(v_toPure_528_);
lean_dec_ref(v_toApplicative_527_);
v___x_529_ = lean_apply_2(v_toPure_528_, lean_box(0), v_init_516_);
return v___x_529_;
}
else
{
size_t v___x_530_; size_t v___x_531_; lean_object* v___x_532_; 
v___x_530_ = lean_usize_of_nat(v_start_518_);
v___x_531_ = lean_usize_of_nat(v___x_524_);
v___x_532_ = l_ByteArray_foldlMUnsafe_fold___redArg(v_inst_514_, v_f_515_, v_as_517_, v___x_530_, v___x_531_, v_init_516_);
return v___x_532_;
}
}
else
{
size_t v___x_533_; size_t v___x_534_; lean_object* v___x_535_; 
v___x_533_ = lean_usize_of_nat(v_start_518_);
v___x_534_ = lean_usize_of_nat(v_stop_519_);
v___x_535_ = l_ByteArray_foldlMUnsafe_fold___redArg(v_inst_514_, v_f_515_, v_as_517_, v___x_533_, v___x_534_, v_init_516_);
return v___x_535_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe___redArg___boxed(lean_object* v_inst_536_, lean_object* v_f_537_, lean_object* v_init_538_, lean_object* v_as_539_, lean_object* v_start_540_, lean_object* v_stop_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_ByteArray_foldlMUnsafe___redArg(v_inst_536_, v_f_537_, v_init_538_, v_as_539_, v_start_540_, v_stop_541_);
lean_dec(v_stop_541_);
lean_dec(v_start_540_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe(lean_object* v_00_u03b2_543_, lean_object* v_m_544_, lean_object* v_inst_545_, lean_object* v_f_546_, lean_object* v_init_547_, lean_object* v_as_548_, lean_object* v_start_549_, lean_object* v_stop_550_){
_start:
{
uint8_t v___x_551_; 
v___x_551_ = lean_nat_dec_lt(v_start_549_, v_stop_550_);
if (v___x_551_ == 0)
{
lean_object* v_toApplicative_552_; lean_object* v_toPure_553_; lean_object* v___x_554_; 
lean_dec_ref(v_as_548_);
lean_dec(v_f_546_);
v_toApplicative_552_ = lean_ctor_get(v_inst_545_, 0);
lean_inc_ref(v_toApplicative_552_);
lean_dec_ref(v_inst_545_);
v_toPure_553_ = lean_ctor_get(v_toApplicative_552_, 1);
lean_inc(v_toPure_553_);
lean_dec_ref(v_toApplicative_552_);
v___x_554_ = lean_apply_2(v_toPure_553_, lean_box(0), v_init_547_);
return v___x_554_;
}
else
{
lean_object* v___x_555_; uint8_t v___x_556_; 
v___x_555_ = lean_byte_array_size(v_as_548_);
v___x_556_ = lean_nat_dec_le(v_stop_550_, v___x_555_);
if (v___x_556_ == 0)
{
uint8_t v___x_557_; 
v___x_557_ = lean_nat_dec_lt(v_start_549_, v___x_555_);
if (v___x_557_ == 0)
{
lean_object* v_toApplicative_558_; lean_object* v_toPure_559_; lean_object* v___x_560_; 
lean_dec_ref(v_as_548_);
lean_dec(v_f_546_);
v_toApplicative_558_ = lean_ctor_get(v_inst_545_, 0);
lean_inc_ref(v_toApplicative_558_);
lean_dec_ref(v_inst_545_);
v_toPure_559_ = lean_ctor_get(v_toApplicative_558_, 1);
lean_inc(v_toPure_559_);
lean_dec_ref(v_toApplicative_558_);
v___x_560_ = lean_apply_2(v_toPure_559_, lean_box(0), v_init_547_);
return v___x_560_;
}
else
{
size_t v___x_561_; size_t v___x_562_; lean_object* v___x_563_; 
v___x_561_ = lean_usize_of_nat(v_start_549_);
v___x_562_ = lean_usize_of_nat(v___x_555_);
v___x_563_ = l_ByteArray_foldlMUnsafe_fold___redArg(v_inst_545_, v_f_546_, v_as_548_, v___x_561_, v___x_562_, v_init_547_);
return v___x_563_;
}
}
else
{
size_t v___x_564_; size_t v___x_565_; lean_object* v___x_566_; 
v___x_564_ = lean_usize_of_nat(v_start_549_);
v___x_565_ = lean_usize_of_nat(v_stop_550_);
v___x_566_ = l_ByteArray_foldlMUnsafe_fold___redArg(v_inst_545_, v_f_546_, v_as_548_, v___x_564_, v___x_565_, v_init_547_);
return v___x_566_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe___boxed(lean_object* v_00_u03b2_567_, lean_object* v_m_568_, lean_object* v_inst_569_, lean_object* v_f_570_, lean_object* v_init_571_, lean_object* v_as_572_, lean_object* v_start_573_, lean_object* v_stop_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_ByteArray_foldlMUnsafe(v_00_u03b2_567_, v_m_568_, v_inst_569_, v_f_570_, v_init_571_, v_as_572_, v_start_573_, v_stop_574_);
lean_dec(v_stop_574_);
lean_dec(v_start_573_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlM_loop___redArg___lam__0___boxed(lean_object* v_j_576_, lean_object* v_inst_577_, lean_object* v_f_578_, lean_object* v_as_579_, lean_object* v_stop_580_, lean_object* v_n_581_, lean_object* v_____do__lift_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_ByteArray_foldlM_loop___redArg___lam__0(v_j_576_, v_inst_577_, v_f_578_, v_as_579_, v_stop_580_, v_n_581_, v_____do__lift_582_);
lean_dec(v_n_581_);
lean_dec(v_j_576_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlM_loop___redArg(lean_object* v_inst_584_, lean_object* v_f_585_, lean_object* v_as_586_, lean_object* v_stop_587_, lean_object* v_i_588_, lean_object* v_j_589_, lean_object* v_b_590_){
_start:
{
uint8_t v___x_591_; 
v___x_591_ = lean_nat_dec_lt(v_j_589_, v_stop_587_);
if (v___x_591_ == 0)
{
lean_object* v_toApplicative_592_; lean_object* v_toPure_593_; lean_object* v___x_594_; 
lean_dec(v_j_589_);
lean_dec(v_stop_587_);
lean_dec_ref(v_as_586_);
lean_dec(v_f_585_);
v_toApplicative_592_ = lean_ctor_get(v_inst_584_, 0);
lean_inc_ref(v_toApplicative_592_);
lean_dec_ref(v_inst_584_);
v_toPure_593_ = lean_ctor_get(v_toApplicative_592_, 1);
lean_inc(v_toPure_593_);
lean_dec_ref(v_toApplicative_592_);
v___x_594_ = lean_apply_2(v_toPure_593_, lean_box(0), v_b_590_);
return v___x_594_;
}
else
{
lean_object* v_zero_595_; uint8_t v_isZero_596_; 
v_zero_595_ = lean_unsigned_to_nat(0u);
v_isZero_596_ = lean_nat_dec_eq(v_i_588_, v_zero_595_);
if (v_isZero_596_ == 1)
{
lean_object* v_toApplicative_597_; lean_object* v_toPure_598_; lean_object* v___x_599_; 
lean_dec(v_j_589_);
lean_dec(v_stop_587_);
lean_dec_ref(v_as_586_);
lean_dec(v_f_585_);
v_toApplicative_597_ = lean_ctor_get(v_inst_584_, 0);
lean_inc_ref(v_toApplicative_597_);
lean_dec_ref(v_inst_584_);
v_toPure_598_ = lean_ctor_get(v_toApplicative_597_, 1);
lean_inc(v_toPure_598_);
lean_dec_ref(v_toApplicative_597_);
v___x_599_ = lean_apply_2(v_toPure_598_, lean_box(0), v_b_590_);
return v___x_599_;
}
else
{
lean_object* v_toBind_600_; lean_object* v_one_601_; lean_object* v_n_602_; lean_object* v___f_603_; uint8_t v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v_toBind_600_ = lean_ctor_get(v_inst_584_, 1);
lean_inc(v_toBind_600_);
v_one_601_ = lean_unsigned_to_nat(1u);
v_n_602_ = lean_nat_sub(v_i_588_, v_one_601_);
lean_inc_ref(v_as_586_);
lean_inc(v_f_585_);
lean_inc(v_j_589_);
v___f_603_ = lean_alloc_closure((void*)(l_ByteArray_foldlM_loop___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_603_, 0, v_j_589_);
lean_closure_set(v___f_603_, 1, v_inst_584_);
lean_closure_set(v___f_603_, 2, v_f_585_);
lean_closure_set(v___f_603_, 3, v_as_586_);
lean_closure_set(v___f_603_, 4, v_stop_587_);
lean_closure_set(v___f_603_, 5, v_n_602_);
v___x_604_ = lean_byte_array_fget(v_as_586_, v_j_589_);
lean_dec(v_j_589_);
lean_dec_ref(v_as_586_);
v___x_605_ = lean_box(v___x_604_);
v___x_606_ = lean_apply_2(v_f_585_, v_b_590_, v___x_605_);
v___x_607_ = lean_apply_4(v_toBind_600_, lean_box(0), lean_box(0), v___x_606_, v___f_603_);
return v___x_607_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlM_loop___redArg___lam__0(lean_object* v_j_608_, lean_object* v_inst_609_, lean_object* v_f_610_, lean_object* v_as_611_, lean_object* v_stop_612_, lean_object* v_n_613_, lean_object* v_____do__lift_614_){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_615_ = lean_unsigned_to_nat(1u);
v___x_616_ = lean_nat_add(v_j_608_, v___x_615_);
v___x_617_ = l_ByteArray_foldlM_loop___redArg(v_inst_609_, v_f_610_, v_as_611_, v_stop_612_, v_n_613_, v___x_616_, v_____do__lift_614_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlM_loop___redArg___boxed(lean_object* v_inst_618_, lean_object* v_f_619_, lean_object* v_as_620_, lean_object* v_stop_621_, lean_object* v_i_622_, lean_object* v_j_623_, lean_object* v_b_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_ByteArray_foldlM_loop___redArg(v_inst_618_, v_f_619_, v_as_620_, v_stop_621_, v_i_622_, v_j_623_, v_b_624_);
lean_dec(v_i_622_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlM_loop(lean_object* v_00_u03b2_626_, lean_object* v_m_627_, lean_object* v_inst_628_, lean_object* v_f_629_, lean_object* v_as_630_, lean_object* v_stop_631_, lean_object* v_h_632_, lean_object* v_i_633_, lean_object* v_j_634_, lean_object* v_b_635_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = l_ByteArray_foldlM_loop___redArg(v_inst_628_, v_f_629_, v_as_630_, v_stop_631_, v_i_633_, v_j_634_, v_b_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlM_loop___boxed(lean_object* v_00_u03b2_637_, lean_object* v_m_638_, lean_object* v_inst_639_, lean_object* v_f_640_, lean_object* v_as_641_, lean_object* v_stop_642_, lean_object* v_h_643_, lean_object* v_i_644_, lean_object* v_j_645_, lean_object* v_b_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_ByteArray_foldlM_loop(v_00_u03b2_637_, v_m_638_, v_inst_639_, v_f_640_, v_as_641_, v_stop_642_, v_h_643_, v_i_644_, v_j_645_, v_b_646_);
lean_dec(v_i_644_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldl___redArg___lam__0(lean_object* v_f_648_, lean_object* v_x1_649_, uint8_t v_x2_650_){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_651_ = lean_box(v_x2_650_);
v___x_652_ = lean_apply_2(v_f_648_, v_x1_649_, v___x_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldl___redArg___lam__0___boxed(lean_object* v_f_653_, lean_object* v_x1_654_, lean_object* v_x2_655_){
_start:
{
uint8_t v_x2_190__boxed_656_; lean_object* v_res_657_; 
v_x2_190__boxed_656_ = lean_unbox(v_x2_655_);
v_res_657_ = l_ByteArray_foldl___redArg___lam__0(v_f_653_, v_x1_654_, v_x2_190__boxed_656_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldl___redArg(lean_object* v_f_677_, lean_object* v_init_678_, lean_object* v_as_679_, lean_object* v_start_680_, lean_object* v_stop_681_){
_start:
{
lean_object* v___x_682_; uint8_t v___x_683_; 
v___x_682_ = ((lean_object*)(l_ByteArray_foldl___redArg___closed__9));
v___x_683_ = lean_nat_dec_lt(v_start_680_, v_stop_681_);
if (v___x_683_ == 0)
{
lean_dec_ref(v_as_679_);
lean_dec(v_f_677_);
return v_init_678_;
}
else
{
lean_object* v___f_684_; lean_object* v___x_685_; uint8_t v___x_686_; 
v___f_684_ = lean_alloc_closure((void*)(l_ByteArray_foldl___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_684_, 0, v_f_677_);
v___x_685_ = lean_byte_array_size(v_as_679_);
v___x_686_ = lean_nat_dec_le(v_stop_681_, v___x_685_);
if (v___x_686_ == 0)
{
uint8_t v___x_687_; 
v___x_687_ = lean_nat_dec_lt(v_start_680_, v___x_685_);
if (v___x_687_ == 0)
{
lean_dec_ref(v___f_684_);
lean_dec_ref(v_as_679_);
return v_init_678_;
}
else
{
size_t v___x_688_; size_t v___x_689_; lean_object* v___x_690_; 
v___x_688_ = lean_usize_of_nat(v_start_680_);
v___x_689_ = lean_usize_of_nat(v___x_685_);
v___x_690_ = l_ByteArray_foldlMUnsafe_fold___redArg(v___x_682_, v___f_684_, v_as_679_, v___x_688_, v___x_689_, v_init_678_);
return v___x_690_;
}
}
else
{
size_t v___x_691_; size_t v___x_692_; lean_object* v___x_693_; 
v___x_691_ = lean_usize_of_nat(v_start_680_);
v___x_692_ = lean_usize_of_nat(v_stop_681_);
v___x_693_ = l_ByteArray_foldlMUnsafe_fold___redArg(v___x_682_, v___f_684_, v_as_679_, v___x_691_, v___x_692_, v_init_678_);
return v___x_693_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldl___redArg___boxed(lean_object* v_f_694_, lean_object* v_init_695_, lean_object* v_as_696_, lean_object* v_start_697_, lean_object* v_stop_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_ByteArray_foldl___redArg(v_f_694_, v_init_695_, v_as_696_, v_start_697_, v_stop_698_);
lean_dec(v_stop_698_);
lean_dec(v_start_697_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldl(lean_object* v_00_u03b2_700_, lean_object* v_f_701_, lean_object* v_init_702_, lean_object* v_as_703_, lean_object* v_start_704_, lean_object* v_stop_705_){
_start:
{
lean_object* v___x_706_; uint8_t v___x_707_; 
v___x_706_ = ((lean_object*)(l_ByteArray_foldl___redArg___closed__9));
v___x_707_ = lean_nat_dec_lt(v_start_704_, v_stop_705_);
if (v___x_707_ == 0)
{
lean_dec_ref(v_as_703_);
lean_dec(v_f_701_);
return v_init_702_;
}
else
{
lean_object* v___f_708_; lean_object* v___x_709_; uint8_t v___x_710_; 
v___f_708_ = lean_alloc_closure((void*)(l_ByteArray_foldl___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_708_, 0, v_f_701_);
v___x_709_ = lean_byte_array_size(v_as_703_);
v___x_710_ = lean_nat_dec_le(v_stop_705_, v___x_709_);
if (v___x_710_ == 0)
{
uint8_t v___x_711_; 
v___x_711_ = lean_nat_dec_lt(v_start_704_, v___x_709_);
if (v___x_711_ == 0)
{
lean_dec_ref(v___f_708_);
lean_dec_ref(v_as_703_);
return v_init_702_;
}
else
{
size_t v___x_712_; size_t v___x_713_; lean_object* v___x_714_; 
v___x_712_ = lean_usize_of_nat(v_start_704_);
v___x_713_ = lean_usize_of_nat(v___x_709_);
v___x_714_ = l_ByteArray_foldlMUnsafe_fold___redArg(v___x_706_, v___f_708_, v_as_703_, v___x_712_, v___x_713_, v_init_702_);
return v___x_714_;
}
}
else
{
size_t v___x_715_; size_t v___x_716_; lean_object* v___x_717_; 
v___x_715_ = lean_usize_of_nat(v_start_704_);
v___x_716_ = lean_usize_of_nat(v_stop_705_);
v___x_717_ = l_ByteArray_foldlMUnsafe_fold___redArg(v___x_706_, v___f_708_, v_as_703_, v___x_715_, v___x_716_, v_init_702_);
return v___x_717_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldl___boxed(lean_object* v_00_u03b2_718_, lean_object* v_f_719_, lean_object* v_init_720_, lean_object* v_as_721_, lean_object* v_start_722_, lean_object* v_stop_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_ByteArray_foldl(v_00_u03b2_718_, v_f_719_, v_init_720_, v_as_721_, v_start_722_, v_stop_723_);
lean_dec(v_stop_723_);
lean_dec(v_start_722_);
return v_res_724_;
}
}
static lean_object* _init_l_ByteArray_instInhabitedIterator_default___closed__0(void){
_start:
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_725_ = lean_unsigned_to_nat(0u);
v___x_726_ = l_ByteArray_empty;
v___x_727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
lean_ctor_set(v___x_727_, 1, v___x_725_);
return v___x_727_;
}
}
static lean_object* _init_l_ByteArray_instInhabitedIterator_default(void){
_start:
{
lean_object* v___x_728_; 
v___x_728_ = lean_obj_once(&l_ByteArray_instInhabitedIterator_default___closed__0, &l_ByteArray_instInhabitedIterator_default___closed__0_once, _init_l_ByteArray_instInhabitedIterator_default___closed__0);
return v___x_728_;
}
}
static lean_object* _init_l_ByteArray_instInhabitedIterator(void){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = l_ByteArray_instInhabitedIterator_default;
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_mkIterator(lean_object* v_arr_730_){
_start:
{
lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_731_ = lean_unsigned_to_nat(0u);
v___x_732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_732_, 0, v_arr_730_);
lean_ctor_set(v___x_732_, 1, v___x_731_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_iter(lean_object* v_arr_733_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = l_ByteArray_mkIterator(v_arr_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_instSizeOfIterator___lam__0(lean_object* v_i_735_){
_start:
{
lean_object* v_array_736_; lean_object* v_idx_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v_array_736_ = lean_ctor_get(v_i_735_, 0);
v_idx_737_ = lean_ctor_get(v_i_735_, 1);
v___x_738_ = lean_byte_array_size(v_array_736_);
v___x_739_ = lean_nat_sub(v___x_738_, v_idx_737_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_instSizeOfIterator___lam__0___boxed(lean_object* v_i_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_ByteArray_instSizeOfIterator___lam__0(v_i_740_);
lean_dec_ref(v_i_740_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_remainingBytes(lean_object* v_x_744_){
_start:
{
lean_object* v_array_745_; lean_object* v_idx_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v_array_745_ = lean_ctor_get(v_x_744_, 0);
v_idx_746_ = lean_ctor_get(v_x_744_, 1);
v___x_747_ = lean_byte_array_size(v_array_745_);
v___x_748_ = lean_nat_sub(v___x_747_, v_idx_746_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_remainingBytes___boxed(lean_object* v_x_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_ByteArray_Iterator_remainingBytes(v_x_749_);
lean_dec_ref(v_x_749_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_pos(lean_object* v_self_751_){
_start:
{
lean_object* v_idx_752_; 
v_idx_752_ = lean_ctor_get(v_self_751_, 1);
lean_inc(v_idx_752_);
return v_idx_752_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_pos___boxed(lean_object* v_self_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l_ByteArray_Iterator_pos(v_self_753_);
lean_dec_ref(v_self_753_);
return v_res_754_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_Iterator_atEnd(lean_object* v_x_755_){
_start:
{
lean_object* v_array_756_; lean_object* v_idx_757_; lean_object* v___x_758_; uint8_t v___x_759_; 
v_array_756_ = lean_ctor_get(v_x_755_, 0);
v_idx_757_ = lean_ctor_get(v_x_755_, 1);
v___x_758_ = lean_byte_array_size(v_array_756_);
v___x_759_ = lean_nat_dec_le(v___x_758_, v_idx_757_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_atEnd___boxed(lean_object* v_x_760_){
_start:
{
uint8_t v_res_761_; lean_object* v_r_762_; 
v_res_761_ = l_ByteArray_Iterator_atEnd(v_x_760_);
lean_dec_ref(v_x_760_);
v_r_762_ = lean_box(v_res_761_);
return v_r_762_;
}
}
static uint8_t _init_l_ByteArray_Iterator_curr___closed__0(void){
_start:
{
lean_object* v___x_763_; uint8_t v___x_764_; 
v___x_763_ = lean_unsigned_to_nat(0u);
v___x_764_ = lean_uint8_of_nat(v___x_763_);
return v___x_764_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_Iterator_curr(lean_object* v_x_765_){
_start:
{
lean_object* v_array_766_; lean_object* v_idx_767_; lean_object* v___x_768_; uint8_t v___x_769_; 
v_array_766_ = lean_ctor_get(v_x_765_, 0);
v_idx_767_ = lean_ctor_get(v_x_765_, 1);
v___x_768_ = lean_byte_array_size(v_array_766_);
v___x_769_ = lean_nat_dec_lt(v_idx_767_, v___x_768_);
if (v___x_769_ == 0)
{
uint8_t v___x_770_; 
v___x_770_ = lean_uint8_once(&l_ByteArray_Iterator_curr___closed__0, &l_ByteArray_Iterator_curr___closed__0_once, _init_l_ByteArray_Iterator_curr___closed__0);
return v___x_770_;
}
else
{
uint8_t v___x_771_; 
v___x_771_ = lean_byte_array_fget(v_array_766_, v_idx_767_);
return v___x_771_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_curr___boxed(lean_object* v_x_772_){
_start:
{
uint8_t v_res_773_; lean_object* v_r_774_; 
v_res_773_ = l_ByteArray_Iterator_curr(v_x_772_);
lean_dec_ref(v_x_772_);
v_r_774_ = lean_box(v_res_773_);
return v_r_774_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_next(lean_object* v_x_775_){
_start:
{
lean_object* v_array_776_; lean_object* v_idx_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_786_; 
v_array_776_ = lean_ctor_get(v_x_775_, 0);
v_idx_777_ = lean_ctor_get(v_x_775_, 1);
v_isSharedCheck_786_ = !lean_is_exclusive(v_x_775_);
if (v_isSharedCheck_786_ == 0)
{
v___x_779_ = v_x_775_;
v_isShared_780_ = v_isSharedCheck_786_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_idx_777_);
lean_inc(v_array_776_);
lean_dec(v_x_775_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_786_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_784_; 
v___x_781_ = lean_unsigned_to_nat(1u);
v___x_782_ = lean_nat_add(v_idx_777_, v___x_781_);
lean_dec(v_idx_777_);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 1, v___x_782_);
v___x_784_ = v___x_779_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_array_776_);
lean_ctor_set(v_reuseFailAlloc_785_, 1, v___x_782_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_prev(lean_object* v_x_787_){
_start:
{
lean_object* v_array_788_; lean_object* v_idx_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_798_; 
v_array_788_ = lean_ctor_get(v_x_787_, 0);
v_idx_789_ = lean_ctor_get(v_x_787_, 1);
v_isSharedCheck_798_ = !lean_is_exclusive(v_x_787_);
if (v_isSharedCheck_798_ == 0)
{
v___x_791_ = v_x_787_;
v_isShared_792_ = v_isSharedCheck_798_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_idx_789_);
lean_inc(v_array_788_);
lean_dec(v_x_787_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_798_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_796_; 
v___x_793_ = lean_unsigned_to_nat(1u);
v___x_794_ = lean_nat_sub(v_idx_789_, v___x_793_);
lean_dec(v_idx_789_);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 1, v___x_794_);
v___x_796_ = v___x_791_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_array_788_);
lean_ctor_set(v_reuseFailAlloc_797_, 1, v___x_794_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
}
LEAN_EXPORT uint8_t l_ByteArray_Iterator_hasNext(lean_object* v_x_799_){
_start:
{
lean_object* v_array_800_; lean_object* v_idx_801_; lean_object* v___x_802_; uint8_t v___x_803_; 
v_array_800_ = lean_ctor_get(v_x_799_, 0);
v_idx_801_ = lean_ctor_get(v_x_799_, 1);
v___x_802_ = lean_byte_array_size(v_array_800_);
v___x_803_ = lean_nat_dec_lt(v_idx_801_, v___x_802_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_hasNext___boxed(lean_object* v_x_804_){
_start:
{
uint8_t v_res_805_; lean_object* v_r_806_; 
v_res_805_ = l_ByteArray_Iterator_hasNext(v_x_804_);
lean_dec_ref(v_x_804_);
v_r_806_ = lean_box(v_res_805_);
return v_r_806_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Basic_0__ByteArray_Iterator_remainingBytes_match__1_splitter___redArg(lean_object* v_x_807_, lean_object* v_h__1_808_){
_start:
{
lean_object* v_array_809_; lean_object* v_idx_810_; lean_object* v___x_811_; 
v_array_809_ = lean_ctor_get(v_x_807_, 0);
lean_inc_ref(v_array_809_);
v_idx_810_ = lean_ctor_get(v_x_807_, 1);
lean_inc(v_idx_810_);
lean_dec_ref(v_x_807_);
v___x_811_ = lean_apply_2(v_h__1_808_, v_array_809_, v_idx_810_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Basic_0__ByteArray_Iterator_remainingBytes_match__1_splitter(lean_object* v_motive_812_, lean_object* v_x_813_, lean_object* v_h__1_814_){
_start:
{
lean_object* v_array_815_; lean_object* v_idx_816_; lean_object* v___x_817_; 
v_array_815_ = lean_ctor_get(v_x_813_, 0);
lean_inc_ref(v_array_815_);
v_idx_816_ = lean_ctor_get(v_x_813_, 1);
lean_inc(v_idx_816_);
lean_dec_ref(v_x_813_);
v___x_817_ = lean_apply_2(v_h__1_814_, v_array_815_, v_idx_816_);
return v___x_817_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_Iterator_curr_x27___redArg(lean_object* v_it_818_){
_start:
{
lean_object* v_array_819_; lean_object* v_idx_820_; uint8_t v___x_821_; 
v_array_819_ = lean_ctor_get(v_it_818_, 0);
v_idx_820_ = lean_ctor_get(v_it_818_, 1);
v___x_821_ = lean_byte_array_fget(v_array_819_, v_idx_820_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_curr_x27___redArg___boxed(lean_object* v_it_822_){
_start:
{
uint8_t v_res_823_; lean_object* v_r_824_; 
v_res_823_ = l_ByteArray_Iterator_curr_x27___redArg(v_it_822_);
lean_dec_ref(v_it_822_);
v_r_824_ = lean_box(v_res_823_);
return v_r_824_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_Iterator_curr_x27(lean_object* v_it_825_, lean_object* v_h_826_){
_start:
{
lean_object* v_array_827_; lean_object* v_idx_828_; uint8_t v___x_829_; 
v_array_827_ = lean_ctor_get(v_it_825_, 0);
v_idx_828_ = lean_ctor_get(v_it_825_, 1);
v___x_829_ = lean_byte_array_fget(v_array_827_, v_idx_828_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_curr_x27___boxed(lean_object* v_it_830_, lean_object* v_h_831_){
_start:
{
uint8_t v_res_832_; lean_object* v_r_833_; 
v_res_832_ = l_ByteArray_Iterator_curr_x27(v_it_830_, v_h_831_);
lean_dec_ref(v_it_830_);
v_r_833_ = lean_box(v_res_832_);
return v_r_833_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_next_x27___redArg(lean_object* v_it_834_){
_start:
{
lean_object* v_array_835_; lean_object* v_idx_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_845_; 
v_array_835_ = lean_ctor_get(v_it_834_, 0);
v_idx_836_ = lean_ctor_get(v_it_834_, 1);
v_isSharedCheck_845_ = !lean_is_exclusive(v_it_834_);
if (v_isSharedCheck_845_ == 0)
{
v___x_838_ = v_it_834_;
v_isShared_839_ = v_isSharedCheck_845_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_idx_836_);
lean_inc(v_array_835_);
lean_dec(v_it_834_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_845_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_843_; 
v___x_840_ = lean_unsigned_to_nat(1u);
v___x_841_ = lean_nat_add(v_idx_836_, v___x_840_);
lean_dec(v_idx_836_);
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 1, v___x_841_);
v___x_843_ = v___x_838_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_array_835_);
lean_ctor_set(v_reuseFailAlloc_844_, 1, v___x_841_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_next_x27(lean_object* v_it_846_, lean_object* v___h_847_){
_start:
{
lean_object* v_array_848_; lean_object* v_idx_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_858_; 
v_array_848_ = lean_ctor_get(v_it_846_, 0);
v_idx_849_ = lean_ctor_get(v_it_846_, 1);
v_isSharedCheck_858_ = !lean_is_exclusive(v_it_846_);
if (v_isSharedCheck_858_ == 0)
{
v___x_851_ = v_it_846_;
v_isShared_852_ = v_isSharedCheck_858_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_idx_849_);
lean_inc(v_array_848_);
lean_dec(v_it_846_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_858_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_856_; 
v___x_853_ = lean_unsigned_to_nat(1u);
v___x_854_ = lean_nat_add(v_idx_849_, v___x_853_);
lean_dec(v_idx_849_);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 1, v___x_854_);
v___x_856_ = v___x_851_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_array_848_);
lean_ctor_set(v_reuseFailAlloc_857_, 1, v___x_854_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
}
LEAN_EXPORT uint8_t l_ByteArray_Iterator_hasPrev(lean_object* v_x_859_){
_start:
{
lean_object* v_idx_860_; lean_object* v___x_861_; uint8_t v___x_862_; 
v_idx_860_ = lean_ctor_get(v_x_859_, 1);
v___x_861_ = lean_unsigned_to_nat(0u);
v___x_862_ = lean_nat_dec_lt(v___x_861_, v_idx_860_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_hasPrev___boxed(lean_object* v_x_863_){
_start:
{
uint8_t v_res_864_; lean_object* v_r_865_; 
v_res_864_ = l_ByteArray_Iterator_hasPrev(v_x_863_);
lean_dec_ref(v_x_863_);
v_r_865_ = lean_box(v_res_864_);
return v_r_865_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_toEnd(lean_object* v_x_866_){
_start:
{
lean_object* v_array_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_875_; 
v_array_867_ = lean_ctor_get(v_x_866_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v_x_866_);
if (v_isSharedCheck_875_ == 0)
{
lean_object* v_unused_876_; 
v_unused_876_ = lean_ctor_get(v_x_866_, 1);
lean_dec(v_unused_876_);
v___x_869_ = v_x_866_;
v_isShared_870_ = v_isSharedCheck_875_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_array_867_);
lean_dec(v_x_866_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_875_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_871_; lean_object* v___x_873_; 
v___x_871_ = lean_byte_array_size(v_array_867_);
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 1, v___x_871_);
v___x_873_ = v___x_869_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_array_867_);
lean_ctor_set(v_reuseFailAlloc_874_, 1, v___x_871_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_forward(lean_object* v_x_877_, lean_object* v_x_878_){
_start:
{
lean_object* v_array_879_; lean_object* v_idx_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_888_; 
v_array_879_ = lean_ctor_get(v_x_877_, 0);
v_idx_880_ = lean_ctor_get(v_x_877_, 1);
v_isSharedCheck_888_ = !lean_is_exclusive(v_x_877_);
if (v_isSharedCheck_888_ == 0)
{
v___x_882_ = v_x_877_;
v_isShared_883_ = v_isSharedCheck_888_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_idx_880_);
lean_inc(v_array_879_);
lean_dec(v_x_877_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_888_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_884_; lean_object* v___x_886_; 
v___x_884_ = lean_nat_add(v_idx_880_, v_x_878_);
lean_dec(v_idx_880_);
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 1, v___x_884_);
v___x_886_ = v___x_882_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_array_879_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v___x_884_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_forward___boxed(lean_object* v_x_889_, lean_object* v_x_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_ByteArray_Iterator_forward(v_x_889_, v_x_890_);
lean_dec(v_x_890_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_nextn(lean_object* v_a_892_, lean_object* v_a_893_){
_start:
{
lean_object* v_array_894_; lean_object* v_idx_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_903_; 
v_array_894_ = lean_ctor_get(v_a_892_, 0);
v_idx_895_ = lean_ctor_get(v_a_892_, 1);
v_isSharedCheck_903_ = !lean_is_exclusive(v_a_892_);
if (v_isSharedCheck_903_ == 0)
{
v___x_897_ = v_a_892_;
v_isShared_898_ = v_isSharedCheck_903_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_idx_895_);
lean_inc(v_array_894_);
lean_dec(v_a_892_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_903_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_899_; lean_object* v___x_901_; 
v___x_899_ = lean_nat_add(v_idx_895_, v_a_893_);
lean_dec(v_idx_895_);
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 1, v___x_899_);
v___x_901_ = v___x_897_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_array_894_);
lean_ctor_set(v_reuseFailAlloc_902_, 1, v___x_899_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_nextn___boxed(lean_object* v_a_904_, lean_object* v_a_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_ByteArray_Iterator_nextn(v_a_904_, v_a_905_);
lean_dec(v_a_905_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_prevn(lean_object* v_x_907_, lean_object* v_x_908_){
_start:
{
lean_object* v_array_909_; lean_object* v_idx_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_918_; 
v_array_909_ = lean_ctor_get(v_x_907_, 0);
v_idx_910_ = lean_ctor_get(v_x_907_, 1);
v_isSharedCheck_918_ = !lean_is_exclusive(v_x_907_);
if (v_isSharedCheck_918_ == 0)
{
v___x_912_ = v_x_907_;
v_isShared_913_ = v_isSharedCheck_918_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_idx_910_);
lean_inc(v_array_909_);
lean_dec(v_x_907_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_918_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_914_; lean_object* v___x_916_; 
v___x_914_ = lean_nat_sub(v_idx_910_, v_x_908_);
lean_dec(v_idx_910_);
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 1, v___x_914_);
v___x_916_ = v___x_912_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_array_909_);
lean_ctor_set(v_reuseFailAlloc_917_, 1, v___x_914_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_prevn___boxed(lean_object* v_x_919_, lean_object* v_x_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_ByteArray_Iterator_prevn(v_x_919_, v_x_920_);
lean_dec(v_x_920_);
return v_res_921_;
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
