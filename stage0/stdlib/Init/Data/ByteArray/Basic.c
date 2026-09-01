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
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe_loop___redArg___lam__0___boxed(lean_object* v_toPure_286_, lean_object* v_i_287_, lean_object* v_inst_288_, lean_object* v_as_289_, lean_object* v_f_290_, lean_object* v_sz_291_, lean_object* v_____do__lift_292_){
_start:
{
size_t v_i_boxed_293_; size_t v_sz_boxed_294_; lean_object* v_res_295_; 
v_i_boxed_293_ = lean_unbox_usize(v_i_287_);
lean_dec(v_i_287_);
v_sz_boxed_294_ = lean_unbox_usize(v_sz_291_);
lean_dec(v_sz_291_);
v_res_295_ = l_ByteArray_forInUnsafe_loop___redArg___lam__0(v_toPure_286_, v_i_boxed_293_, v_inst_288_, v_as_289_, v_f_290_, v_sz_boxed_294_, v_____do__lift_292_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe_loop___redArg(lean_object* v_inst_296_, lean_object* v_as_297_, lean_object* v_f_298_, size_t v_sz_299_, size_t v_i_300_, lean_object* v_b_301_){
_start:
{
lean_object* v_toApplicative_302_; lean_object* v_toBind_303_; lean_object* v_toPure_304_; uint8_t v___x_305_; 
v_toApplicative_302_ = lean_ctor_get(v_inst_296_, 0);
v_toBind_303_ = lean_ctor_get(v_inst_296_, 1);
lean_inc(v_toBind_303_);
v_toPure_304_ = lean_ctor_get(v_toApplicative_302_, 1);
lean_inc(v_toPure_304_);
v___x_305_ = lean_usize_dec_lt(v_i_300_, v_sz_299_);
if (v___x_305_ == 0)
{
lean_object* v___x_306_; 
lean_dec(v_toBind_303_);
lean_dec(v_f_298_);
lean_dec_ref(v_as_297_);
lean_dec_ref(v_inst_296_);
v___x_306_ = lean_apply_2(v_toPure_304_, lean_box(0), v_b_301_);
return v___x_306_;
}
else
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___f_309_; uint8_t v_a_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_307_ = lean_box_usize(v_i_300_);
v___x_308_ = lean_box_usize(v_sz_299_);
lean_inc(v_f_298_);
lean_inc_ref(v_as_297_);
v___f_309_ = lean_alloc_closure((void*)(l_ByteArray_forInUnsafe_loop___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_309_, 0, v_toPure_304_);
lean_closure_set(v___f_309_, 1, v___x_307_);
lean_closure_set(v___f_309_, 2, v_inst_296_);
lean_closure_set(v___f_309_, 3, v_as_297_);
lean_closure_set(v___f_309_, 4, v_f_298_);
lean_closure_set(v___f_309_, 5, v___x_308_);
v_a_310_ = lean_byte_array_uget(v_as_297_, v_i_300_);
lean_dec_ref(v_as_297_);
v___x_311_ = lean_box(v_a_310_);
v___x_312_ = lean_apply_2(v_f_298_, v___x_311_, v_b_301_);
v___x_313_ = lean_apply_4(v_toBind_303_, lean_box(0), lean_box(0), v___x_312_, v___f_309_);
return v___x_313_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe_loop___redArg___lam__0(lean_object* v_toPure_314_, size_t v_i_315_, lean_object* v_inst_316_, lean_object* v_as_317_, lean_object* v_f_318_, size_t v_sz_319_, lean_object* v_____do__lift_320_){
_start:
{
if (lean_obj_tag(v_____do__lift_320_) == 0)
{
lean_object* v_a_321_; lean_object* v___x_322_; 
lean_dec(v_f_318_);
lean_dec_ref(v_as_317_);
lean_dec_ref(v_inst_316_);
v_a_321_ = lean_ctor_get(v_____do__lift_320_, 0);
lean_inc(v_a_321_);
lean_dec_ref_known(v_____do__lift_320_, 1);
v___x_322_ = lean_apply_2(v_toPure_314_, lean_box(0), v_a_321_);
return v___x_322_;
}
else
{
lean_object* v_a_323_; size_t v___x_324_; size_t v___x_325_; lean_object* v___x_326_; 
lean_dec(v_toPure_314_);
v_a_323_ = lean_ctor_get(v_____do__lift_320_, 0);
lean_inc(v_a_323_);
lean_dec_ref_known(v_____do__lift_320_, 1);
v___x_324_ = ((size_t)1ULL);
v___x_325_ = lean_usize_add(v_i_315_, v___x_324_);
v___x_326_ = l_ByteArray_forInUnsafe_loop___redArg(v_inst_316_, v_as_317_, v_f_318_, v_sz_319_, v___x_325_, v_a_323_);
return v___x_326_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe_loop___redArg___boxed(lean_object* v_inst_327_, lean_object* v_as_328_, lean_object* v_f_329_, lean_object* v_sz_330_, lean_object* v_i_331_, lean_object* v_b_332_){
_start:
{
size_t v_sz_boxed_333_; size_t v_i_boxed_334_; lean_object* v_res_335_; 
v_sz_boxed_333_ = lean_unbox_usize(v_sz_330_);
lean_dec(v_sz_330_);
v_i_boxed_334_ = lean_unbox_usize(v_i_331_);
lean_dec(v_i_331_);
v_res_335_ = l_ByteArray_forInUnsafe_loop___redArg(v_inst_327_, v_as_328_, v_f_329_, v_sz_boxed_333_, v_i_boxed_334_, v_b_332_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe_loop(lean_object* v_00_u03b2_336_, lean_object* v_m_337_, lean_object* v_inst_338_, lean_object* v_as_339_, lean_object* v_f_340_, size_t v_sz_341_, size_t v_i_342_, lean_object* v_b_343_){
_start:
{
lean_object* v___x_344_; 
v___x_344_ = l_ByteArray_forInUnsafe_loop___redArg(v_inst_338_, v_as_339_, v_f_340_, v_sz_341_, v_i_342_, v_b_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe_loop___boxed(lean_object* v_00_u03b2_345_, lean_object* v_m_346_, lean_object* v_inst_347_, lean_object* v_as_348_, lean_object* v_f_349_, lean_object* v_sz_350_, lean_object* v_i_351_, lean_object* v_b_352_){
_start:
{
size_t v_sz_boxed_353_; size_t v_i_boxed_354_; lean_object* v_res_355_; 
v_sz_boxed_353_ = lean_unbox_usize(v_sz_350_);
lean_dec(v_sz_350_);
v_i_boxed_354_ = lean_unbox_usize(v_i_351_);
lean_dec(v_i_351_);
v_res_355_ = l_ByteArray_forInUnsafe_loop(v_00_u03b2_345_, v_m_346_, v_inst_347_, v_as_348_, v_f_349_, v_sz_boxed_353_, v_i_boxed_354_, v_b_352_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe___redArg(lean_object* v_inst_356_, lean_object* v_as_357_, lean_object* v_b_358_, lean_object* v_f_359_){
_start:
{
size_t v_sz_360_; size_t v___x_361_; lean_object* v___x_362_; 
v_sz_360_ = lean_sarray_size(v_as_357_);
v___x_361_ = ((size_t)0ULL);
v___x_362_ = l_ByteArray_forInUnsafe_loop___redArg(v_inst_356_, v_as_357_, v_f_359_, v_sz_360_, v___x_361_, v_b_358_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe(lean_object* v_00_u03b2_363_, lean_object* v_m_364_, lean_object* v_inst_365_, lean_object* v_as_366_, lean_object* v_b_367_, lean_object* v_f_368_){
_start:
{
size_t v_sz_369_; size_t v___x_370_; lean_object* v___x_371_; 
v_sz_369_ = lean_sarray_size(v_as_366_);
v___x_370_ = ((size_t)0ULL);
v___x_371_ = l_ByteArray_forInUnsafe_loop___redArg(v_inst_365_, v_as_366_, v_f_368_, v_sz_369_, v___x_370_, v_b_367_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_forIn_loop___redArg___lam__0___boxed(lean_object* v_toPure_372_, lean_object* v_inst_373_, lean_object* v_as_374_, lean_object* v_f_375_, lean_object* v_n_376_, lean_object* v_____do__lift_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_ByteArray_forIn_loop___redArg___lam__0(v_toPure_372_, v_inst_373_, v_as_374_, v_f_375_, v_n_376_, v_____do__lift_377_);
lean_dec(v_n_376_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_forIn_loop___redArg(lean_object* v_inst_379_, lean_object* v_as_380_, lean_object* v_f_381_, lean_object* v_i_382_, lean_object* v_b_383_){
_start:
{
lean_object* v_toApplicative_384_; lean_object* v_toBind_385_; lean_object* v_toPure_386_; lean_object* v_zero_387_; uint8_t v_isZero_388_; 
v_toApplicative_384_ = lean_ctor_get(v_inst_379_, 0);
v_toBind_385_ = lean_ctor_get(v_inst_379_, 1);
lean_inc(v_toBind_385_);
v_toPure_386_ = lean_ctor_get(v_toApplicative_384_, 1);
lean_inc(v_toPure_386_);
v_zero_387_ = lean_unsigned_to_nat(0u);
v_isZero_388_ = lean_nat_dec_eq(v_i_382_, v_zero_387_);
if (v_isZero_388_ == 1)
{
lean_object* v___x_389_; 
lean_dec(v_toBind_385_);
lean_dec(v_f_381_);
lean_dec_ref(v_as_380_);
lean_dec_ref(v_inst_379_);
v___x_389_ = lean_apply_2(v_toPure_386_, lean_box(0), v_b_383_);
return v___x_389_;
}
else
{
lean_object* v_one_390_; lean_object* v_n_391_; lean_object* v___f_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; uint8_t v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v_one_390_ = lean_unsigned_to_nat(1u);
v_n_391_ = lean_nat_sub(v_i_382_, v_one_390_);
lean_inc(v_n_391_);
lean_inc(v_f_381_);
lean_inc_ref(v_as_380_);
v___f_392_ = lean_alloc_closure((void*)(l_ByteArray_forIn_loop___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_392_, 0, v_toPure_386_);
lean_closure_set(v___f_392_, 1, v_inst_379_);
lean_closure_set(v___f_392_, 2, v_as_380_);
lean_closure_set(v___f_392_, 3, v_f_381_);
lean_closure_set(v___f_392_, 4, v_n_391_);
v___x_393_ = lean_byte_array_size(v_as_380_);
v___x_394_ = lean_nat_sub(v___x_393_, v_one_390_);
v___x_395_ = lean_nat_sub(v___x_394_, v_n_391_);
lean_dec(v_n_391_);
lean_dec(v___x_394_);
v___x_396_ = lean_byte_array_fget(v_as_380_, v___x_395_);
lean_dec(v___x_395_);
lean_dec_ref(v_as_380_);
v___x_397_ = lean_box(v___x_396_);
v___x_398_ = lean_apply_2(v_f_381_, v___x_397_, v_b_383_);
v___x_399_ = lean_apply_4(v_toBind_385_, lean_box(0), lean_box(0), v___x_398_, v___f_392_);
return v___x_399_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_forIn_loop___redArg___lam__0(lean_object* v_toPure_400_, lean_object* v_inst_401_, lean_object* v_as_402_, lean_object* v_f_403_, lean_object* v_n_404_, lean_object* v_____do__lift_405_){
_start:
{
if (lean_obj_tag(v_____do__lift_405_) == 0)
{
lean_object* v_a_406_; lean_object* v___x_407_; 
lean_dec(v_f_403_);
lean_dec_ref(v_as_402_);
lean_dec_ref(v_inst_401_);
v_a_406_ = lean_ctor_get(v_____do__lift_405_, 0);
lean_inc(v_a_406_);
lean_dec_ref_known(v_____do__lift_405_, 1);
v___x_407_ = lean_apply_2(v_toPure_400_, lean_box(0), v_a_406_);
return v___x_407_;
}
else
{
lean_object* v_a_408_; lean_object* v___x_409_; 
lean_dec(v_toPure_400_);
v_a_408_ = lean_ctor_get(v_____do__lift_405_, 0);
lean_inc(v_a_408_);
lean_dec_ref_known(v_____do__lift_405_, 1);
v___x_409_ = l_ByteArray_forIn_loop___redArg(v_inst_401_, v_as_402_, v_f_403_, v_n_404_, v_a_408_);
return v___x_409_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_forIn_loop___redArg___boxed(lean_object* v_inst_410_, lean_object* v_as_411_, lean_object* v_f_412_, lean_object* v_i_413_, lean_object* v_b_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_ByteArray_forIn_loop___redArg(v_inst_410_, v_as_411_, v_f_412_, v_i_413_, v_b_414_);
lean_dec(v_i_413_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_forIn_loop(lean_object* v_00_u03b2_416_, lean_object* v_m_417_, lean_object* v_inst_418_, lean_object* v_as_419_, lean_object* v_f_420_, lean_object* v_i_421_, lean_object* v_h_422_, lean_object* v_b_423_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = l_ByteArray_forIn_loop___redArg(v_inst_418_, v_as_419_, v_f_420_, v_i_421_, v_b_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_forIn_loop___boxed(lean_object* v_00_u03b2_425_, lean_object* v_m_426_, lean_object* v_inst_427_, lean_object* v_as_428_, lean_object* v_f_429_, lean_object* v_i_430_, lean_object* v_h_431_, lean_object* v_b_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_ByteArray_forIn_loop(v_00_u03b2_425_, v_m_426_, v_inst_427_, v_as_428_, v_f_429_, v_i_430_, v_h_431_, v_b_432_);
lean_dec(v_i_430_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_instForInUInt8OfMonad___redArg___lam__0(lean_object* v_inst_434_, lean_object* v_00_u03b2_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_){
_start:
{
size_t v_sz_439_; size_t v___x_440_; lean_object* v___x_441_; 
v_sz_439_ = lean_sarray_size(v___y_436_);
v___x_440_ = ((size_t)0ULL);
v___x_441_ = l_ByteArray_forInUnsafe_loop___redArg(v_inst_434_, v___y_436_, v___y_438_, v_sz_439_, v___x_440_, v___y_437_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_instForInUInt8OfMonad___redArg(lean_object* v_inst_442_){
_start:
{
lean_object* v___f_443_; 
v___f_443_ = lean_alloc_closure((void*)(l_ByteArray_instForInUInt8OfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_443_, 0, v_inst_442_);
return v___f_443_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_instForInUInt8OfMonad(lean_object* v_m_444_, lean_object* v_inst_445_){
_start:
{
lean_object* v___f_446_; 
v___f_446_ = lean_alloc_closure((void*)(l_ByteArray_instForInUInt8OfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_446_, 0, v_inst_445_);
return v___f_446_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___redArg___lam__0___boxed(lean_object* v_i_447_, lean_object* v_inst_448_, lean_object* v_f_449_, lean_object* v_as_450_, lean_object* v_stop_451_, lean_object* v_____do__lift_452_){
_start:
{
size_t v_i_boxed_453_; size_t v_stop_boxed_454_; lean_object* v_res_455_; 
v_i_boxed_453_ = lean_unbox_usize(v_i_447_);
lean_dec(v_i_447_);
v_stop_boxed_454_ = lean_unbox_usize(v_stop_451_);
lean_dec(v_stop_451_);
v_res_455_ = l_ByteArray_foldlMUnsafe_fold___redArg___lam__0(v_i_boxed_453_, v_inst_448_, v_f_449_, v_as_450_, v_stop_boxed_454_, v_____do__lift_452_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___redArg(lean_object* v_inst_456_, lean_object* v_f_457_, lean_object* v_as_458_, size_t v_i_459_, size_t v_stop_460_, lean_object* v_b_461_){
_start:
{
lean_object* v_toApplicative_462_; lean_object* v_toBind_463_; lean_object* v_toPure_464_; uint8_t v___x_465_; 
v_toApplicative_462_ = lean_ctor_get(v_inst_456_, 0);
v_toBind_463_ = lean_ctor_get(v_inst_456_, 1);
lean_inc(v_toBind_463_);
v_toPure_464_ = lean_ctor_get(v_toApplicative_462_, 1);
v___x_465_ = lean_usize_dec_eq(v_i_459_, v_stop_460_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___f_468_; uint8_t v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_466_ = lean_box_usize(v_i_459_);
v___x_467_ = lean_box_usize(v_stop_460_);
lean_inc_ref(v_as_458_);
lean_inc(v_f_457_);
v___f_468_ = lean_alloc_closure((void*)(l_ByteArray_foldlMUnsafe_fold___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_468_, 0, v___x_466_);
lean_closure_set(v___f_468_, 1, v_inst_456_);
lean_closure_set(v___f_468_, 2, v_f_457_);
lean_closure_set(v___f_468_, 3, v_as_458_);
lean_closure_set(v___f_468_, 4, v___x_467_);
v___x_469_ = lean_byte_array_uget(v_as_458_, v_i_459_);
lean_dec_ref(v_as_458_);
v___x_470_ = lean_box(v___x_469_);
v___x_471_ = lean_apply_2(v_f_457_, v_b_461_, v___x_470_);
v___x_472_ = lean_apply_4(v_toBind_463_, lean_box(0), lean_box(0), v___x_471_, v___f_468_);
return v___x_472_;
}
else
{
lean_object* v___x_473_; 
lean_inc(v_toPure_464_);
lean_dec(v_toBind_463_);
lean_dec_ref(v_as_458_);
lean_dec(v_f_457_);
lean_dec_ref(v_inst_456_);
v___x_473_ = lean_apply_2(v_toPure_464_, lean_box(0), v_b_461_);
return v___x_473_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___redArg___lam__0(size_t v_i_474_, lean_object* v_inst_475_, lean_object* v_f_476_, lean_object* v_as_477_, size_t v_stop_478_, lean_object* v_____do__lift_479_){
_start:
{
size_t v___x_480_; size_t v___x_481_; lean_object* v___x_482_; 
v___x_480_ = ((size_t)1ULL);
v___x_481_ = lean_usize_add(v_i_474_, v___x_480_);
v___x_482_ = l_ByteArray_foldlMUnsafe_fold___redArg(v_inst_475_, v_f_476_, v_as_477_, v___x_481_, v_stop_478_, v_____do__lift_479_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___redArg___boxed(lean_object* v_inst_483_, lean_object* v_f_484_, lean_object* v_as_485_, lean_object* v_i_486_, lean_object* v_stop_487_, lean_object* v_b_488_){
_start:
{
size_t v_i_boxed_489_; size_t v_stop_boxed_490_; lean_object* v_res_491_; 
v_i_boxed_489_ = lean_unbox_usize(v_i_486_);
lean_dec(v_i_486_);
v_stop_boxed_490_ = lean_unbox_usize(v_stop_487_);
lean_dec(v_stop_487_);
v_res_491_ = l_ByteArray_foldlMUnsafe_fold___redArg(v_inst_483_, v_f_484_, v_as_485_, v_i_boxed_489_, v_stop_boxed_490_, v_b_488_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold(lean_object* v_00_u03b2_492_, lean_object* v_m_493_, lean_object* v_inst_494_, lean_object* v_f_495_, lean_object* v_as_496_, size_t v_i_497_, size_t v_stop_498_, lean_object* v_b_499_){
_start:
{
lean_object* v___x_500_; 
v___x_500_ = l_ByteArray_foldlMUnsafe_fold___redArg(v_inst_494_, v_f_495_, v_as_496_, v_i_497_, v_stop_498_, v_b_499_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___boxed(lean_object* v_00_u03b2_501_, lean_object* v_m_502_, lean_object* v_inst_503_, lean_object* v_f_504_, lean_object* v_as_505_, lean_object* v_i_506_, lean_object* v_stop_507_, lean_object* v_b_508_){
_start:
{
size_t v_i_boxed_509_; size_t v_stop_boxed_510_; lean_object* v_res_511_; 
v_i_boxed_509_ = lean_unbox_usize(v_i_506_);
lean_dec(v_i_506_);
v_stop_boxed_510_ = lean_unbox_usize(v_stop_507_);
lean_dec(v_stop_507_);
v_res_511_ = l_ByteArray_foldlMUnsafe_fold(v_00_u03b2_501_, v_m_502_, v_inst_503_, v_f_504_, v_as_505_, v_i_boxed_509_, v_stop_boxed_510_, v_b_508_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe___redArg(lean_object* v_inst_512_, lean_object* v_f_513_, lean_object* v_init_514_, lean_object* v_as_515_, lean_object* v_start_516_, lean_object* v_stop_517_){
_start:
{
lean_object* v_toApplicative_518_; lean_object* v_toPure_519_; uint8_t v___x_520_; 
v_toApplicative_518_ = lean_ctor_get(v_inst_512_, 0);
v_toPure_519_ = lean_ctor_get(v_toApplicative_518_, 1);
v___x_520_ = lean_nat_dec_lt(v_start_516_, v_stop_517_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; 
lean_inc(v_toPure_519_);
lean_dec_ref(v_as_515_);
lean_dec(v_f_513_);
lean_dec_ref(v_inst_512_);
v___x_521_ = lean_apply_2(v_toPure_519_, lean_box(0), v_init_514_);
return v___x_521_;
}
else
{
lean_object* v___x_522_; uint8_t v___x_523_; 
v___x_522_ = lean_byte_array_size(v_as_515_);
v___x_523_ = lean_nat_dec_le(v_stop_517_, v___x_522_);
if (v___x_523_ == 0)
{
uint8_t v___x_524_; 
v___x_524_ = lean_nat_dec_lt(v_start_516_, v___x_522_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; 
lean_inc(v_toPure_519_);
lean_dec_ref(v_as_515_);
lean_dec(v_f_513_);
lean_dec_ref(v_inst_512_);
v___x_525_ = lean_apply_2(v_toPure_519_, lean_box(0), v_init_514_);
return v___x_525_;
}
else
{
size_t v___x_526_; size_t v___x_527_; lean_object* v___x_528_; 
v___x_526_ = lean_usize_of_nat(v_start_516_);
v___x_527_ = lean_usize_of_nat(v___x_522_);
v___x_528_ = l_ByteArray_foldlMUnsafe_fold___redArg(v_inst_512_, v_f_513_, v_as_515_, v___x_526_, v___x_527_, v_init_514_);
return v___x_528_;
}
}
else
{
size_t v___x_529_; size_t v___x_530_; lean_object* v___x_531_; 
v___x_529_ = lean_usize_of_nat(v_start_516_);
v___x_530_ = lean_usize_of_nat(v_stop_517_);
v___x_531_ = l_ByteArray_foldlMUnsafe_fold___redArg(v_inst_512_, v_f_513_, v_as_515_, v___x_529_, v___x_530_, v_init_514_);
return v___x_531_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe___redArg___boxed(lean_object* v_inst_532_, lean_object* v_f_533_, lean_object* v_init_534_, lean_object* v_as_535_, lean_object* v_start_536_, lean_object* v_stop_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_ByteArray_foldlMUnsafe___redArg(v_inst_532_, v_f_533_, v_init_534_, v_as_535_, v_start_536_, v_stop_537_);
lean_dec(v_stop_537_);
lean_dec(v_start_536_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe(lean_object* v_00_u03b2_539_, lean_object* v_m_540_, lean_object* v_inst_541_, lean_object* v_f_542_, lean_object* v_init_543_, lean_object* v_as_544_, lean_object* v_start_545_, lean_object* v_stop_546_){
_start:
{
lean_object* v_toApplicative_547_; lean_object* v_toPure_548_; uint8_t v___x_549_; 
v_toApplicative_547_ = lean_ctor_get(v_inst_541_, 0);
v_toPure_548_ = lean_ctor_get(v_toApplicative_547_, 1);
v___x_549_ = lean_nat_dec_lt(v_start_545_, v_stop_546_);
if (v___x_549_ == 0)
{
lean_object* v___x_550_; 
lean_inc(v_toPure_548_);
lean_dec_ref(v_as_544_);
lean_dec(v_f_542_);
lean_dec_ref(v_inst_541_);
v___x_550_ = lean_apply_2(v_toPure_548_, lean_box(0), v_init_543_);
return v___x_550_;
}
else
{
lean_object* v___x_551_; uint8_t v___x_552_; 
v___x_551_ = lean_byte_array_size(v_as_544_);
v___x_552_ = lean_nat_dec_le(v_stop_546_, v___x_551_);
if (v___x_552_ == 0)
{
uint8_t v___x_553_; 
v___x_553_ = lean_nat_dec_lt(v_start_545_, v___x_551_);
if (v___x_553_ == 0)
{
lean_object* v___x_554_; 
lean_inc(v_toPure_548_);
lean_dec_ref(v_as_544_);
lean_dec(v_f_542_);
lean_dec_ref(v_inst_541_);
v___x_554_ = lean_apply_2(v_toPure_548_, lean_box(0), v_init_543_);
return v___x_554_;
}
else
{
size_t v___x_555_; size_t v___x_556_; lean_object* v___x_557_; 
v___x_555_ = lean_usize_of_nat(v_start_545_);
v___x_556_ = lean_usize_of_nat(v___x_551_);
v___x_557_ = l_ByteArray_foldlMUnsafe_fold___redArg(v_inst_541_, v_f_542_, v_as_544_, v___x_555_, v___x_556_, v_init_543_);
return v___x_557_;
}
}
else
{
size_t v___x_558_; size_t v___x_559_; lean_object* v___x_560_; 
v___x_558_ = lean_usize_of_nat(v_start_545_);
v___x_559_ = lean_usize_of_nat(v_stop_546_);
v___x_560_ = l_ByteArray_foldlMUnsafe_fold___redArg(v_inst_541_, v_f_542_, v_as_544_, v___x_558_, v___x_559_, v_init_543_);
return v___x_560_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe___boxed(lean_object* v_00_u03b2_561_, lean_object* v_m_562_, lean_object* v_inst_563_, lean_object* v_f_564_, lean_object* v_init_565_, lean_object* v_as_566_, lean_object* v_start_567_, lean_object* v_stop_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_ByteArray_foldlMUnsafe(v_00_u03b2_561_, v_m_562_, v_inst_563_, v_f_564_, v_init_565_, v_as_566_, v_start_567_, v_stop_568_);
lean_dec(v_stop_568_);
lean_dec(v_start_567_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlM_loop___redArg___lam__0___boxed(lean_object* v_j_570_, lean_object* v_inst_571_, lean_object* v_f_572_, lean_object* v_as_573_, lean_object* v_stop_574_, lean_object* v_n_575_, lean_object* v_____do__lift_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_ByteArray_foldlM_loop___redArg___lam__0(v_j_570_, v_inst_571_, v_f_572_, v_as_573_, v_stop_574_, v_n_575_, v_____do__lift_576_);
lean_dec(v_n_575_);
lean_dec(v_j_570_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlM_loop___redArg(lean_object* v_inst_578_, lean_object* v_f_579_, lean_object* v_as_580_, lean_object* v_stop_581_, lean_object* v_i_582_, lean_object* v_j_583_, lean_object* v_b_584_){
_start:
{
lean_object* v_toApplicative_585_; lean_object* v_toBind_586_; lean_object* v_toPure_587_; uint8_t v___x_588_; 
v_toApplicative_585_ = lean_ctor_get(v_inst_578_, 0);
v_toBind_586_ = lean_ctor_get(v_inst_578_, 1);
lean_inc(v_toBind_586_);
v_toPure_587_ = lean_ctor_get(v_toApplicative_585_, 1);
v___x_588_ = lean_nat_dec_lt(v_j_583_, v_stop_581_);
if (v___x_588_ == 0)
{
lean_object* v___x_589_; 
lean_inc(v_toPure_587_);
lean_dec(v_toBind_586_);
lean_dec(v_j_583_);
lean_dec(v_stop_581_);
lean_dec_ref(v_as_580_);
lean_dec(v_f_579_);
lean_dec_ref(v_inst_578_);
v___x_589_ = lean_apply_2(v_toPure_587_, lean_box(0), v_b_584_);
return v___x_589_;
}
else
{
lean_object* v_zero_590_; uint8_t v_isZero_591_; 
v_zero_590_ = lean_unsigned_to_nat(0u);
v_isZero_591_ = lean_nat_dec_eq(v_i_582_, v_zero_590_);
if (v_isZero_591_ == 1)
{
lean_object* v___x_592_; 
lean_inc(v_toPure_587_);
lean_dec(v_toBind_586_);
lean_dec(v_j_583_);
lean_dec(v_stop_581_);
lean_dec_ref(v_as_580_);
lean_dec(v_f_579_);
lean_dec_ref(v_inst_578_);
v___x_592_ = lean_apply_2(v_toPure_587_, lean_box(0), v_b_584_);
return v___x_592_;
}
else
{
lean_object* v_one_593_; lean_object* v_n_594_; lean_object* v___f_595_; uint8_t v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v_one_593_ = lean_unsigned_to_nat(1u);
v_n_594_ = lean_nat_sub(v_i_582_, v_one_593_);
lean_inc_ref(v_as_580_);
lean_inc(v_f_579_);
lean_inc(v_j_583_);
v___f_595_ = lean_alloc_closure((void*)(l_ByteArray_foldlM_loop___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_595_, 0, v_j_583_);
lean_closure_set(v___f_595_, 1, v_inst_578_);
lean_closure_set(v___f_595_, 2, v_f_579_);
lean_closure_set(v___f_595_, 3, v_as_580_);
lean_closure_set(v___f_595_, 4, v_stop_581_);
lean_closure_set(v___f_595_, 5, v_n_594_);
v___x_596_ = lean_byte_array_fget(v_as_580_, v_j_583_);
lean_dec(v_j_583_);
lean_dec_ref(v_as_580_);
v___x_597_ = lean_box(v___x_596_);
v___x_598_ = lean_apply_2(v_f_579_, v_b_584_, v___x_597_);
v___x_599_ = lean_apply_4(v_toBind_586_, lean_box(0), lean_box(0), v___x_598_, v___f_595_);
return v___x_599_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlM_loop___redArg___lam__0(lean_object* v_j_600_, lean_object* v_inst_601_, lean_object* v_f_602_, lean_object* v_as_603_, lean_object* v_stop_604_, lean_object* v_n_605_, lean_object* v_____do__lift_606_){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_607_ = lean_unsigned_to_nat(1u);
v___x_608_ = lean_nat_add(v_j_600_, v___x_607_);
v___x_609_ = l_ByteArray_foldlM_loop___redArg(v_inst_601_, v_f_602_, v_as_603_, v_stop_604_, v_n_605_, v___x_608_, v_____do__lift_606_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlM_loop___redArg___boxed(lean_object* v_inst_610_, lean_object* v_f_611_, lean_object* v_as_612_, lean_object* v_stop_613_, lean_object* v_i_614_, lean_object* v_j_615_, lean_object* v_b_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_ByteArray_foldlM_loop___redArg(v_inst_610_, v_f_611_, v_as_612_, v_stop_613_, v_i_614_, v_j_615_, v_b_616_);
lean_dec(v_i_614_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlM_loop(lean_object* v_00_u03b2_618_, lean_object* v_m_619_, lean_object* v_inst_620_, lean_object* v_f_621_, lean_object* v_as_622_, lean_object* v_stop_623_, lean_object* v_h_624_, lean_object* v_i_625_, lean_object* v_j_626_, lean_object* v_b_627_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l_ByteArray_foldlM_loop___redArg(v_inst_620_, v_f_621_, v_as_622_, v_stop_623_, v_i_625_, v_j_626_, v_b_627_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlM_loop___boxed(lean_object* v_00_u03b2_629_, lean_object* v_m_630_, lean_object* v_inst_631_, lean_object* v_f_632_, lean_object* v_as_633_, lean_object* v_stop_634_, lean_object* v_h_635_, lean_object* v_i_636_, lean_object* v_j_637_, lean_object* v_b_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_ByteArray_foldlM_loop(v_00_u03b2_629_, v_m_630_, v_inst_631_, v_f_632_, v_as_633_, v_stop_634_, v_h_635_, v_i_636_, v_j_637_, v_b_638_);
lean_dec(v_i_636_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldl___redArg___lam__0(lean_object* v_f_640_, lean_object* v_x1_641_, uint8_t v_x2_642_){
_start:
{
lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_643_ = lean_box(v_x2_642_);
v___x_644_ = lean_apply_2(v_f_640_, v_x1_641_, v___x_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldl___redArg___lam__0___boxed(lean_object* v_f_645_, lean_object* v_x1_646_, lean_object* v_x2_647_){
_start:
{
uint8_t v_x2_185__boxed_648_; lean_object* v_res_649_; 
v_x2_185__boxed_648_ = lean_unbox(v_x2_647_);
v_res_649_ = l_ByteArray_foldl___redArg___lam__0(v_f_645_, v_x1_646_, v_x2_185__boxed_648_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldl___redArg(lean_object* v_f_669_, lean_object* v_init_670_, lean_object* v_as_671_, lean_object* v_start_672_, lean_object* v_stop_673_){
_start:
{
lean_object* v___x_674_; uint8_t v___x_675_; 
v___x_674_ = ((lean_object*)(l_ByteArray_foldl___redArg___closed__9));
v___x_675_ = lean_nat_dec_lt(v_start_672_, v_stop_673_);
if (v___x_675_ == 0)
{
lean_dec_ref(v_as_671_);
lean_dec(v_f_669_);
return v_init_670_;
}
else
{
lean_object* v___f_676_; lean_object* v___x_677_; uint8_t v___x_678_; 
v___f_676_ = lean_alloc_closure((void*)(l_ByteArray_foldl___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_676_, 0, v_f_669_);
v___x_677_ = lean_byte_array_size(v_as_671_);
v___x_678_ = lean_nat_dec_le(v_stop_673_, v___x_677_);
if (v___x_678_ == 0)
{
uint8_t v___x_679_; 
v___x_679_ = lean_nat_dec_lt(v_start_672_, v___x_677_);
if (v___x_679_ == 0)
{
lean_dec_ref(v___f_676_);
lean_dec_ref(v_as_671_);
return v_init_670_;
}
else
{
size_t v___x_680_; size_t v___x_681_; lean_object* v___x_682_; 
v___x_680_ = lean_usize_of_nat(v_start_672_);
v___x_681_ = lean_usize_of_nat(v___x_677_);
v___x_682_ = l_ByteArray_foldlMUnsafe_fold___redArg(v___x_674_, v___f_676_, v_as_671_, v___x_680_, v___x_681_, v_init_670_);
return v___x_682_;
}
}
else
{
size_t v___x_683_; size_t v___x_684_; lean_object* v___x_685_; 
v___x_683_ = lean_usize_of_nat(v_start_672_);
v___x_684_ = lean_usize_of_nat(v_stop_673_);
v___x_685_ = l_ByteArray_foldlMUnsafe_fold___redArg(v___x_674_, v___f_676_, v_as_671_, v___x_683_, v___x_684_, v_init_670_);
return v___x_685_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldl___redArg___boxed(lean_object* v_f_686_, lean_object* v_init_687_, lean_object* v_as_688_, lean_object* v_start_689_, lean_object* v_stop_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_ByteArray_foldl___redArg(v_f_686_, v_init_687_, v_as_688_, v_start_689_, v_stop_690_);
lean_dec(v_stop_690_);
lean_dec(v_start_689_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldl(lean_object* v_00_u03b2_692_, lean_object* v_f_693_, lean_object* v_init_694_, lean_object* v_as_695_, lean_object* v_start_696_, lean_object* v_stop_697_){
_start:
{
lean_object* v___x_698_; uint8_t v___x_699_; 
v___x_698_ = ((lean_object*)(l_ByteArray_foldl___redArg___closed__9));
v___x_699_ = lean_nat_dec_lt(v_start_696_, v_stop_697_);
if (v___x_699_ == 0)
{
lean_dec_ref(v_as_695_);
lean_dec(v_f_693_);
return v_init_694_;
}
else
{
lean_object* v___f_700_; lean_object* v___x_701_; uint8_t v___x_702_; 
v___f_700_ = lean_alloc_closure((void*)(l_ByteArray_foldl___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_700_, 0, v_f_693_);
v___x_701_ = lean_byte_array_size(v_as_695_);
v___x_702_ = lean_nat_dec_le(v_stop_697_, v___x_701_);
if (v___x_702_ == 0)
{
uint8_t v___x_703_; 
v___x_703_ = lean_nat_dec_lt(v_start_696_, v___x_701_);
if (v___x_703_ == 0)
{
lean_dec_ref(v___f_700_);
lean_dec_ref(v_as_695_);
return v_init_694_;
}
else
{
size_t v___x_704_; size_t v___x_705_; lean_object* v___x_706_; 
v___x_704_ = lean_usize_of_nat(v_start_696_);
v___x_705_ = lean_usize_of_nat(v___x_701_);
v___x_706_ = l_ByteArray_foldlMUnsafe_fold___redArg(v___x_698_, v___f_700_, v_as_695_, v___x_704_, v___x_705_, v_init_694_);
return v___x_706_;
}
}
else
{
size_t v___x_707_; size_t v___x_708_; lean_object* v___x_709_; 
v___x_707_ = lean_usize_of_nat(v_start_696_);
v___x_708_ = lean_usize_of_nat(v_stop_697_);
v___x_709_ = l_ByteArray_foldlMUnsafe_fold___redArg(v___x_698_, v___f_700_, v_as_695_, v___x_707_, v___x_708_, v_init_694_);
return v___x_709_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldl___boxed(lean_object* v_00_u03b2_710_, lean_object* v_f_711_, lean_object* v_init_712_, lean_object* v_as_713_, lean_object* v_start_714_, lean_object* v_stop_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_ByteArray_foldl(v_00_u03b2_710_, v_f_711_, v_init_712_, v_as_713_, v_start_714_, v_stop_715_);
lean_dec(v_stop_715_);
lean_dec(v_start_714_);
return v_res_716_;
}
}
static lean_object* _init_l_ByteArray_instInhabitedIterator_default___closed__0(void){
_start:
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_717_ = lean_unsigned_to_nat(0u);
v___x_718_ = l_ByteArray_empty;
v___x_719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_719_, 0, v___x_718_);
lean_ctor_set(v___x_719_, 1, v___x_717_);
return v___x_719_;
}
}
static lean_object* _init_l_ByteArray_instInhabitedIterator_default(void){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = lean_obj_once(&l_ByteArray_instInhabitedIterator_default___closed__0, &l_ByteArray_instInhabitedIterator_default___closed__0_once, _init_l_ByteArray_instInhabitedIterator_default___closed__0);
return v___x_720_;
}
}
static lean_object* _init_l_ByteArray_instInhabitedIterator(void){
_start:
{
lean_object* v___x_721_; 
v___x_721_ = l_ByteArray_instInhabitedIterator_default;
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_mkIterator(lean_object* v_arr_722_){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_723_ = lean_unsigned_to_nat(0u);
v___x_724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_724_, 0, v_arr_722_);
lean_ctor_set(v___x_724_, 1, v___x_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_iter(lean_object* v_arr_725_){
_start:
{
lean_object* v___x_726_; 
v___x_726_ = l_ByteArray_mkIterator(v_arr_725_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_instSizeOfIterator___lam__0(lean_object* v_i_727_){
_start:
{
lean_object* v_array_728_; lean_object* v_idx_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v_array_728_ = lean_ctor_get(v_i_727_, 0);
v_idx_729_ = lean_ctor_get(v_i_727_, 1);
v___x_730_ = lean_byte_array_size(v_array_728_);
v___x_731_ = lean_nat_sub(v___x_730_, v_idx_729_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_instSizeOfIterator___lam__0___boxed(lean_object* v_i_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l_ByteArray_instSizeOfIterator___lam__0(v_i_732_);
lean_dec_ref(v_i_732_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_remainingBytes(lean_object* v_x_736_){
_start:
{
lean_object* v_array_737_; lean_object* v_idx_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v_array_737_ = lean_ctor_get(v_x_736_, 0);
v_idx_738_ = lean_ctor_get(v_x_736_, 1);
v___x_739_ = lean_byte_array_size(v_array_737_);
v___x_740_ = lean_nat_sub(v___x_739_, v_idx_738_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_remainingBytes___boxed(lean_object* v_x_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_ByteArray_Iterator_remainingBytes(v_x_741_);
lean_dec_ref(v_x_741_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_pos(lean_object* v_self_743_){
_start:
{
lean_object* v_idx_744_; 
v_idx_744_ = lean_ctor_get(v_self_743_, 1);
lean_inc(v_idx_744_);
return v_idx_744_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_pos___boxed(lean_object* v_self_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_ByteArray_Iterator_pos(v_self_745_);
lean_dec_ref(v_self_745_);
return v_res_746_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_Iterator_atEnd(lean_object* v_x_747_){
_start:
{
lean_object* v_array_748_; lean_object* v_idx_749_; lean_object* v___x_750_; uint8_t v___x_751_; 
v_array_748_ = lean_ctor_get(v_x_747_, 0);
v_idx_749_ = lean_ctor_get(v_x_747_, 1);
v___x_750_ = lean_byte_array_size(v_array_748_);
v___x_751_ = lean_nat_dec_le(v___x_750_, v_idx_749_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_atEnd___boxed(lean_object* v_x_752_){
_start:
{
uint8_t v_res_753_; lean_object* v_r_754_; 
v_res_753_ = l_ByteArray_Iterator_atEnd(v_x_752_);
lean_dec_ref(v_x_752_);
v_r_754_ = lean_box(v_res_753_);
return v_r_754_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_Iterator_curr(lean_object* v_x_755_){
_start:
{
lean_object* v_array_756_; lean_object* v_idx_757_; lean_object* v___x_758_; uint8_t v___x_759_; 
v_array_756_ = lean_ctor_get(v_x_755_, 0);
v_idx_757_ = lean_ctor_get(v_x_755_, 1);
v___x_758_ = lean_byte_array_size(v_array_756_);
v___x_759_ = lean_nat_dec_lt(v_idx_757_, v___x_758_);
if (v___x_759_ == 0)
{
uint8_t v___x_760_; 
v___x_760_ = 0;
return v___x_760_;
}
else
{
uint8_t v___x_761_; 
v___x_761_ = lean_byte_array_fget(v_array_756_, v_idx_757_);
return v___x_761_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_curr___boxed(lean_object* v_x_762_){
_start:
{
uint8_t v_res_763_; lean_object* v_r_764_; 
v_res_763_ = l_ByteArray_Iterator_curr(v_x_762_);
lean_dec_ref(v_x_762_);
v_r_764_ = lean_box(v_res_763_);
return v_r_764_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_next(lean_object* v_x_765_){
_start:
{
lean_object* v_array_766_; lean_object* v_idx_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_776_; 
v_array_766_ = lean_ctor_get(v_x_765_, 0);
v_idx_767_ = lean_ctor_get(v_x_765_, 1);
v_isSharedCheck_776_ = !lean_is_exclusive(v_x_765_);
if (v_isSharedCheck_776_ == 0)
{
v___x_769_ = v_x_765_;
v_isShared_770_ = v_isSharedCheck_776_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_idx_767_);
lean_inc(v_array_766_);
lean_dec(v_x_765_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_776_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_774_; 
v___x_771_ = lean_unsigned_to_nat(1u);
v___x_772_ = lean_nat_add(v_idx_767_, v___x_771_);
lean_dec(v_idx_767_);
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 1, v___x_772_);
v___x_774_ = v___x_769_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_array_766_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v___x_772_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_prev(lean_object* v_x_777_){
_start:
{
lean_object* v_array_778_; lean_object* v_idx_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_788_; 
v_array_778_ = lean_ctor_get(v_x_777_, 0);
v_idx_779_ = lean_ctor_get(v_x_777_, 1);
v_isSharedCheck_788_ = !lean_is_exclusive(v_x_777_);
if (v_isSharedCheck_788_ == 0)
{
v___x_781_ = v_x_777_;
v_isShared_782_ = v_isSharedCheck_788_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_idx_779_);
lean_inc(v_array_778_);
lean_dec(v_x_777_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_788_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_786_; 
v___x_783_ = lean_unsigned_to_nat(1u);
v___x_784_ = lean_nat_sub(v_idx_779_, v___x_783_);
lean_dec(v_idx_779_);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 1, v___x_784_);
v___x_786_ = v___x_781_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_array_778_);
lean_ctor_set(v_reuseFailAlloc_787_, 1, v___x_784_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
}
LEAN_EXPORT uint8_t l_ByteArray_Iterator_hasNext(lean_object* v_x_789_){
_start:
{
lean_object* v_array_790_; lean_object* v_idx_791_; lean_object* v___x_792_; uint8_t v___x_793_; 
v_array_790_ = lean_ctor_get(v_x_789_, 0);
v_idx_791_ = lean_ctor_get(v_x_789_, 1);
v___x_792_ = lean_byte_array_size(v_array_790_);
v___x_793_ = lean_nat_dec_lt(v_idx_791_, v___x_792_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_hasNext___boxed(lean_object* v_x_794_){
_start:
{
uint8_t v_res_795_; lean_object* v_r_796_; 
v_res_795_ = l_ByteArray_Iterator_hasNext(v_x_794_);
lean_dec_ref(v_x_794_);
v_r_796_ = lean_box(v_res_795_);
return v_r_796_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Basic_0__ByteArray_Iterator_remainingBytes_match__1_splitter___redArg(lean_object* v_x_797_, lean_object* v_h__1_798_){
_start:
{
lean_object* v_array_799_; lean_object* v_idx_800_; lean_object* v___x_801_; 
v_array_799_ = lean_ctor_get(v_x_797_, 0);
lean_inc_ref(v_array_799_);
v_idx_800_ = lean_ctor_get(v_x_797_, 1);
lean_inc(v_idx_800_);
lean_dec_ref(v_x_797_);
v___x_801_ = lean_apply_2(v_h__1_798_, v_array_799_, v_idx_800_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Basic_0__ByteArray_Iterator_remainingBytes_match__1_splitter(lean_object* v_motive_802_, lean_object* v_x_803_, lean_object* v_h__1_804_){
_start:
{
lean_object* v_array_805_; lean_object* v_idx_806_; lean_object* v___x_807_; 
v_array_805_ = lean_ctor_get(v_x_803_, 0);
lean_inc_ref(v_array_805_);
v_idx_806_ = lean_ctor_get(v_x_803_, 1);
lean_inc(v_idx_806_);
lean_dec_ref(v_x_803_);
v___x_807_ = lean_apply_2(v_h__1_804_, v_array_805_, v_idx_806_);
return v___x_807_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_Iterator_curr_x27___redArg(lean_object* v_it_808_){
_start:
{
lean_object* v_array_809_; lean_object* v_idx_810_; uint8_t v___x_811_; 
v_array_809_ = lean_ctor_get(v_it_808_, 0);
v_idx_810_ = lean_ctor_get(v_it_808_, 1);
v___x_811_ = lean_byte_array_fget(v_array_809_, v_idx_810_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_curr_x27___redArg___boxed(lean_object* v_it_812_){
_start:
{
uint8_t v_res_813_; lean_object* v_r_814_; 
v_res_813_ = l_ByteArray_Iterator_curr_x27___redArg(v_it_812_);
lean_dec_ref(v_it_812_);
v_r_814_ = lean_box(v_res_813_);
return v_r_814_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_Iterator_curr_x27(lean_object* v_it_815_, lean_object* v_h_816_){
_start:
{
lean_object* v_array_817_; lean_object* v_idx_818_; uint8_t v___x_819_; 
v_array_817_ = lean_ctor_get(v_it_815_, 0);
v_idx_818_ = lean_ctor_get(v_it_815_, 1);
v___x_819_ = lean_byte_array_fget(v_array_817_, v_idx_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_curr_x27___boxed(lean_object* v_it_820_, lean_object* v_h_821_){
_start:
{
uint8_t v_res_822_; lean_object* v_r_823_; 
v_res_822_ = l_ByteArray_Iterator_curr_x27(v_it_820_, v_h_821_);
lean_dec_ref(v_it_820_);
v_r_823_ = lean_box(v_res_822_);
return v_r_823_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_next_x27___redArg(lean_object* v_it_824_){
_start:
{
lean_object* v_array_825_; lean_object* v_idx_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_835_; 
v_array_825_ = lean_ctor_get(v_it_824_, 0);
v_idx_826_ = lean_ctor_get(v_it_824_, 1);
v_isSharedCheck_835_ = !lean_is_exclusive(v_it_824_);
if (v_isSharedCheck_835_ == 0)
{
v___x_828_ = v_it_824_;
v_isShared_829_ = v_isSharedCheck_835_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_idx_826_);
lean_inc(v_array_825_);
lean_dec(v_it_824_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_835_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_833_; 
v___x_830_ = lean_unsigned_to_nat(1u);
v___x_831_ = lean_nat_add(v_idx_826_, v___x_830_);
lean_dec(v_idx_826_);
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 1, v___x_831_);
v___x_833_ = v___x_828_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_array_825_);
lean_ctor_set(v_reuseFailAlloc_834_, 1, v___x_831_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_next_x27(lean_object* v_it_836_, lean_object* v___h_837_){
_start:
{
lean_object* v_array_838_; lean_object* v_idx_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_848_; 
v_array_838_ = lean_ctor_get(v_it_836_, 0);
v_idx_839_ = lean_ctor_get(v_it_836_, 1);
v_isSharedCheck_848_ = !lean_is_exclusive(v_it_836_);
if (v_isSharedCheck_848_ == 0)
{
v___x_841_ = v_it_836_;
v_isShared_842_ = v_isSharedCheck_848_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_idx_839_);
lean_inc(v_array_838_);
lean_dec(v_it_836_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_848_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_846_; 
v___x_843_ = lean_unsigned_to_nat(1u);
v___x_844_ = lean_nat_add(v_idx_839_, v___x_843_);
lean_dec(v_idx_839_);
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 1, v___x_844_);
v___x_846_ = v___x_841_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_array_838_);
lean_ctor_set(v_reuseFailAlloc_847_, 1, v___x_844_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
}
LEAN_EXPORT uint8_t l_ByteArray_Iterator_hasPrev(lean_object* v_x_849_){
_start:
{
lean_object* v_idx_850_; lean_object* v___x_851_; uint8_t v___x_852_; 
v_idx_850_ = lean_ctor_get(v_x_849_, 1);
v___x_851_ = lean_unsigned_to_nat(0u);
v___x_852_ = lean_nat_dec_lt(v___x_851_, v_idx_850_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_hasPrev___boxed(lean_object* v_x_853_){
_start:
{
uint8_t v_res_854_; lean_object* v_r_855_; 
v_res_854_ = l_ByteArray_Iterator_hasPrev(v_x_853_);
lean_dec_ref(v_x_853_);
v_r_855_ = lean_box(v_res_854_);
return v_r_855_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_toEnd(lean_object* v_x_856_){
_start:
{
lean_object* v_array_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_865_; 
v_array_857_ = lean_ctor_get(v_x_856_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v_x_856_);
if (v_isSharedCheck_865_ == 0)
{
lean_object* v_unused_866_; 
v_unused_866_ = lean_ctor_get(v_x_856_, 1);
lean_dec(v_unused_866_);
v___x_859_ = v_x_856_;
v_isShared_860_ = v_isSharedCheck_865_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_array_857_);
lean_dec(v_x_856_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_865_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_861_; lean_object* v___x_863_; 
v___x_861_ = lean_byte_array_size(v_array_857_);
if (v_isShared_860_ == 0)
{
lean_ctor_set(v___x_859_, 1, v___x_861_);
v___x_863_ = v___x_859_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_array_857_);
lean_ctor_set(v_reuseFailAlloc_864_, 1, v___x_861_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_forward(lean_object* v_x_867_, lean_object* v_x_868_){
_start:
{
lean_object* v_array_869_; lean_object* v_idx_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_878_; 
v_array_869_ = lean_ctor_get(v_x_867_, 0);
v_idx_870_ = lean_ctor_get(v_x_867_, 1);
v_isSharedCheck_878_ = !lean_is_exclusive(v_x_867_);
if (v_isSharedCheck_878_ == 0)
{
v___x_872_ = v_x_867_;
v_isShared_873_ = v_isSharedCheck_878_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_idx_870_);
lean_inc(v_array_869_);
lean_dec(v_x_867_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_878_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_874_; lean_object* v___x_876_; 
v___x_874_ = lean_nat_add(v_idx_870_, v_x_868_);
lean_dec(v_idx_870_);
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 1, v___x_874_);
v___x_876_ = v___x_872_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_array_869_);
lean_ctor_set(v_reuseFailAlloc_877_, 1, v___x_874_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_forward___boxed(lean_object* v_x_879_, lean_object* v_x_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_ByteArray_Iterator_forward(v_x_879_, v_x_880_);
lean_dec(v_x_880_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_nextn(lean_object* v_a_882_, lean_object* v_a_883_){
_start:
{
lean_object* v_array_884_; lean_object* v_idx_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_893_; 
v_array_884_ = lean_ctor_get(v_a_882_, 0);
v_idx_885_ = lean_ctor_get(v_a_882_, 1);
v_isSharedCheck_893_ = !lean_is_exclusive(v_a_882_);
if (v_isSharedCheck_893_ == 0)
{
v___x_887_ = v_a_882_;
v_isShared_888_ = v_isSharedCheck_893_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_idx_885_);
lean_inc(v_array_884_);
lean_dec(v_a_882_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_893_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_889_; lean_object* v___x_891_; 
v___x_889_ = lean_nat_add(v_idx_885_, v_a_883_);
lean_dec(v_idx_885_);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 1, v___x_889_);
v___x_891_ = v___x_887_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_array_884_);
lean_ctor_set(v_reuseFailAlloc_892_, 1, v___x_889_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_nextn___boxed(lean_object* v_a_894_, lean_object* v_a_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l_ByteArray_Iterator_nextn(v_a_894_, v_a_895_);
lean_dec(v_a_895_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_prevn(lean_object* v_x_897_, lean_object* v_x_898_){
_start:
{
lean_object* v_array_899_; lean_object* v_idx_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_908_; 
v_array_899_ = lean_ctor_get(v_x_897_, 0);
v_idx_900_ = lean_ctor_get(v_x_897_, 1);
v_isSharedCheck_908_ = !lean_is_exclusive(v_x_897_);
if (v_isSharedCheck_908_ == 0)
{
v___x_902_ = v_x_897_;
v_isShared_903_ = v_isSharedCheck_908_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_idx_900_);
lean_inc(v_array_899_);
lean_dec(v_x_897_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_908_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_904_; lean_object* v___x_906_; 
v___x_904_ = lean_nat_sub(v_idx_900_, v_x_898_);
lean_dec(v_idx_900_);
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 1, v___x_904_);
v___x_906_ = v___x_902_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_array_899_);
lean_ctor_set(v_reuseFailAlloc_907_, 1, v___x_904_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_prevn___boxed(lean_object* v_x_909_, lean_object* v_x_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_ByteArray_Iterator_prevn(v_x_909_, v_x_910_);
lean_dec(v_x_910_);
return v_res_911_;
}
}
lean_object* runtime_initialize_Init_Data_UInt_BasicAux(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_DecidableEq(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Attach(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_ByteArray_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
