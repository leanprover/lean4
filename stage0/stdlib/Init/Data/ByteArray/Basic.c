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
lean_object* lean_sarray_mark_linear(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_markLinear___boxed(lean_object*);
lean_object* lean_sarray_propagate_mark(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_propagateMark___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT void l_ByteArray_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_lhs_1_ = stack[0].m_obj;
lean_object* v_rhs_2_ = stack[1].m_obj;
uint8_t v_res_3_;
v_res_3_ = lean_sarray_dec_eq(v_lhs_1_, v_rhs_2_);
stack->m_num = v_res_3_;
}
LEAN_EXPORT lean_object* l_ByteArray_beq___boxed(lean_object* v_lhs_4_, lean_object* v_rhs_5_){
_start:
{
uint8_t v_res_6_; lean_object* v_r_7_; 
v_res_6_ = lean_sarray_dec_eq(v_lhs_4_, v_rhs_5_);
lean_dec_ref(v_rhs_5_);
lean_dec_ref(v_lhs_4_);
v_r_7_ = lean_box(v_res_6_);
return v_r_7_;
}
}
LEAN_EXPORT void l_ByteArray_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_lhs_10_ = stack[0].m_obj;
lean_object* v_rhs_11_ = stack[1].m_obj;
uint8_t v_res_12_;
v_res_12_ = lean_sarray_dec_eq(v_lhs_10_, v_rhs_11_);
stack->m_num = v_res_12_;
}
LEAN_EXPORT lean_object* l_ByteArray_decEq___boxed(lean_object* v_lhs_13_, lean_object* v_rhs_14_){
_start:
{
uint8_t v_res_15_; lean_object* v_r_16_; 
v_res_15_ = lean_sarray_dec_eq(v_lhs_13_, v_rhs_14_);
lean_dec_ref(v_rhs_14_);
lean_dec_ref(v_lhs_13_);
v_r_16_ = lean_box(v_res_15_);
return v_r_16_;
}
}
uint8_t l_ByteArray_instDecidableEq(lean_object* v_lhs_17_, lean_object* v_rhs_18_){
_start:
{
uint8_t v___x_19_; 
v___x_19_ = lean_sarray_dec_eq(v_lhs_17_, v_rhs_18_);
return v___x_19_;
}
}
LEAN_EXPORT void l_ByteArray_instDecidableEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_lhs_17_ = stack[0].m_obj;
lean_object* v_rhs_18_ = stack[1].m_obj;
uint8_t v_res_20_;
v_res_20_ = l_ByteArray_instDecidableEq(v_lhs_17_, v_rhs_18_);
stack->m_num = v_res_20_;
}
LEAN_EXPORT lean_object* l_ByteArray_instDecidableEq___boxed(lean_object* v_lhs_21_, lean_object* v_rhs_22_){
_start:
{
uint8_t v_res_23_; lean_object* v_r_24_; 
v_res_23_ = l_ByteArray_instDecidableEq(v_lhs_21_, v_rhs_22_);
lean_dec_ref(v_rhs_22_);
lean_dec_ref(v_lhs_21_);
v_r_24_ = lean_box(v_res_23_);
return v_r_24_;
}
}
static lean_object* _init_l_ByteArray_instInhabited(void){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = l_ByteArray_empty;
return v___x_25_;
}
}
static lean_object* _init_l_ByteArray_instEmptyCollection(void){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = l_ByteArray_empty;
return v___x_26_;
}
}
LEAN_EXPORT void l_ByteArray_usize_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_27_ = stack[0].m_obj;
size_t v_res_28_;
v_res_28_ = lean_sarray_size(v_a_27_);
stack->m_num = v_res_28_;
}
LEAN_EXPORT lean_object* l_ByteArray_usize___boxed(lean_object* v_a_29_){
_start:
{
size_t v_res_30_; lean_object* v_r_31_; 
v_res_30_ = lean_sarray_size(v_a_29_);
lean_dec_ref(v_a_29_);
v_r_31_ = lean_box_usize(v_res_30_);
return v_r_31_;
}
}
static lean_object* _init_l_ByteArray_uget___auto__1___closed__13(void){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_56_ = ((lean_object*)(l_ByteArray_uget___auto__1___closed__12));
v___x_57_ = l_Lean_mkAtom(v___x_56_);
return v___x_57_;
}
}
static lean_object* _init_l_ByteArray_uget___auto__1___closed__14(void){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_58_ = lean_obj_once(&l_ByteArray_uget___auto__1___closed__13, &l_ByteArray_uget___auto__1___closed__13_once, _init_l_ByteArray_uget___auto__1___closed__13);
v___x_59_ = ((lean_object*)(l_ByteArray_uget___auto__1___closed__5));
v___x_60_ = lean_array_push(v___x_59_, v___x_58_);
return v___x_60_;
}
}
static lean_object* _init_l_ByteArray_uget___auto__1___closed__15(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_61_ = lean_obj_once(&l_ByteArray_uget___auto__1___closed__14, &l_ByteArray_uget___auto__1___closed__14_once, _init_l_ByteArray_uget___auto__1___closed__14);
v___x_62_ = ((lean_object*)(l_ByteArray_uget___auto__1___closed__11));
v___x_63_ = lean_box(2);
v___x_64_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_64_, 0, v___x_63_);
lean_ctor_set(v___x_64_, 1, v___x_62_);
lean_ctor_set(v___x_64_, 2, v___x_61_);
return v___x_64_;
}
}
static lean_object* _init_l_ByteArray_uget___auto__1___closed__16(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_65_ = lean_obj_once(&l_ByteArray_uget___auto__1___closed__15, &l_ByteArray_uget___auto__1___closed__15_once, _init_l_ByteArray_uget___auto__1___closed__15);
v___x_66_ = ((lean_object*)(l_ByteArray_uget___auto__1___closed__5));
v___x_67_ = lean_array_push(v___x_66_, v___x_65_);
return v___x_67_;
}
}
static lean_object* _init_l_ByteArray_uget___auto__1___closed__17(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_68_ = lean_obj_once(&l_ByteArray_uget___auto__1___closed__16, &l_ByteArray_uget___auto__1___closed__16_once, _init_l_ByteArray_uget___auto__1___closed__16);
v___x_69_ = ((lean_object*)(l_ByteArray_uget___auto__1___closed__9));
v___x_70_ = lean_box(2);
v___x_71_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
lean_ctor_set(v___x_71_, 1, v___x_69_);
lean_ctor_set(v___x_71_, 2, v___x_68_);
return v___x_71_;
}
}
static lean_object* _init_l_ByteArray_uget___auto__1___closed__18(void){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_72_ = lean_obj_once(&l_ByteArray_uget___auto__1___closed__17, &l_ByteArray_uget___auto__1___closed__17_once, _init_l_ByteArray_uget___auto__1___closed__17);
v___x_73_ = ((lean_object*)(l_ByteArray_uget___auto__1___closed__5));
v___x_74_ = lean_array_push(v___x_73_, v___x_72_);
return v___x_74_;
}
}
static lean_object* _init_l_ByteArray_uget___auto__1___closed__19(void){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_75_ = lean_obj_once(&l_ByteArray_uget___auto__1___closed__18, &l_ByteArray_uget___auto__1___closed__18_once, _init_l_ByteArray_uget___auto__1___closed__18);
v___x_76_ = ((lean_object*)(l_ByteArray_uget___auto__1___closed__7));
v___x_77_ = lean_box(2);
v___x_78_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
lean_ctor_set(v___x_78_, 1, v___x_76_);
lean_ctor_set(v___x_78_, 2, v___x_75_);
return v___x_78_;
}
}
static lean_object* _init_l_ByteArray_uget___auto__1___closed__20(void){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_79_ = lean_obj_once(&l_ByteArray_uget___auto__1___closed__19, &l_ByteArray_uget___auto__1___closed__19_once, _init_l_ByteArray_uget___auto__1___closed__19);
v___x_80_ = ((lean_object*)(l_ByteArray_uget___auto__1___closed__5));
v___x_81_ = lean_array_push(v___x_80_, v___x_79_);
return v___x_81_;
}
}
static lean_object* _init_l_ByteArray_uget___auto__1___closed__21(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_82_ = lean_obj_once(&l_ByteArray_uget___auto__1___closed__20, &l_ByteArray_uget___auto__1___closed__20_once, _init_l_ByteArray_uget___auto__1___closed__20);
v___x_83_ = ((lean_object*)(l_ByteArray_uget___auto__1___closed__4));
v___x_84_ = lean_box(2);
v___x_85_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_85_, 0, v___x_84_);
lean_ctor_set(v___x_85_, 1, v___x_83_);
lean_ctor_set(v___x_85_, 2, v___x_82_);
return v___x_85_;
}
}
static lean_object* _init_l_ByteArray_uget___auto__1(void){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = lean_obj_once(&l_ByteArray_uget___auto__1___closed__21, &l_ByteArray_uget___auto__1___closed__21_once, _init_l_ByteArray_uget___auto__1___closed__21);
return v___x_86_;
}
}
LEAN_EXPORT void l_ByteArray_uget_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_87_ = stack[0].m_obj;
size_t v_i_88_ = stack[1].m_num;
uint8_t v_res_90_;
v_res_90_ = lean_byte_array_uget(v_a_87_, v_i_88_);
stack->m_num = v_res_90_;
}
LEAN_EXPORT lean_object* l_ByteArray_uget___boxed(lean_object* v_a_91_, lean_object* v_i_92_, lean_object* v_h_93_){
_start:
{
size_t v_i_boxed_94_; uint8_t v_res_95_; lean_object* v_r_96_; 
v_i_boxed_94_ = lean_unbox_usize(v_i_92_);
lean_dec(v_i_92_);
v_res_95_ = lean_byte_array_uget(v_a_91_, v_i_boxed_94_);
lean_dec_ref(v_a_91_);
v_r_96_ = lean_box(v_res_95_);
return v_r_96_;
}
}
LEAN_EXPORT void l_ByteArray_get_x21_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_97_ = stack[0].m_obj;
lean_object* v_a_00___x40___internal___hyg_98_ = stack[1].m_obj;
uint8_t v_res_99_;
v_res_99_ = lean_byte_array_get(v_a_00___x40___internal___hyg_97_, v_a_00___x40___internal___hyg_98_);
stack->m_num = v_res_99_;
}
LEAN_EXPORT lean_object* l_ByteArray_get_x21___boxed(lean_object* v_a_00___x40___internal___hyg_100_, lean_object* v_a_00___x40___internal___hyg_101_){
_start:
{
uint8_t v_res_102_; lean_object* v_r_103_; 
v_res_102_ = lean_byte_array_get(v_a_00___x40___internal___hyg_100_, v_a_00___x40___internal___hyg_101_);
lean_dec(v_a_00___x40___internal___hyg_101_);
lean_dec_ref(v_a_00___x40___internal___hyg_100_);
v_r_103_ = lean_box(v_res_102_);
return v_r_103_;
}
}
static lean_object* _init_l_ByteArray_get___auto__1(void){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = lean_obj_once(&l_ByteArray_uget___auto__1___closed__21, &l_ByteArray_uget___auto__1___closed__21_once, _init_l_ByteArray_uget___auto__1___closed__21);
return v___x_104_;
}
}
LEAN_EXPORT void l_ByteArray_get_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_105_ = stack[0].m_obj;
lean_object* v_i_106_ = stack[1].m_obj;
uint8_t v_res_108_;
v_res_108_ = lean_byte_array_fget(v_a_105_, v_i_106_);
stack->m_num = v_res_108_;
}
LEAN_EXPORT lean_object* l_ByteArray_get___boxed(lean_object* v_a_109_, lean_object* v_i_110_, lean_object* v_h_111_){
_start:
{
uint8_t v_res_112_; lean_object* v_r_113_; 
v_res_112_ = lean_byte_array_fget(v_a_109_, v_i_110_);
lean_dec(v_i_110_);
lean_dec_ref(v_a_109_);
v_r_113_ = lean_box(v_res_112_);
return v_r_113_;
}
}
uint8_t l_ByteArray_instGetElemNatUInt8LtSize___lam__0(lean_object* v_xs_114_, lean_object* v_i_115_, lean_object* v_h_116_){
_start:
{
uint8_t v___x_117_; 
v___x_117_ = lean_byte_array_fget(v_xs_114_, v_i_115_);
return v___x_117_;
}
}
LEAN_EXPORT void l_ByteArray_instGetElemNatUInt8LtSize___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_114_ = stack[0].m_obj;
lean_object* v_i_115_ = stack[1].m_obj;
uint8_t v_res_118_;
v_res_118_ = l_ByteArray_instGetElemNatUInt8LtSize___lam__0(v_xs_114_, v_i_115_, lean_box(0));
stack->m_num = v_res_118_;
}
LEAN_EXPORT lean_object* l_ByteArray_instGetElemNatUInt8LtSize___lam__0___boxed(lean_object* v_xs_119_, lean_object* v_i_120_, lean_object* v_h_121_){
_start:
{
uint8_t v_res_122_; lean_object* v_r_123_; 
v_res_122_ = l_ByteArray_instGetElemNatUInt8LtSize___lam__0(v_xs_119_, v_i_120_, v_h_121_);
lean_dec(v_i_120_);
lean_dec_ref(v_xs_119_);
v_r_123_ = lean_box(v_res_122_);
return v_r_123_;
}
}
uint8_t l_ByteArray_instGetElemUSizeUInt8LtNatValToFinSize___lam__0(lean_object* v_xs_126_, size_t v_i_127_, lean_object* v_h_128_){
_start:
{
uint8_t v___x_129_; 
v___x_129_ = lean_byte_array_uget(v_xs_126_, v_i_127_);
return v___x_129_;
}
}
LEAN_EXPORT void l_ByteArray_instGetElemUSizeUInt8LtNatValToFinSize___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_126_ = stack[0].m_obj;
size_t v_i_127_ = stack[1].m_num;
uint8_t v_res_130_;
v_res_130_ = l_ByteArray_instGetElemUSizeUInt8LtNatValToFinSize___lam__0(v_xs_126_, v_i_127_, lean_box(0));
stack->m_num = v_res_130_;
}
LEAN_EXPORT lean_object* l_ByteArray_instGetElemUSizeUInt8LtNatValToFinSize___lam__0___boxed(lean_object* v_xs_131_, lean_object* v_i_132_, lean_object* v_h_133_){
_start:
{
size_t v_i_boxed_134_; uint8_t v_res_135_; lean_object* v_r_136_; 
v_i_boxed_134_ = lean_unbox_usize(v_i_132_);
lean_dec(v_i_132_);
v_res_135_ = l_ByteArray_instGetElemUSizeUInt8LtNatValToFinSize___lam__0(v_xs_131_, v_i_boxed_134_, v_h_133_);
lean_dec_ref(v_xs_131_);
v_r_136_ = lean_box(v_res_135_);
return v_r_136_;
}
}
LEAN_EXPORT void l_ByteArray_set_x21_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_139_ = stack[0].m_obj;
lean_object* v_a_00___x40___internal___hyg_140_ = stack[1].m_obj;
uint8_t v_a_00___x40___internal___hyg_141_ = stack[2].m_num;
lean_object* v_res_142_;
v_res_142_ = lean_byte_array_set(v_a_00___x40___internal___hyg_139_, v_a_00___x40___internal___hyg_140_, v_a_00___x40___internal___hyg_141_);
stack->m_obj
 = v_res_142_;
}
LEAN_EXPORT lean_object* l_ByteArray_set_x21___boxed(lean_object* v_a_00___x40___internal___hyg_143_, lean_object* v_a_00___x40___internal___hyg_144_, lean_object* v_a_00___x40___internal___hyg_145_){
_start:
{
uint8_t v_a_00___x40___internal___hyg_3__boxed_146_; lean_object* v_res_147_; 
v_a_00___x40___internal___hyg_3__boxed_146_ = lean_unbox(v_a_00___x40___internal___hyg_145_);
v_res_147_ = lean_byte_array_set(v_a_00___x40___internal___hyg_143_, v_a_00___x40___internal___hyg_144_, v_a_00___x40___internal___hyg_3__boxed_146_);
lean_dec(v_a_00___x40___internal___hyg_144_);
return v_res_147_;
}
}
static lean_object* _init_l_ByteArray_set___auto__1(void){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = lean_obj_once(&l_ByteArray_uget___auto__1___closed__21, &l_ByteArray_uget___auto__1___closed__21_once, _init_l_ByteArray_uget___auto__1___closed__21);
return v___x_148_;
}
}
LEAN_EXPORT void l_ByteArray_set_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_149_ = stack[0].m_obj;
lean_object* v_i_150_ = stack[1].m_obj;
uint8_t v_a_00___x40___internal___hyg_151_ = stack[2].m_num;
lean_object* v_res_153_;
v_res_153_ = lean_byte_array_fset(v_a_149_, v_i_150_, v_a_00___x40___internal___hyg_151_);
stack->m_obj
 = v_res_153_;
}
LEAN_EXPORT lean_object* l_ByteArray_set___boxed(lean_object* v_a_154_, lean_object* v_i_155_, lean_object* v_a_00___x40___internal___hyg_156_, lean_object* v_h_157_){
_start:
{
uint8_t v_a_00___x40___internal___hyg_1__boxed_158_; lean_object* v_res_159_; 
v_a_00___x40___internal___hyg_1__boxed_158_ = lean_unbox(v_a_00___x40___internal___hyg_156_);
v_res_159_ = lean_byte_array_fset(v_a_154_, v_i_155_, v_a_00___x40___internal___hyg_1__boxed_158_);
lean_dec(v_i_155_);
return v_res_159_;
}
}
static lean_object* _init_l_ByteArray_uset___auto__1(void){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = lean_obj_once(&l_ByteArray_uget___auto__1___closed__21, &l_ByteArray_uget___auto__1___closed__21_once, _init_l_ByteArray_uget___auto__1___closed__21);
return v___x_160_;
}
}
LEAN_EXPORT void l_ByteArray_uset_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_161_ = stack[0].m_obj;
size_t v_i_162_ = stack[1].m_num;
uint8_t v_a_00___x40___internal___hyg_163_ = stack[2].m_num;
lean_object* v_res_165_;
v_res_165_ = lean_byte_array_uset(v_a_161_, v_i_162_, v_a_00___x40___internal___hyg_163_);
stack->m_obj
 = v_res_165_;
}
LEAN_EXPORT lean_object* l_ByteArray_uset___boxed(lean_object* v_a_166_, lean_object* v_i_167_, lean_object* v_a_00___x40___internal___hyg_168_, lean_object* v_h_169_){
_start:
{
size_t v_i_boxed_170_; uint8_t v_a_00___x40___internal___hyg_1__boxed_171_; lean_object* v_res_172_; 
v_i_boxed_170_ = lean_unbox_usize(v_i_167_);
lean_dec(v_i_167_);
v_a_00___x40___internal___hyg_1__boxed_171_ = lean_unbox(v_a_00___x40___internal___hyg_168_);
v_res_172_ = lean_byte_array_uset(v_a_166_, v_i_boxed_170_, v_a_00___x40___internal___hyg_1__boxed_171_);
return v_res_172_;
}
}
LEAN_EXPORT void l_ByteArray_markLinear_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_173_ = stack[0].m_obj;
lean_object* v_res_174_;
v_res_174_ = lean_sarray_mark_linear(v_a_173_);
stack->m_obj
 = v_res_174_;
}
LEAN_EXPORT lean_object* l_ByteArray_markLinear___boxed(lean_object* v_a_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = lean_sarray_mark_linear(v_a_175_);
return v_res_176_;
}
}
LEAN_EXPORT void l_ByteArray_propagateMark_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_177_ = stack[0].m_obj;
lean_object* v_b_178_ = stack[1].m_obj;
lean_object* v_res_179_;
v_res_179_ = lean_sarray_propagate_mark(v_a_177_, v_b_178_);
stack->m_obj
 = v_res_179_;
}
LEAN_EXPORT lean_object* l_ByteArray_propagateMark___boxed(lean_object* v_a_180_, lean_object* v_b_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = lean_sarray_propagate_mark(v_a_180_, v_b_181_);
lean_dec_ref(v_a_180_);
return v_res_182_;
}
}
LEAN_EXPORT void l_ByteArray_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_183_ = stack[0].m_obj;
uint64_t v_res_184_;
v_res_184_ = lean_byte_array_hash(v_a_183_);
stack->m_num = v_res_184_;
}
LEAN_EXPORT lean_object* l_ByteArray_hash___boxed(lean_object* v_a_185_){
_start:
{
uint64_t v_res_186_; lean_object* v_r_187_; 
v_res_186_ = lean_byte_array_hash(v_a_185_);
lean_dec_ref(v_a_185_);
v_r_187_ = lean_box_uint64(v_res_186_);
return v_r_187_;
}
}
uint8_t l_ByteArray_isEmpty(lean_object* v_s_190_){
_start:
{
lean_object* v___x_191_; lean_object* v___x_192_; uint8_t v___x_193_; 
v___x_191_ = lean_byte_array_size(v_s_190_);
v___x_192_ = lean_unsigned_to_nat(0u);
v___x_193_ = lean_nat_dec_eq(v___x_191_, v___x_192_);
return v___x_193_;
}
}
LEAN_EXPORT void l_ByteArray_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_190_ = stack[0].m_obj;
uint8_t v_res_194_;
v_res_194_ = l_ByteArray_isEmpty(v_s_190_);
stack->m_num = v_res_194_;
}
LEAN_EXPORT lean_object* l_ByteArray_isEmpty___boxed(lean_object* v_s_195_){
_start:
{
uint8_t v_res_196_; lean_object* v_r_197_; 
v_res_196_ = l_ByteArray_isEmpty(v_s_195_);
lean_dec_ref(v_s_195_);
v_r_197_ = lean_box(v_res_196_);
return v_r_197_;
}
}
LEAN_EXPORT void l_ByteArray_copySlice_0interp(lean_interpreter_value* stack)
{
lean_object* v_src_198_ = stack[0].m_obj;
lean_object* v_srcOff_199_ = stack[1].m_obj;
lean_object* v_dest_200_ = stack[2].m_obj;
lean_object* v_destOff_201_ = stack[3].m_obj;
lean_object* v_len_202_ = stack[4].m_obj;
uint8_t v_exact_203_ = stack[5].m_num;
lean_object* v_res_204_;
v_res_204_ = lean_byte_array_copy_slice(v_src_198_, v_srcOff_199_, v_dest_200_, v_destOff_201_, v_len_202_, v_exact_203_);
stack->m_obj
 = v_res_204_;
}
LEAN_EXPORT lean_object* l_ByteArray_copySlice___boxed(lean_object* v_src_205_, lean_object* v_srcOff_206_, lean_object* v_dest_207_, lean_object* v_destOff_208_, lean_object* v_len_209_, lean_object* v_exact_210_){
_start:
{
uint8_t v_exact_boxed_211_; lean_object* v_res_212_; 
v_exact_boxed_211_ = lean_unbox(v_exact_210_);
v_res_212_ = lean_byte_array_copy_slice(v_src_205_, v_srcOff_206_, v_dest_207_, v_destOff_208_, v_len_209_, v_exact_boxed_211_);
lean_dec_ref(v_src_205_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_extract(lean_object* v_a_213_, lean_object* v_b_214_, lean_object* v_e_215_){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; uint8_t v___x_219_; lean_object* v___x_220_; 
v___x_216_ = l_ByteArray_empty;
v___x_217_ = lean_unsigned_to_nat(0u);
v___x_218_ = lean_nat_sub(v_e_215_, v_b_214_);
v___x_219_ = 1;
v___x_220_ = lean_byte_array_copy_slice(v_a_213_, v_b_214_, v___x_216_, v___x_217_, v___x_218_, v___x_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_extract___boxed(lean_object* v_a_221_, lean_object* v_b_222_, lean_object* v_e_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l_ByteArray_extract(v_a_221_, v_b_222_, v_e_223_);
lean_dec(v_e_223_);
lean_dec_ref(v_a_221_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_fastAppend(lean_object* v_a_225_, lean_object* v_b_226_){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; uint8_t v___x_230_; lean_object* v___x_231_; 
v___x_227_ = lean_unsigned_to_nat(0u);
v___x_228_ = lean_byte_array_size(v_a_225_);
v___x_229_ = lean_byte_array_size(v_b_226_);
v___x_230_ = 0;
v___x_231_ = lean_byte_array_copy_slice(v_b_226_, v___x_227_, v_a_225_, v___x_228_, v___x_229_, v___x_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_fastAppend___boxed(lean_object* v_a_232_, lean_object* v_b_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_ByteArray_fastAppend(v_a_232_, v_b_233_);
lean_dec_ref(v_b_233_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_toList_loop(lean_object* v_bs_237_, lean_object* v_i_238_, lean_object* v_r_239_){
_start:
{
lean_object* v___x_240_; uint8_t v___x_241_; 
v___x_240_ = lean_byte_array_size(v_bs_237_);
v___x_241_ = lean_nat_dec_lt(v_i_238_, v___x_240_);
if (v___x_241_ == 0)
{
lean_object* v___x_242_; 
lean_dec(v_i_238_);
v___x_242_ = l_List_reverse___redArg(v_r_239_);
return v___x_242_;
}
else
{
lean_object* v___x_243_; lean_object* v___x_244_; uint8_t v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_243_ = lean_unsigned_to_nat(1u);
v___x_244_ = lean_nat_add(v_i_238_, v___x_243_);
v___x_245_ = lean_byte_array_get(v_bs_237_, v_i_238_);
lean_dec(v_i_238_);
v___x_246_ = lean_box(v___x_245_);
v___x_247_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
lean_ctor_set(v___x_247_, 1, v_r_239_);
v_i_238_ = v___x_244_;
v_r_239_ = v___x_247_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_toList_loop___boxed(lean_object* v_bs_249_, lean_object* v_i_250_, lean_object* v_r_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_ByteArray_toList_loop(v_bs_249_, v_i_250_, v_r_251_);
lean_dec_ref(v_bs_249_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_toList(lean_object* v_bs_253_){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_254_ = lean_unsigned_to_nat(0u);
v___x_255_ = lean_box(0);
v___x_256_ = l_ByteArray_toList_loop(v_bs_253_, v___x_254_, v___x_255_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_toList___boxed(lean_object* v_bs_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_ByteArray_toList(v_bs_257_);
lean_dec_ref(v_bs_257_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findFinIdx_x3f_loop(lean_object* v_a_259_, lean_object* v_p_260_, lean_object* v_i_261_){
_start:
{
lean_object* v___x_262_; uint8_t v___x_263_; 
v___x_262_ = lean_byte_array_size(v_a_259_);
v___x_263_ = lean_nat_dec_lt(v_i_261_, v___x_262_);
if (v___x_263_ == 0)
{
lean_object* v___x_264_; 
lean_dec(v_i_261_);
lean_dec_ref(v_p_260_);
v___x_264_ = lean_box(0);
return v___x_264_;
}
else
{
uint8_t v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; uint8_t v___x_268_; 
v___x_265_ = lean_byte_array_fget(v_a_259_, v_i_261_);
v___x_266_ = lean_box(v___x_265_);
lean_inc_ref(v_p_260_);
v___x_267_ = lean_apply_1(v_p_260_, v___x_266_);
v___x_268_ = lean_unbox(v___x_267_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_269_ = lean_unsigned_to_nat(1u);
v___x_270_ = lean_nat_add(v_i_261_, v___x_269_);
lean_dec(v_i_261_);
v_i_261_ = v___x_270_;
goto _start;
}
else
{
lean_object* v___x_272_; 
lean_dec_ref(v_p_260_);
v___x_272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_272_, 0, v_i_261_);
return v___x_272_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_findFinIdx_x3f_loop___boxed(lean_object* v_a_273_, lean_object* v_p_274_, lean_object* v_i_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_ByteArray_findFinIdx_x3f_loop(v_a_273_, v_p_274_, v_i_275_);
lean_dec_ref(v_a_273_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findFinIdx_x3f(lean_object* v_a_277_, lean_object* v_p_278_, lean_object* v_start_279_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = l_ByteArray_findFinIdx_x3f_loop(v_a_277_, v_p_278_, v_start_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findFinIdx_x3f___boxed(lean_object* v_a_281_, lean_object* v_p_282_, lean_object* v_start_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_ByteArray_findFinIdx_x3f(v_a_281_, v_p_282_, v_start_283_);
lean_dec_ref(v_a_281_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop(lean_object* v_a_285_, lean_object* v_p_286_, lean_object* v_i_287_){
_start:
{
lean_object* v___x_288_; uint8_t v___x_289_; 
v___x_288_ = lean_byte_array_size(v_a_285_);
v___x_289_ = lean_nat_dec_lt(v_i_287_, v___x_288_);
if (v___x_289_ == 0)
{
lean_object* v___x_290_; 
lean_dec(v_i_287_);
lean_dec_ref(v_p_286_);
v___x_290_ = lean_box(0);
return v___x_290_;
}
else
{
uint8_t v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_291_ = lean_byte_array_fget(v_a_285_, v_i_287_);
v___x_292_ = lean_box(v___x_291_);
lean_inc_ref(v_p_286_);
v___x_293_ = lean_apply_1(v_p_286_, v___x_292_);
v___x_294_ = lean_unbox(v___x_293_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = lean_unsigned_to_nat(1u);
v___x_296_ = lean_nat_add(v_i_287_, v___x_295_);
lean_dec(v_i_287_);
v_i_287_ = v___x_296_;
goto _start;
}
else
{
lean_object* v___x_298_; 
lean_dec_ref(v_p_286_);
v___x_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_298_, 0, v_i_287_);
return v___x_298_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___boxed(lean_object* v_a_299_, lean_object* v_p_300_, lean_object* v_i_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_ByteArray_findIdx_x3f_loop(v_a_299_, v_p_300_, v_i_301_);
lean_dec_ref(v_a_299_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f(lean_object* v_a_303_, lean_object* v_p_304_, lean_object* v_start_305_){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = l_ByteArray_findIdx_x3f_loop(v_a_303_, v_p_304_, v_start_305_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f___boxed(lean_object* v_a_307_, lean_object* v_p_308_, lean_object* v_start_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_ByteArray_findIdx_x3f(v_a_307_, v_p_308_, v_start_309_);
lean_dec_ref(v_a_307_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe_loop___redArg___lam__0___boxed(lean_object* v_toPure_311_, lean_object* v_i_312_, lean_object* v_inst_313_, lean_object* v_as_314_, lean_object* v_f_315_, lean_object* v_sz_316_, lean_object* v_____do__lift_317_){
_start:
{
size_t v_i_boxed_318_; size_t v_sz_boxed_319_; lean_object* v_res_320_; 
v_i_boxed_318_ = lean_unbox_usize(v_i_312_);
lean_dec(v_i_312_);
v_sz_boxed_319_ = lean_unbox_usize(v_sz_316_);
lean_dec(v_sz_316_);
v_res_320_ = l_ByteArray_forInUnsafe_loop___redArg___lam__0(v_toPure_311_, v_i_boxed_318_, v_inst_313_, v_as_314_, v_f_315_, v_sz_boxed_319_, v_____do__lift_317_);
return v_res_320_;
}
}
lean_object* l_ByteArray_forInUnsafe_loop___redArg(lean_object* v_inst_321_, lean_object* v_as_322_, lean_object* v_f_323_, size_t v_sz_324_, size_t v_i_325_, lean_object* v_b_326_){
_start:
{
lean_object* v_toApplicative_327_; lean_object* v_toBind_328_; lean_object* v_toPure_329_; uint8_t v___x_330_; 
v_toApplicative_327_ = lean_ctor_get(v_inst_321_, 0);
v_toBind_328_ = lean_ctor_get(v_inst_321_, 1);
lean_inc(v_toBind_328_);
v_toPure_329_ = lean_ctor_get(v_toApplicative_327_, 1);
lean_inc(v_toPure_329_);
v___x_330_ = lean_usize_dec_lt(v_i_325_, v_sz_324_);
if (v___x_330_ == 0)
{
lean_object* v___x_331_; 
lean_dec(v_toBind_328_);
lean_dec(v_f_323_);
lean_dec_ref(v_as_322_);
lean_dec_ref(v_inst_321_);
v___x_331_ = lean_apply_2(v_toPure_329_, lean_box(0), v_b_326_);
return v___x_331_;
}
else
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___f_334_; uint8_t v_a_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_332_ = lean_box_usize(v_i_325_);
v___x_333_ = lean_box_usize(v_sz_324_);
lean_inc(v_f_323_);
lean_inc_ref(v_as_322_);
v___f_334_ = lean_alloc_closure((void*)(l_ByteArray_forInUnsafe_loop___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_334_, 0, v_toPure_329_);
lean_closure_set(v___f_334_, 1, v___x_332_);
lean_closure_set(v___f_334_, 2, v_inst_321_);
lean_closure_set(v___f_334_, 3, v_as_322_);
lean_closure_set(v___f_334_, 4, v_f_323_);
lean_closure_set(v___f_334_, 5, v___x_333_);
v_a_335_ = lean_byte_array_uget(v_as_322_, v_i_325_);
lean_dec_ref(v_as_322_);
v___x_336_ = lean_box(v_a_335_);
v___x_337_ = lean_apply_2(v_f_323_, v___x_336_, v_b_326_);
v___x_338_ = lean_apply_4(v_toBind_328_, lean_box(0), lean_box(0), v___x_337_, v___f_334_);
return v___x_338_;
}
}
}
LEAN_EXPORT void l_ByteArray_forInUnsafe_loop___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_321_ = stack[0].m_obj;
lean_object* v_as_322_ = stack[1].m_obj;
lean_object* v_f_323_ = stack[2].m_obj;
size_t v_sz_324_ = stack[3].m_num;
size_t v_i_325_ = stack[4].m_num;
lean_object* v_b_326_ = stack[5].m_obj;
lean_object* v_res_339_;
v_res_339_ = l_ByteArray_forInUnsafe_loop___redArg(v_inst_321_, v_as_322_, v_f_323_, v_sz_324_, v_i_325_, v_b_326_);
stack->m_obj
 = v_res_339_;
}
lean_object* l_ByteArray_forInUnsafe_loop___redArg___lam__0(lean_object* v_toPure_340_, size_t v_i_341_, lean_object* v_inst_342_, lean_object* v_as_343_, lean_object* v_f_344_, size_t v_sz_345_, lean_object* v_____do__lift_346_){
_start:
{
if (lean_obj_tag(v_____do__lift_346_) == 0)
{
lean_object* v_a_347_; lean_object* v___x_348_; 
lean_dec(v_f_344_);
lean_dec_ref(v_as_343_);
lean_dec_ref(v_inst_342_);
v_a_347_ = lean_ctor_get(v_____do__lift_346_, 0);
lean_inc(v_a_347_);
lean_dec_ref_known(v_____do__lift_346_, 1);
v___x_348_ = lean_apply_2(v_toPure_340_, lean_box(0), v_a_347_);
return v___x_348_;
}
else
{
lean_object* v_a_349_; size_t v___x_350_; size_t v___x_351_; lean_object* v___x_352_; 
lean_dec(v_toPure_340_);
v_a_349_ = lean_ctor_get(v_____do__lift_346_, 0);
lean_inc(v_a_349_);
lean_dec_ref_known(v_____do__lift_346_, 1);
v___x_350_ = ((size_t)1ULL);
v___x_351_ = lean_usize_add(v_i_341_, v___x_350_);
v___x_352_ = l_ByteArray_forInUnsafe_loop___redArg(v_inst_342_, v_as_343_, v_f_344_, v_sz_345_, v___x_351_, v_a_349_);
return v___x_352_;
}
}
}
LEAN_EXPORT void l_ByteArray_forInUnsafe_loop___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_340_ = stack[0].m_obj;
size_t v_i_341_ = stack[1].m_num;
lean_object* v_inst_342_ = stack[2].m_obj;
lean_object* v_as_343_ = stack[3].m_obj;
lean_object* v_f_344_ = stack[4].m_obj;
size_t v_sz_345_ = stack[5].m_num;
lean_object* v_____do__lift_346_ = stack[6].m_obj;
lean_object* v_res_353_;
v_res_353_ = l_ByteArray_forInUnsafe_loop___redArg___lam__0(v_toPure_340_, v_i_341_, v_inst_342_, v_as_343_, v_f_344_, v_sz_345_, v_____do__lift_346_);
stack->m_obj
 = v_res_353_;
}
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe_loop___redArg___boxed(lean_object* v_inst_354_, lean_object* v_as_355_, lean_object* v_f_356_, lean_object* v_sz_357_, lean_object* v_i_358_, lean_object* v_b_359_){
_start:
{
size_t v_sz_boxed_360_; size_t v_i_boxed_361_; lean_object* v_res_362_; 
v_sz_boxed_360_ = lean_unbox_usize(v_sz_357_);
lean_dec(v_sz_357_);
v_i_boxed_361_ = lean_unbox_usize(v_i_358_);
lean_dec(v_i_358_);
v_res_362_ = l_ByteArray_forInUnsafe_loop___redArg(v_inst_354_, v_as_355_, v_f_356_, v_sz_boxed_360_, v_i_boxed_361_, v_b_359_);
return v_res_362_;
}
}
lean_object* l_ByteArray_forInUnsafe_loop(lean_object* v_00_u03b2_363_, lean_object* v_m_364_, lean_object* v_inst_365_, lean_object* v_as_366_, lean_object* v_f_367_, size_t v_sz_368_, size_t v_i_369_, lean_object* v_b_370_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = l_ByteArray_forInUnsafe_loop___redArg(v_inst_365_, v_as_366_, v_f_367_, v_sz_368_, v_i_369_, v_b_370_);
return v___x_371_;
}
}
LEAN_EXPORT void l_ByteArray_forInUnsafe_loop_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_365_ = stack[2].m_obj;
lean_object* v_as_366_ = stack[3].m_obj;
lean_object* v_f_367_ = stack[4].m_obj;
size_t v_sz_368_ = stack[5].m_num;
size_t v_i_369_ = stack[6].m_num;
lean_object* v_b_370_ = stack[7].m_obj;
lean_object* v_res_372_;
v_res_372_ = l_ByteArray_forInUnsafe_loop(lean_box(0), lean_box(0), v_inst_365_, v_as_366_, v_f_367_, v_sz_368_, v_i_369_, v_b_370_);
stack->m_obj
 = v_res_372_;
}
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe_loop___boxed(lean_object* v_00_u03b2_373_, lean_object* v_m_374_, lean_object* v_inst_375_, lean_object* v_as_376_, lean_object* v_f_377_, lean_object* v_sz_378_, lean_object* v_i_379_, lean_object* v_b_380_){
_start:
{
size_t v_sz_boxed_381_; size_t v_i_boxed_382_; lean_object* v_res_383_; 
v_sz_boxed_381_ = lean_unbox_usize(v_sz_378_);
lean_dec(v_sz_378_);
v_i_boxed_382_ = lean_unbox_usize(v_i_379_);
lean_dec(v_i_379_);
v_res_383_ = l_ByteArray_forInUnsafe_loop(v_00_u03b2_373_, v_m_374_, v_inst_375_, v_as_376_, v_f_377_, v_sz_boxed_381_, v_i_boxed_382_, v_b_380_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe___redArg(lean_object* v_inst_384_, lean_object* v_as_385_, lean_object* v_b_386_, lean_object* v_f_387_){
_start:
{
size_t v_sz_388_; size_t v___x_389_; lean_object* v___x_390_; 
v_sz_388_ = lean_sarray_size(v_as_385_);
v___x_389_ = ((size_t)0ULL);
v___x_390_ = l_ByteArray_forInUnsafe_loop___redArg(v_inst_384_, v_as_385_, v_f_387_, v_sz_388_, v___x_389_, v_b_386_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe(lean_object* v_00_u03b2_391_, lean_object* v_m_392_, lean_object* v_inst_393_, lean_object* v_as_394_, lean_object* v_b_395_, lean_object* v_f_396_){
_start:
{
size_t v_sz_397_; size_t v___x_398_; lean_object* v___x_399_; 
v_sz_397_ = lean_sarray_size(v_as_394_);
v___x_398_ = ((size_t)0ULL);
v___x_399_ = l_ByteArray_forInUnsafe_loop___redArg(v_inst_393_, v_as_394_, v_f_396_, v_sz_397_, v___x_398_, v_b_395_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_forIn_loop___redArg___lam__0___boxed(lean_object* v_toPure_400_, lean_object* v_inst_401_, lean_object* v_as_402_, lean_object* v_f_403_, lean_object* v_n_404_, lean_object* v_____do__lift_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_ByteArray_forIn_loop___redArg___lam__0(v_toPure_400_, v_inst_401_, v_as_402_, v_f_403_, v_n_404_, v_____do__lift_405_);
lean_dec(v_n_404_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_forIn_loop___redArg(lean_object* v_inst_407_, lean_object* v_as_408_, lean_object* v_f_409_, lean_object* v_i_410_, lean_object* v_b_411_){
_start:
{
lean_object* v_toApplicative_412_; lean_object* v_toBind_413_; lean_object* v_toPure_414_; lean_object* v_zero_415_; uint8_t v_isZero_416_; 
v_toApplicative_412_ = lean_ctor_get(v_inst_407_, 0);
v_toBind_413_ = lean_ctor_get(v_inst_407_, 1);
lean_inc(v_toBind_413_);
v_toPure_414_ = lean_ctor_get(v_toApplicative_412_, 1);
lean_inc(v_toPure_414_);
v_zero_415_ = lean_unsigned_to_nat(0u);
v_isZero_416_ = lean_nat_dec_eq(v_i_410_, v_zero_415_);
if (v_isZero_416_ == 1)
{
lean_object* v___x_417_; 
lean_dec(v_toBind_413_);
lean_dec(v_f_409_);
lean_dec_ref(v_as_408_);
lean_dec_ref(v_inst_407_);
v___x_417_ = lean_apply_2(v_toPure_414_, lean_box(0), v_b_411_);
return v___x_417_;
}
else
{
lean_object* v_one_418_; lean_object* v_n_419_; lean_object* v___f_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; uint8_t v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v_one_418_ = lean_unsigned_to_nat(1u);
v_n_419_ = lean_nat_sub(v_i_410_, v_one_418_);
lean_inc(v_n_419_);
lean_inc(v_f_409_);
lean_inc_ref(v_as_408_);
v___f_420_ = lean_alloc_closure((void*)(l_ByteArray_forIn_loop___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_420_, 0, v_toPure_414_);
lean_closure_set(v___f_420_, 1, v_inst_407_);
lean_closure_set(v___f_420_, 2, v_as_408_);
lean_closure_set(v___f_420_, 3, v_f_409_);
lean_closure_set(v___f_420_, 4, v_n_419_);
v___x_421_ = lean_byte_array_size(v_as_408_);
v___x_422_ = lean_nat_sub(v___x_421_, v_one_418_);
v___x_423_ = lean_nat_sub(v___x_422_, v_n_419_);
lean_dec(v_n_419_);
lean_dec(v___x_422_);
v___x_424_ = lean_byte_array_fget(v_as_408_, v___x_423_);
lean_dec(v___x_423_);
lean_dec_ref(v_as_408_);
v___x_425_ = lean_box(v___x_424_);
v___x_426_ = lean_apply_2(v_f_409_, v___x_425_, v_b_411_);
v___x_427_ = lean_apply_4(v_toBind_413_, lean_box(0), lean_box(0), v___x_426_, v___f_420_);
return v___x_427_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_forIn_loop___redArg___lam__0(lean_object* v_toPure_428_, lean_object* v_inst_429_, lean_object* v_as_430_, lean_object* v_f_431_, lean_object* v_n_432_, lean_object* v_____do__lift_433_){
_start:
{
if (lean_obj_tag(v_____do__lift_433_) == 0)
{
lean_object* v_a_434_; lean_object* v___x_435_; 
lean_dec(v_f_431_);
lean_dec_ref(v_as_430_);
lean_dec_ref(v_inst_429_);
v_a_434_ = lean_ctor_get(v_____do__lift_433_, 0);
lean_inc(v_a_434_);
lean_dec_ref_known(v_____do__lift_433_, 1);
v___x_435_ = lean_apply_2(v_toPure_428_, lean_box(0), v_a_434_);
return v___x_435_;
}
else
{
lean_object* v_a_436_; lean_object* v___x_437_; 
lean_dec(v_toPure_428_);
v_a_436_ = lean_ctor_get(v_____do__lift_433_, 0);
lean_inc(v_a_436_);
lean_dec_ref_known(v_____do__lift_433_, 1);
v___x_437_ = l_ByteArray_forIn_loop___redArg(v_inst_429_, v_as_430_, v_f_431_, v_n_432_, v_a_436_);
return v___x_437_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_forIn_loop___redArg___boxed(lean_object* v_inst_438_, lean_object* v_as_439_, lean_object* v_f_440_, lean_object* v_i_441_, lean_object* v_b_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_ByteArray_forIn_loop___redArg(v_inst_438_, v_as_439_, v_f_440_, v_i_441_, v_b_442_);
lean_dec(v_i_441_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_forIn_loop(lean_object* v_00_u03b2_444_, lean_object* v_m_445_, lean_object* v_inst_446_, lean_object* v_as_447_, lean_object* v_f_448_, lean_object* v_i_449_, lean_object* v_h_450_, lean_object* v_b_451_){
_start:
{
lean_object* v___x_452_; 
v___x_452_ = l_ByteArray_forIn_loop___redArg(v_inst_446_, v_as_447_, v_f_448_, v_i_449_, v_b_451_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_forIn_loop___boxed(lean_object* v_00_u03b2_453_, lean_object* v_m_454_, lean_object* v_inst_455_, lean_object* v_as_456_, lean_object* v_f_457_, lean_object* v_i_458_, lean_object* v_h_459_, lean_object* v_b_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_ByteArray_forIn_loop(v_00_u03b2_453_, v_m_454_, v_inst_455_, v_as_456_, v_f_457_, v_i_458_, v_h_459_, v_b_460_);
lean_dec(v_i_458_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_instForInUInt8OfMonad___redArg___lam__0(lean_object* v_inst_462_, lean_object* v_00_u03b2_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_){
_start:
{
size_t v_sz_467_; size_t v___x_468_; lean_object* v___x_469_; 
v_sz_467_ = lean_sarray_size(v___y_464_);
v___x_468_ = ((size_t)0ULL);
v___x_469_ = l_ByteArray_forInUnsafe_loop___redArg(v_inst_462_, v___y_464_, v___y_466_, v_sz_467_, v___x_468_, v___y_465_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_instForInUInt8OfMonad___redArg(lean_object* v_inst_470_){
_start:
{
lean_object* v___f_471_; 
v___f_471_ = lean_alloc_closure((void*)(l_ByteArray_instForInUInt8OfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_471_, 0, v_inst_470_);
return v___f_471_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_instForInUInt8OfMonad(lean_object* v_m_472_, lean_object* v_inst_473_){
_start:
{
lean_object* v___f_474_; 
v___f_474_ = lean_alloc_closure((void*)(l_ByteArray_instForInUInt8OfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_474_, 0, v_inst_473_);
return v___f_474_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___redArg___lam__0___boxed(lean_object* v_i_475_, lean_object* v_inst_476_, lean_object* v_f_477_, lean_object* v_as_478_, lean_object* v_stop_479_, lean_object* v_____do__lift_480_){
_start:
{
size_t v_i_boxed_481_; size_t v_stop_boxed_482_; lean_object* v_res_483_; 
v_i_boxed_481_ = lean_unbox_usize(v_i_475_);
lean_dec(v_i_475_);
v_stop_boxed_482_ = lean_unbox_usize(v_stop_479_);
lean_dec(v_stop_479_);
v_res_483_ = l_ByteArray_foldlMUnsafe_fold___redArg___lam__0(v_i_boxed_481_, v_inst_476_, v_f_477_, v_as_478_, v_stop_boxed_482_, v_____do__lift_480_);
return v_res_483_;
}
}
lean_object* l_ByteArray_foldlMUnsafe_fold___redArg(lean_object* v_inst_484_, lean_object* v_f_485_, lean_object* v_as_486_, size_t v_i_487_, size_t v_stop_488_, lean_object* v_b_489_){
_start:
{
lean_object* v_toApplicative_490_; lean_object* v_toBind_491_; lean_object* v_toPure_492_; uint8_t v___x_493_; 
v_toApplicative_490_ = lean_ctor_get(v_inst_484_, 0);
v_toBind_491_ = lean_ctor_get(v_inst_484_, 1);
lean_inc(v_toBind_491_);
v_toPure_492_ = lean_ctor_get(v_toApplicative_490_, 1);
v___x_493_ = lean_usize_dec_eq(v_i_487_, v_stop_488_);
if (v___x_493_ == 0)
{
lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___f_496_; uint8_t v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_494_ = lean_box_usize(v_i_487_);
v___x_495_ = lean_box_usize(v_stop_488_);
lean_inc_ref(v_as_486_);
lean_inc(v_f_485_);
v___f_496_ = lean_alloc_closure((void*)(l_ByteArray_foldlMUnsafe_fold___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_496_, 0, v___x_494_);
lean_closure_set(v___f_496_, 1, v_inst_484_);
lean_closure_set(v___f_496_, 2, v_f_485_);
lean_closure_set(v___f_496_, 3, v_as_486_);
lean_closure_set(v___f_496_, 4, v___x_495_);
v___x_497_ = lean_byte_array_uget(v_as_486_, v_i_487_);
lean_dec_ref(v_as_486_);
v___x_498_ = lean_box(v___x_497_);
v___x_499_ = lean_apply_2(v_f_485_, v_b_489_, v___x_498_);
v___x_500_ = lean_apply_4(v_toBind_491_, lean_box(0), lean_box(0), v___x_499_, v___f_496_);
return v___x_500_;
}
else
{
lean_object* v___x_501_; 
lean_inc(v_toPure_492_);
lean_dec(v_toBind_491_);
lean_dec_ref(v_as_486_);
lean_dec(v_f_485_);
lean_dec_ref(v_inst_484_);
v___x_501_ = lean_apply_2(v_toPure_492_, lean_box(0), v_b_489_);
return v___x_501_;
}
}
}
LEAN_EXPORT void l_ByteArray_foldlMUnsafe_fold___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_484_ = stack[0].m_obj;
lean_object* v_f_485_ = stack[1].m_obj;
lean_object* v_as_486_ = stack[2].m_obj;
size_t v_i_487_ = stack[3].m_num;
size_t v_stop_488_ = stack[4].m_num;
lean_object* v_b_489_ = stack[5].m_obj;
lean_object* v_res_502_;
v_res_502_ = l_ByteArray_foldlMUnsafe_fold___redArg(v_inst_484_, v_f_485_, v_as_486_, v_i_487_, v_stop_488_, v_b_489_);
stack->m_obj
 = v_res_502_;
}
lean_object* l_ByteArray_foldlMUnsafe_fold___redArg___lam__0(size_t v_i_503_, lean_object* v_inst_504_, lean_object* v_f_505_, lean_object* v_as_506_, size_t v_stop_507_, lean_object* v_____do__lift_508_){
_start:
{
size_t v___x_509_; size_t v___x_510_; lean_object* v___x_511_; 
v___x_509_ = ((size_t)1ULL);
v___x_510_ = lean_usize_add(v_i_503_, v___x_509_);
v___x_511_ = l_ByteArray_foldlMUnsafe_fold___redArg(v_inst_504_, v_f_505_, v_as_506_, v___x_510_, v_stop_507_, v_____do__lift_508_);
return v___x_511_;
}
}
LEAN_EXPORT void l_ByteArray_foldlMUnsafe_fold___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
size_t v_i_503_ = stack[0].m_num;
lean_object* v_inst_504_ = stack[1].m_obj;
lean_object* v_f_505_ = stack[2].m_obj;
lean_object* v_as_506_ = stack[3].m_obj;
size_t v_stop_507_ = stack[4].m_num;
lean_object* v_____do__lift_508_ = stack[5].m_obj;
lean_object* v_res_512_;
v_res_512_ = l_ByteArray_foldlMUnsafe_fold___redArg___lam__0(v_i_503_, v_inst_504_, v_f_505_, v_as_506_, v_stop_507_, v_____do__lift_508_);
stack->m_obj
 = v_res_512_;
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___redArg___boxed(lean_object* v_inst_513_, lean_object* v_f_514_, lean_object* v_as_515_, lean_object* v_i_516_, lean_object* v_stop_517_, lean_object* v_b_518_){
_start:
{
size_t v_i_boxed_519_; size_t v_stop_boxed_520_; lean_object* v_res_521_; 
v_i_boxed_519_ = lean_unbox_usize(v_i_516_);
lean_dec(v_i_516_);
v_stop_boxed_520_ = lean_unbox_usize(v_stop_517_);
lean_dec(v_stop_517_);
v_res_521_ = l_ByteArray_foldlMUnsafe_fold___redArg(v_inst_513_, v_f_514_, v_as_515_, v_i_boxed_519_, v_stop_boxed_520_, v_b_518_);
return v_res_521_;
}
}
lean_object* l_ByteArray_foldlMUnsafe_fold(lean_object* v_00_u03b2_522_, lean_object* v_m_523_, lean_object* v_inst_524_, lean_object* v_f_525_, lean_object* v_as_526_, size_t v_i_527_, size_t v_stop_528_, lean_object* v_b_529_){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = l_ByteArray_foldlMUnsafe_fold___redArg(v_inst_524_, v_f_525_, v_as_526_, v_i_527_, v_stop_528_, v_b_529_);
return v___x_530_;
}
}
LEAN_EXPORT void l_ByteArray_foldlMUnsafe_fold_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_524_ = stack[2].m_obj;
lean_object* v_f_525_ = stack[3].m_obj;
lean_object* v_as_526_ = stack[4].m_obj;
size_t v_i_527_ = stack[5].m_num;
size_t v_stop_528_ = stack[6].m_num;
lean_object* v_b_529_ = stack[7].m_obj;
lean_object* v_res_531_;
v_res_531_ = l_ByteArray_foldlMUnsafe_fold(lean_box(0), lean_box(0), v_inst_524_, v_f_525_, v_as_526_, v_i_527_, v_stop_528_, v_b_529_);
stack->m_obj
 = v_res_531_;
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___boxed(lean_object* v_00_u03b2_532_, lean_object* v_m_533_, lean_object* v_inst_534_, lean_object* v_f_535_, lean_object* v_as_536_, lean_object* v_i_537_, lean_object* v_stop_538_, lean_object* v_b_539_){
_start:
{
size_t v_i_boxed_540_; size_t v_stop_boxed_541_; lean_object* v_res_542_; 
v_i_boxed_540_ = lean_unbox_usize(v_i_537_);
lean_dec(v_i_537_);
v_stop_boxed_541_ = lean_unbox_usize(v_stop_538_);
lean_dec(v_stop_538_);
v_res_542_ = l_ByteArray_foldlMUnsafe_fold(v_00_u03b2_532_, v_m_533_, v_inst_534_, v_f_535_, v_as_536_, v_i_boxed_540_, v_stop_boxed_541_, v_b_539_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe___redArg(lean_object* v_inst_543_, lean_object* v_f_544_, lean_object* v_init_545_, lean_object* v_as_546_, lean_object* v_start_547_, lean_object* v_stop_548_){
_start:
{
lean_object* v_toApplicative_549_; lean_object* v_toPure_550_; uint8_t v___x_551_; 
v_toApplicative_549_ = lean_ctor_get(v_inst_543_, 0);
v_toPure_550_ = lean_ctor_get(v_toApplicative_549_, 1);
v___x_551_ = lean_nat_dec_lt(v_start_547_, v_stop_548_);
if (v___x_551_ == 0)
{
lean_object* v___x_552_; 
lean_inc(v_toPure_550_);
lean_dec_ref(v_as_546_);
lean_dec(v_f_544_);
lean_dec_ref(v_inst_543_);
v___x_552_ = lean_apply_2(v_toPure_550_, lean_box(0), v_init_545_);
return v___x_552_;
}
else
{
lean_object* v___x_553_; uint8_t v___x_554_; 
v___x_553_ = lean_byte_array_size(v_as_546_);
v___x_554_ = lean_nat_dec_le(v_stop_548_, v___x_553_);
if (v___x_554_ == 0)
{
uint8_t v___x_555_; 
v___x_555_ = lean_nat_dec_lt(v_start_547_, v___x_553_);
if (v___x_555_ == 0)
{
lean_object* v___x_556_; 
lean_inc(v_toPure_550_);
lean_dec_ref(v_as_546_);
lean_dec(v_f_544_);
lean_dec_ref(v_inst_543_);
v___x_556_ = lean_apply_2(v_toPure_550_, lean_box(0), v_init_545_);
return v___x_556_;
}
else
{
size_t v___x_557_; size_t v___x_558_; lean_object* v___x_559_; 
v___x_557_ = lean_usize_of_nat(v_start_547_);
v___x_558_ = lean_usize_of_nat(v___x_553_);
v___x_559_ = l_ByteArray_foldlMUnsafe_fold___redArg(v_inst_543_, v_f_544_, v_as_546_, v___x_557_, v___x_558_, v_init_545_);
return v___x_559_;
}
}
else
{
size_t v___x_560_; size_t v___x_561_; lean_object* v___x_562_; 
v___x_560_ = lean_usize_of_nat(v_start_547_);
v___x_561_ = lean_usize_of_nat(v_stop_548_);
v___x_562_ = l_ByteArray_foldlMUnsafe_fold___redArg(v_inst_543_, v_f_544_, v_as_546_, v___x_560_, v___x_561_, v_init_545_);
return v___x_562_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe___redArg___boxed(lean_object* v_inst_563_, lean_object* v_f_564_, lean_object* v_init_565_, lean_object* v_as_566_, lean_object* v_start_567_, lean_object* v_stop_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_ByteArray_foldlMUnsafe___redArg(v_inst_563_, v_f_564_, v_init_565_, v_as_566_, v_start_567_, v_stop_568_);
lean_dec(v_stop_568_);
lean_dec(v_start_567_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe(lean_object* v_00_u03b2_570_, lean_object* v_m_571_, lean_object* v_inst_572_, lean_object* v_f_573_, lean_object* v_init_574_, lean_object* v_as_575_, lean_object* v_start_576_, lean_object* v_stop_577_){
_start:
{
lean_object* v_toApplicative_578_; lean_object* v_toPure_579_; uint8_t v___x_580_; 
v_toApplicative_578_ = lean_ctor_get(v_inst_572_, 0);
v_toPure_579_ = lean_ctor_get(v_toApplicative_578_, 1);
v___x_580_ = lean_nat_dec_lt(v_start_576_, v_stop_577_);
if (v___x_580_ == 0)
{
lean_object* v___x_581_; 
lean_inc(v_toPure_579_);
lean_dec_ref(v_as_575_);
lean_dec(v_f_573_);
lean_dec_ref(v_inst_572_);
v___x_581_ = lean_apply_2(v_toPure_579_, lean_box(0), v_init_574_);
return v___x_581_;
}
else
{
lean_object* v___x_582_; uint8_t v___x_583_; 
v___x_582_ = lean_byte_array_size(v_as_575_);
v___x_583_ = lean_nat_dec_le(v_stop_577_, v___x_582_);
if (v___x_583_ == 0)
{
uint8_t v___x_584_; 
v___x_584_ = lean_nat_dec_lt(v_start_576_, v___x_582_);
if (v___x_584_ == 0)
{
lean_object* v___x_585_; 
lean_inc(v_toPure_579_);
lean_dec_ref(v_as_575_);
lean_dec(v_f_573_);
lean_dec_ref(v_inst_572_);
v___x_585_ = lean_apply_2(v_toPure_579_, lean_box(0), v_init_574_);
return v___x_585_;
}
else
{
size_t v___x_586_; size_t v___x_587_; lean_object* v___x_588_; 
v___x_586_ = lean_usize_of_nat(v_start_576_);
v___x_587_ = lean_usize_of_nat(v___x_582_);
v___x_588_ = l_ByteArray_foldlMUnsafe_fold___redArg(v_inst_572_, v_f_573_, v_as_575_, v___x_586_, v___x_587_, v_init_574_);
return v___x_588_;
}
}
else
{
size_t v___x_589_; size_t v___x_590_; lean_object* v___x_591_; 
v___x_589_ = lean_usize_of_nat(v_start_576_);
v___x_590_ = lean_usize_of_nat(v_stop_577_);
v___x_591_ = l_ByteArray_foldlMUnsafe_fold___redArg(v_inst_572_, v_f_573_, v_as_575_, v___x_589_, v___x_590_, v_init_574_);
return v___x_591_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe___boxed(lean_object* v_00_u03b2_592_, lean_object* v_m_593_, lean_object* v_inst_594_, lean_object* v_f_595_, lean_object* v_init_596_, lean_object* v_as_597_, lean_object* v_start_598_, lean_object* v_stop_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_ByteArray_foldlMUnsafe(v_00_u03b2_592_, v_m_593_, v_inst_594_, v_f_595_, v_init_596_, v_as_597_, v_start_598_, v_stop_599_);
lean_dec(v_stop_599_);
lean_dec(v_start_598_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlM_loop___redArg___lam__0___boxed(lean_object* v_j_601_, lean_object* v_inst_602_, lean_object* v_f_603_, lean_object* v_as_604_, lean_object* v_stop_605_, lean_object* v_n_606_, lean_object* v_____do__lift_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_ByteArray_foldlM_loop___redArg___lam__0(v_j_601_, v_inst_602_, v_f_603_, v_as_604_, v_stop_605_, v_n_606_, v_____do__lift_607_);
lean_dec(v_n_606_);
lean_dec(v_j_601_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlM_loop___redArg(lean_object* v_inst_609_, lean_object* v_f_610_, lean_object* v_as_611_, lean_object* v_stop_612_, lean_object* v_i_613_, lean_object* v_j_614_, lean_object* v_b_615_){
_start:
{
lean_object* v_toApplicative_616_; lean_object* v_toBind_617_; lean_object* v_toPure_618_; uint8_t v___x_619_; 
v_toApplicative_616_ = lean_ctor_get(v_inst_609_, 0);
v_toBind_617_ = lean_ctor_get(v_inst_609_, 1);
lean_inc(v_toBind_617_);
v_toPure_618_ = lean_ctor_get(v_toApplicative_616_, 1);
v___x_619_ = lean_nat_dec_lt(v_j_614_, v_stop_612_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; 
lean_inc(v_toPure_618_);
lean_dec(v_toBind_617_);
lean_dec(v_j_614_);
lean_dec(v_stop_612_);
lean_dec_ref(v_as_611_);
lean_dec(v_f_610_);
lean_dec_ref(v_inst_609_);
v___x_620_ = lean_apply_2(v_toPure_618_, lean_box(0), v_b_615_);
return v___x_620_;
}
else
{
lean_object* v_zero_621_; uint8_t v_isZero_622_; 
v_zero_621_ = lean_unsigned_to_nat(0u);
v_isZero_622_ = lean_nat_dec_eq(v_i_613_, v_zero_621_);
if (v_isZero_622_ == 1)
{
lean_object* v___x_623_; 
lean_inc(v_toPure_618_);
lean_dec(v_toBind_617_);
lean_dec(v_j_614_);
lean_dec(v_stop_612_);
lean_dec_ref(v_as_611_);
lean_dec(v_f_610_);
lean_dec_ref(v_inst_609_);
v___x_623_ = lean_apply_2(v_toPure_618_, lean_box(0), v_b_615_);
return v___x_623_;
}
else
{
lean_object* v_one_624_; lean_object* v_n_625_; lean_object* v___f_626_; uint8_t v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v_one_624_ = lean_unsigned_to_nat(1u);
v_n_625_ = lean_nat_sub(v_i_613_, v_one_624_);
lean_inc_ref(v_as_611_);
lean_inc(v_f_610_);
lean_inc(v_j_614_);
v___f_626_ = lean_alloc_closure((void*)(l_ByteArray_foldlM_loop___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_626_, 0, v_j_614_);
lean_closure_set(v___f_626_, 1, v_inst_609_);
lean_closure_set(v___f_626_, 2, v_f_610_);
lean_closure_set(v___f_626_, 3, v_as_611_);
lean_closure_set(v___f_626_, 4, v_stop_612_);
lean_closure_set(v___f_626_, 5, v_n_625_);
v___x_627_ = lean_byte_array_fget(v_as_611_, v_j_614_);
lean_dec(v_j_614_);
lean_dec_ref(v_as_611_);
v___x_628_ = lean_box(v___x_627_);
v___x_629_ = lean_apply_2(v_f_610_, v_b_615_, v___x_628_);
v___x_630_ = lean_apply_4(v_toBind_617_, lean_box(0), lean_box(0), v___x_629_, v___f_626_);
return v___x_630_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlM_loop___redArg___lam__0(lean_object* v_j_631_, lean_object* v_inst_632_, lean_object* v_f_633_, lean_object* v_as_634_, lean_object* v_stop_635_, lean_object* v_n_636_, lean_object* v_____do__lift_637_){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_638_ = lean_unsigned_to_nat(1u);
v___x_639_ = lean_nat_add(v_j_631_, v___x_638_);
v___x_640_ = l_ByteArray_foldlM_loop___redArg(v_inst_632_, v_f_633_, v_as_634_, v_stop_635_, v_n_636_, v___x_639_, v_____do__lift_637_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlM_loop___redArg___boxed(lean_object* v_inst_641_, lean_object* v_f_642_, lean_object* v_as_643_, lean_object* v_stop_644_, lean_object* v_i_645_, lean_object* v_j_646_, lean_object* v_b_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l_ByteArray_foldlM_loop___redArg(v_inst_641_, v_f_642_, v_as_643_, v_stop_644_, v_i_645_, v_j_646_, v_b_647_);
lean_dec(v_i_645_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlM_loop(lean_object* v_00_u03b2_649_, lean_object* v_m_650_, lean_object* v_inst_651_, lean_object* v_f_652_, lean_object* v_as_653_, lean_object* v_stop_654_, lean_object* v_h_655_, lean_object* v_i_656_, lean_object* v_j_657_, lean_object* v_b_658_){
_start:
{
lean_object* v___x_659_; 
v___x_659_ = l_ByteArray_foldlM_loop___redArg(v_inst_651_, v_f_652_, v_as_653_, v_stop_654_, v_i_656_, v_j_657_, v_b_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlM_loop___boxed(lean_object* v_00_u03b2_660_, lean_object* v_m_661_, lean_object* v_inst_662_, lean_object* v_f_663_, lean_object* v_as_664_, lean_object* v_stop_665_, lean_object* v_h_666_, lean_object* v_i_667_, lean_object* v_j_668_, lean_object* v_b_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_ByteArray_foldlM_loop(v_00_u03b2_660_, v_m_661_, v_inst_662_, v_f_663_, v_as_664_, v_stop_665_, v_h_666_, v_i_667_, v_j_668_, v_b_669_);
lean_dec(v_i_667_);
return v_res_670_;
}
}
lean_object* l_ByteArray_foldl___redArg___lam__0(lean_object* v_f_671_, lean_object* v_x1_672_, uint8_t v_x2_673_){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_674_ = lean_box(v_x2_673_);
v___x_675_ = lean_apply_2(v_f_671_, v_x1_672_, v___x_674_);
return v___x_675_;
}
}
LEAN_EXPORT void l_ByteArray_foldl___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_671_ = stack[0].m_obj;
lean_object* v_x1_672_ = stack[1].m_obj;
uint8_t v_x2_673_ = stack[2].m_num;
lean_object* v_res_676_;
v_res_676_ = l_ByteArray_foldl___redArg___lam__0(v_f_671_, v_x1_672_, v_x2_673_);
stack->m_obj
 = v_res_676_;
}
LEAN_EXPORT lean_object* l_ByteArray_foldl___redArg___lam__0___boxed(lean_object* v_f_677_, lean_object* v_x1_678_, lean_object* v_x2_679_){
_start:
{
uint8_t v_x2_187__boxed_680_; lean_object* v_res_681_; 
v_x2_187__boxed_680_ = lean_unbox(v_x2_679_);
v_res_681_ = l_ByteArray_foldl___redArg___lam__0(v_f_677_, v_x1_678_, v_x2_187__boxed_680_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldl___redArg(lean_object* v_f_701_, lean_object* v_init_702_, lean_object* v_as_703_, lean_object* v_start_704_, lean_object* v_stop_705_){
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
LEAN_EXPORT lean_object* l_ByteArray_foldl___redArg___boxed(lean_object* v_f_718_, lean_object* v_init_719_, lean_object* v_as_720_, lean_object* v_start_721_, lean_object* v_stop_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l_ByteArray_foldl___redArg(v_f_718_, v_init_719_, v_as_720_, v_start_721_, v_stop_722_);
lean_dec(v_stop_722_);
lean_dec(v_start_721_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldl(lean_object* v_00_u03b2_724_, lean_object* v_f_725_, lean_object* v_init_726_, lean_object* v_as_727_, lean_object* v_start_728_, lean_object* v_stop_729_){
_start:
{
lean_object* v___x_730_; uint8_t v___x_731_; 
v___x_730_ = ((lean_object*)(l_ByteArray_foldl___redArg___closed__9));
v___x_731_ = lean_nat_dec_lt(v_start_728_, v_stop_729_);
if (v___x_731_ == 0)
{
lean_dec_ref(v_as_727_);
lean_dec(v_f_725_);
return v_init_726_;
}
else
{
lean_object* v___f_732_; lean_object* v___x_733_; uint8_t v___x_734_; 
v___f_732_ = lean_alloc_closure((void*)(l_ByteArray_foldl___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_732_, 0, v_f_725_);
v___x_733_ = lean_byte_array_size(v_as_727_);
v___x_734_ = lean_nat_dec_le(v_stop_729_, v___x_733_);
if (v___x_734_ == 0)
{
uint8_t v___x_735_; 
v___x_735_ = lean_nat_dec_lt(v_start_728_, v___x_733_);
if (v___x_735_ == 0)
{
lean_dec_ref(v___f_732_);
lean_dec_ref(v_as_727_);
return v_init_726_;
}
else
{
size_t v___x_736_; size_t v___x_737_; lean_object* v___x_738_; 
v___x_736_ = lean_usize_of_nat(v_start_728_);
v___x_737_ = lean_usize_of_nat(v___x_733_);
v___x_738_ = l_ByteArray_foldlMUnsafe_fold___redArg(v___x_730_, v___f_732_, v_as_727_, v___x_736_, v___x_737_, v_init_726_);
return v___x_738_;
}
}
else
{
size_t v___x_739_; size_t v___x_740_; lean_object* v___x_741_; 
v___x_739_ = lean_usize_of_nat(v_start_728_);
v___x_740_ = lean_usize_of_nat(v_stop_729_);
v___x_741_ = l_ByteArray_foldlMUnsafe_fold___redArg(v___x_730_, v___f_732_, v_as_727_, v___x_739_, v___x_740_, v_init_726_);
return v___x_741_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldl___boxed(lean_object* v_00_u03b2_742_, lean_object* v_f_743_, lean_object* v_init_744_, lean_object* v_as_745_, lean_object* v_start_746_, lean_object* v_stop_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_ByteArray_foldl(v_00_u03b2_742_, v_f_743_, v_init_744_, v_as_745_, v_start_746_, v_stop_747_);
lean_dec(v_stop_747_);
lean_dec(v_start_746_);
return v_res_748_;
}
}
static lean_object* _init_l_ByteArray_instInhabitedIterator_default___closed__0(void){
_start:
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_749_ = lean_unsigned_to_nat(0u);
v___x_750_ = l_ByteArray_empty;
v___x_751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_751_, 0, v___x_750_);
lean_ctor_set(v___x_751_, 1, v___x_749_);
return v___x_751_;
}
}
static lean_object* _init_l_ByteArray_instInhabitedIterator_default(void){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = lean_obj_once(&l_ByteArray_instInhabitedIterator_default___closed__0, &l_ByteArray_instInhabitedIterator_default___closed__0_once, _init_l_ByteArray_instInhabitedIterator_default___closed__0);
return v___x_752_;
}
}
static lean_object* _init_l_ByteArray_instInhabitedIterator(void){
_start:
{
lean_object* v___x_753_; 
v___x_753_ = l_ByteArray_instInhabitedIterator_default;
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_mkIterator(lean_object* v_arr_754_){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_755_ = lean_unsigned_to_nat(0u);
v___x_756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_756_, 0, v_arr_754_);
lean_ctor_set(v___x_756_, 1, v___x_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_iter(lean_object* v_arr_757_){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = l_ByteArray_mkIterator(v_arr_757_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_instSizeOfIterator___lam__0(lean_object* v_i_759_){
_start:
{
lean_object* v_array_760_; lean_object* v_idx_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v_array_760_ = lean_ctor_get(v_i_759_, 0);
v_idx_761_ = lean_ctor_get(v_i_759_, 1);
v___x_762_ = lean_byte_array_size(v_array_760_);
v___x_763_ = lean_nat_sub(v___x_762_, v_idx_761_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_instSizeOfIterator___lam__0___boxed(lean_object* v_i_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_ByteArray_instSizeOfIterator___lam__0(v_i_764_);
lean_dec_ref(v_i_764_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_remainingBytes(lean_object* v_x_768_){
_start:
{
lean_object* v_array_769_; lean_object* v_idx_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v_array_769_ = lean_ctor_get(v_x_768_, 0);
v_idx_770_ = lean_ctor_get(v_x_768_, 1);
v___x_771_ = lean_byte_array_size(v_array_769_);
v___x_772_ = lean_nat_sub(v___x_771_, v_idx_770_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_remainingBytes___boxed(lean_object* v_x_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_ByteArray_Iterator_remainingBytes(v_x_773_);
lean_dec_ref(v_x_773_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_pos(lean_object* v_self_775_){
_start:
{
lean_object* v_idx_776_; 
v_idx_776_ = lean_ctor_get(v_self_775_, 1);
lean_inc(v_idx_776_);
return v_idx_776_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_pos___boxed(lean_object* v_self_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_ByteArray_Iterator_pos(v_self_777_);
lean_dec_ref(v_self_777_);
return v_res_778_;
}
}
uint8_t l_ByteArray_Iterator_atEnd(lean_object* v_x_779_){
_start:
{
lean_object* v_array_780_; lean_object* v_idx_781_; lean_object* v___x_782_; uint8_t v___x_783_; 
v_array_780_ = lean_ctor_get(v_x_779_, 0);
v_idx_781_ = lean_ctor_get(v_x_779_, 1);
v___x_782_ = lean_byte_array_size(v_array_780_);
v___x_783_ = lean_nat_dec_le(v___x_782_, v_idx_781_);
return v___x_783_;
}
}
LEAN_EXPORT void l_ByteArray_Iterator_atEnd_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_779_ = stack[0].m_obj;
uint8_t v_res_784_;
v_res_784_ = l_ByteArray_Iterator_atEnd(v_x_779_);
stack->m_num = v_res_784_;
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_atEnd___boxed(lean_object* v_x_785_){
_start:
{
uint8_t v_res_786_; lean_object* v_r_787_; 
v_res_786_ = l_ByteArray_Iterator_atEnd(v_x_785_);
lean_dec_ref(v_x_785_);
v_r_787_ = lean_box(v_res_786_);
return v_r_787_;
}
}
uint8_t l_ByteArray_Iterator_curr(lean_object* v_x_788_){
_start:
{
lean_object* v_array_789_; lean_object* v_idx_790_; lean_object* v___x_791_; uint8_t v___x_792_; 
v_array_789_ = lean_ctor_get(v_x_788_, 0);
v_idx_790_ = lean_ctor_get(v_x_788_, 1);
v___x_791_ = lean_byte_array_size(v_array_789_);
v___x_792_ = lean_nat_dec_lt(v_idx_790_, v___x_791_);
if (v___x_792_ == 0)
{
uint8_t v___x_793_; 
v___x_793_ = 0;
return v___x_793_;
}
else
{
uint8_t v___x_794_; 
v___x_794_ = lean_byte_array_fget(v_array_789_, v_idx_790_);
return v___x_794_;
}
}
}
LEAN_EXPORT void l_ByteArray_Iterator_curr_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_788_ = stack[0].m_obj;
uint8_t v_res_795_;
v_res_795_ = l_ByteArray_Iterator_curr(v_x_788_);
stack->m_num = v_res_795_;
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_curr___boxed(lean_object* v_x_796_){
_start:
{
uint8_t v_res_797_; lean_object* v_r_798_; 
v_res_797_ = l_ByteArray_Iterator_curr(v_x_796_);
lean_dec_ref(v_x_796_);
v_r_798_ = lean_box(v_res_797_);
return v_r_798_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_next(lean_object* v_x_799_){
_start:
{
lean_object* v_array_800_; lean_object* v_idx_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_810_; 
v_array_800_ = lean_ctor_get(v_x_799_, 0);
v_idx_801_ = lean_ctor_get(v_x_799_, 1);
v_isSharedCheck_810_ = !lean_is_exclusive(v_x_799_);
if (v_isSharedCheck_810_ == 0)
{
v___x_803_ = v_x_799_;
v_isShared_804_ = v_isSharedCheck_810_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_idx_801_);
lean_inc(v_array_800_);
lean_dec(v_x_799_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_810_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_808_; 
v___x_805_ = lean_unsigned_to_nat(1u);
v___x_806_ = lean_nat_add(v_idx_801_, v___x_805_);
lean_dec(v_idx_801_);
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 1, v___x_806_);
v___x_808_ = v___x_803_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_array_800_);
lean_ctor_set(v_reuseFailAlloc_809_, 1, v___x_806_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_prev(lean_object* v_x_811_){
_start:
{
lean_object* v_array_812_; lean_object* v_idx_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_822_; 
v_array_812_ = lean_ctor_get(v_x_811_, 0);
v_idx_813_ = lean_ctor_get(v_x_811_, 1);
v_isSharedCheck_822_ = !lean_is_exclusive(v_x_811_);
if (v_isSharedCheck_822_ == 0)
{
v___x_815_ = v_x_811_;
v_isShared_816_ = v_isSharedCheck_822_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_idx_813_);
lean_inc(v_array_812_);
lean_dec(v_x_811_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_822_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_820_; 
v___x_817_ = lean_unsigned_to_nat(1u);
v___x_818_ = lean_nat_sub(v_idx_813_, v___x_817_);
lean_dec(v_idx_813_);
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 1, v___x_818_);
v___x_820_ = v___x_815_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_array_812_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v___x_818_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
}
uint8_t l_ByteArray_Iterator_hasNext(lean_object* v_x_823_){
_start:
{
lean_object* v_array_824_; lean_object* v_idx_825_; lean_object* v___x_826_; uint8_t v___x_827_; 
v_array_824_ = lean_ctor_get(v_x_823_, 0);
v_idx_825_ = lean_ctor_get(v_x_823_, 1);
v___x_826_ = lean_byte_array_size(v_array_824_);
v___x_827_ = lean_nat_dec_lt(v_idx_825_, v___x_826_);
return v___x_827_;
}
}
LEAN_EXPORT void l_ByteArray_Iterator_hasNext_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_823_ = stack[0].m_obj;
uint8_t v_res_828_;
v_res_828_ = l_ByteArray_Iterator_hasNext(v_x_823_);
stack->m_num = v_res_828_;
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_hasNext___boxed(lean_object* v_x_829_){
_start:
{
uint8_t v_res_830_; lean_object* v_r_831_; 
v_res_830_ = l_ByteArray_Iterator_hasNext(v_x_829_);
lean_dec_ref(v_x_829_);
v_r_831_ = lean_box(v_res_830_);
return v_r_831_;
}
}
uint8_t l_ByteArray_Iterator_curr_x27___redArg(lean_object* v_it_832_){
_start:
{
lean_object* v_array_833_; lean_object* v_idx_834_; uint8_t v___x_835_; 
v_array_833_ = lean_ctor_get(v_it_832_, 0);
v_idx_834_ = lean_ctor_get(v_it_832_, 1);
v___x_835_ = lean_byte_array_fget(v_array_833_, v_idx_834_);
return v___x_835_;
}
}
LEAN_EXPORT void l_ByteArray_Iterator_curr_x27___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_it_832_ = stack[0].m_obj;
uint8_t v_res_836_;
v_res_836_ = l_ByteArray_Iterator_curr_x27___redArg(v_it_832_);
stack->m_num = v_res_836_;
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_curr_x27___redArg___boxed(lean_object* v_it_837_){
_start:
{
uint8_t v_res_838_; lean_object* v_r_839_; 
v_res_838_ = l_ByteArray_Iterator_curr_x27___redArg(v_it_837_);
lean_dec_ref(v_it_837_);
v_r_839_ = lean_box(v_res_838_);
return v_r_839_;
}
}
uint8_t l_ByteArray_Iterator_curr_x27(lean_object* v_it_840_, lean_object* v_h_841_){
_start:
{
lean_object* v_array_842_; lean_object* v_idx_843_; uint8_t v___x_844_; 
v_array_842_ = lean_ctor_get(v_it_840_, 0);
v_idx_843_ = lean_ctor_get(v_it_840_, 1);
v___x_844_ = lean_byte_array_fget(v_array_842_, v_idx_843_);
return v___x_844_;
}
}
LEAN_EXPORT void l_ByteArray_Iterator_curr_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_it_840_ = stack[0].m_obj;
uint8_t v_res_845_;
v_res_845_ = l_ByteArray_Iterator_curr_x27(v_it_840_, lean_box(0));
stack->m_num = v_res_845_;
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_curr_x27___boxed(lean_object* v_it_846_, lean_object* v_h_847_){
_start:
{
uint8_t v_res_848_; lean_object* v_r_849_; 
v_res_848_ = l_ByteArray_Iterator_curr_x27(v_it_846_, v_h_847_);
lean_dec_ref(v_it_846_);
v_r_849_ = lean_box(v_res_848_);
return v_r_849_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_next_x27___redArg(lean_object* v_it_850_){
_start:
{
lean_object* v_array_851_; lean_object* v_idx_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_861_; 
v_array_851_ = lean_ctor_get(v_it_850_, 0);
v_idx_852_ = lean_ctor_get(v_it_850_, 1);
v_isSharedCheck_861_ = !lean_is_exclusive(v_it_850_);
if (v_isSharedCheck_861_ == 0)
{
v___x_854_ = v_it_850_;
v_isShared_855_ = v_isSharedCheck_861_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_idx_852_);
lean_inc(v_array_851_);
lean_dec(v_it_850_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_861_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_859_; 
v___x_856_ = lean_unsigned_to_nat(1u);
v___x_857_ = lean_nat_add(v_idx_852_, v___x_856_);
lean_dec(v_idx_852_);
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 1, v___x_857_);
v___x_859_ = v___x_854_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_array_851_);
lean_ctor_set(v_reuseFailAlloc_860_, 1, v___x_857_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_next_x27(lean_object* v_it_862_, lean_object* v___h_863_){
_start:
{
lean_object* v_array_864_; lean_object* v_idx_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_874_; 
v_array_864_ = lean_ctor_get(v_it_862_, 0);
v_idx_865_ = lean_ctor_get(v_it_862_, 1);
v_isSharedCheck_874_ = !lean_is_exclusive(v_it_862_);
if (v_isSharedCheck_874_ == 0)
{
v___x_867_ = v_it_862_;
v_isShared_868_ = v_isSharedCheck_874_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_idx_865_);
lean_inc(v_array_864_);
lean_dec(v_it_862_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_874_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_872_; 
v___x_869_ = lean_unsigned_to_nat(1u);
v___x_870_ = lean_nat_add(v_idx_865_, v___x_869_);
lean_dec(v_idx_865_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 1, v___x_870_);
v___x_872_ = v___x_867_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_array_864_);
lean_ctor_set(v_reuseFailAlloc_873_, 1, v___x_870_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
}
uint8_t l_ByteArray_Iterator_hasPrev(lean_object* v_x_875_){
_start:
{
lean_object* v_idx_876_; lean_object* v___x_877_; uint8_t v___x_878_; 
v_idx_876_ = lean_ctor_get(v_x_875_, 1);
v___x_877_ = lean_unsigned_to_nat(0u);
v___x_878_ = lean_nat_dec_lt(v___x_877_, v_idx_876_);
return v___x_878_;
}
}
LEAN_EXPORT void l_ByteArray_Iterator_hasPrev_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_875_ = stack[0].m_obj;
uint8_t v_res_879_;
v_res_879_ = l_ByteArray_Iterator_hasPrev(v_x_875_);
stack->m_num = v_res_879_;
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_hasPrev___boxed(lean_object* v_x_880_){
_start:
{
uint8_t v_res_881_; lean_object* v_r_882_; 
v_res_881_ = l_ByteArray_Iterator_hasPrev(v_x_880_);
lean_dec_ref(v_x_880_);
v_r_882_ = lean_box(v_res_881_);
return v_r_882_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_toEnd(lean_object* v_x_883_){
_start:
{
lean_object* v_array_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_892_; 
v_array_884_ = lean_ctor_get(v_x_883_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v_x_883_);
if (v_isSharedCheck_892_ == 0)
{
lean_object* v_unused_893_; 
v_unused_893_ = lean_ctor_get(v_x_883_, 1);
lean_dec(v_unused_893_);
v___x_886_ = v_x_883_;
v_isShared_887_ = v_isSharedCheck_892_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_array_884_);
lean_dec(v_x_883_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_892_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_888_; lean_object* v___x_890_; 
v___x_888_ = lean_byte_array_size(v_array_884_);
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 1, v___x_888_);
v___x_890_ = v___x_886_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_array_884_);
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
LEAN_EXPORT lean_object* l_ByteArray_Iterator_forward(lean_object* v_x_894_, lean_object* v_x_895_){
_start:
{
lean_object* v_array_896_; lean_object* v_idx_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_905_; 
v_array_896_ = lean_ctor_get(v_x_894_, 0);
v_idx_897_ = lean_ctor_get(v_x_894_, 1);
v_isSharedCheck_905_ = !lean_is_exclusive(v_x_894_);
if (v_isSharedCheck_905_ == 0)
{
v___x_899_ = v_x_894_;
v_isShared_900_ = v_isSharedCheck_905_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_idx_897_);
lean_inc(v_array_896_);
lean_dec(v_x_894_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_905_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_901_; lean_object* v___x_903_; 
v___x_901_ = lean_nat_add(v_idx_897_, v_x_895_);
lean_dec(v_idx_897_);
if (v_isShared_900_ == 0)
{
lean_ctor_set(v___x_899_, 1, v___x_901_);
v___x_903_ = v___x_899_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v_array_896_);
lean_ctor_set(v_reuseFailAlloc_904_, 1, v___x_901_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_forward___boxed(lean_object* v_x_906_, lean_object* v_x_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_ByteArray_Iterator_forward(v_x_906_, v_x_907_);
lean_dec(v_x_907_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_nextn(lean_object* v_a_909_, lean_object* v_a_910_){
_start:
{
lean_object* v_array_911_; lean_object* v_idx_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_920_; 
v_array_911_ = lean_ctor_get(v_a_909_, 0);
v_idx_912_ = lean_ctor_get(v_a_909_, 1);
v_isSharedCheck_920_ = !lean_is_exclusive(v_a_909_);
if (v_isSharedCheck_920_ == 0)
{
v___x_914_ = v_a_909_;
v_isShared_915_ = v_isSharedCheck_920_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_idx_912_);
lean_inc(v_array_911_);
lean_dec(v_a_909_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_920_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_916_; lean_object* v___x_918_; 
v___x_916_ = lean_nat_add(v_idx_912_, v_a_910_);
lean_dec(v_idx_912_);
if (v_isShared_915_ == 0)
{
lean_ctor_set(v___x_914_, 1, v___x_916_);
v___x_918_ = v___x_914_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_array_911_);
lean_ctor_set(v_reuseFailAlloc_919_, 1, v___x_916_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_nextn___boxed(lean_object* v_a_921_, lean_object* v_a_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_ByteArray_Iterator_nextn(v_a_921_, v_a_922_);
lean_dec(v_a_922_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_prevn(lean_object* v_x_924_, lean_object* v_x_925_){
_start:
{
lean_object* v_array_926_; lean_object* v_idx_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_935_; 
v_array_926_ = lean_ctor_get(v_x_924_, 0);
v_idx_927_ = lean_ctor_get(v_x_924_, 1);
v_isSharedCheck_935_ = !lean_is_exclusive(v_x_924_);
if (v_isSharedCheck_935_ == 0)
{
v___x_929_ = v_x_924_;
v_isShared_930_ = v_isSharedCheck_935_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_idx_927_);
lean_inc(v_array_926_);
lean_dec(v_x_924_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_935_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_931_; lean_object* v___x_933_; 
v___x_931_ = lean_nat_sub(v_idx_927_, v_x_925_);
lean_dec(v_idx_927_);
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 1, v___x_931_);
v___x_933_ = v___x_929_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_array_926_);
lean_ctor_set(v_reuseFailAlloc_934_, 1, v___x_931_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_prevn___boxed(lean_object* v_x_936_, lean_object* v_x_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_ByteArray_Iterator_prevn(v_x_936_, v_x_937_);
lean_dec(v_x_937_);
return v_res_938_;
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
