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
LEAN_EXPORT lean_object* l_ByteArray_markLinear___boxed(lean_object* v_a_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = lean_sarray_mark_linear(v_a_162_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_propagateMark___boxed(lean_object* v_a_166_, lean_object* v_b_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = lean_sarray_propagate_mark(v_a_166_, v_b_167_);
lean_dec_ref(v_a_166_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_hash___boxed(lean_object* v_a_170_){
_start:
{
uint64_t v_res_171_; lean_object* v_r_172_; 
v_res_171_ = lean_byte_array_hash(v_a_170_);
lean_dec_ref(v_a_170_);
v_r_172_ = lean_box_uint64(v_res_171_);
return v_r_172_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_isEmpty(lean_object* v_s_175_){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; uint8_t v___x_178_; 
v___x_176_ = lean_byte_array_size(v_s_175_);
v___x_177_ = lean_unsigned_to_nat(0u);
v___x_178_ = lean_nat_dec_eq(v___x_176_, v___x_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_isEmpty___boxed(lean_object* v_s_179_){
_start:
{
uint8_t v_res_180_; lean_object* v_r_181_; 
v_res_180_ = l_ByteArray_isEmpty(v_s_179_);
lean_dec_ref(v_s_179_);
v_r_181_ = lean_box(v_res_180_);
return v_r_181_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_copySlice___boxed(lean_object* v_src_188_, lean_object* v_srcOff_189_, lean_object* v_dest_190_, lean_object* v_destOff_191_, lean_object* v_len_192_, lean_object* v_exact_193_){
_start:
{
uint8_t v_exact_boxed_194_; lean_object* v_res_195_; 
v_exact_boxed_194_ = lean_unbox(v_exact_193_);
v_res_195_ = lean_byte_array_copy_slice(v_src_188_, v_srcOff_189_, v_dest_190_, v_destOff_191_, v_len_192_, v_exact_boxed_194_);
lean_dec_ref(v_src_188_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_extract(lean_object* v_a_196_, lean_object* v_b_197_, lean_object* v_e_198_){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; uint8_t v___x_202_; lean_object* v___x_203_; 
v___x_199_ = l_ByteArray_empty;
v___x_200_ = lean_unsigned_to_nat(0u);
v___x_201_ = lean_nat_sub(v_e_198_, v_b_197_);
v___x_202_ = 1;
v___x_203_ = lean_byte_array_copy_slice(v_a_196_, v_b_197_, v___x_199_, v___x_200_, v___x_201_, v___x_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_extract___boxed(lean_object* v_a_204_, lean_object* v_b_205_, lean_object* v_e_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_ByteArray_extract(v_a_204_, v_b_205_, v_e_206_);
lean_dec(v_e_206_);
lean_dec_ref(v_a_204_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_fastAppend(lean_object* v_a_208_, lean_object* v_b_209_){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; uint8_t v___x_213_; lean_object* v___x_214_; 
v___x_210_ = lean_unsigned_to_nat(0u);
v___x_211_ = lean_byte_array_size(v_a_208_);
v___x_212_ = lean_byte_array_size(v_b_209_);
v___x_213_ = 0;
v___x_214_ = lean_byte_array_copy_slice(v_b_209_, v___x_210_, v_a_208_, v___x_211_, v___x_212_, v___x_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_fastAppend___boxed(lean_object* v_a_215_, lean_object* v_b_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_ByteArray_fastAppend(v_a_215_, v_b_216_);
lean_dec_ref(v_b_216_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_toList_loop(lean_object* v_bs_220_, lean_object* v_i_221_, lean_object* v_r_222_){
_start:
{
lean_object* v___x_223_; uint8_t v___x_224_; 
v___x_223_ = lean_byte_array_size(v_bs_220_);
v___x_224_ = lean_nat_dec_lt(v_i_221_, v___x_223_);
if (v___x_224_ == 0)
{
lean_object* v___x_225_; 
lean_dec(v_i_221_);
v___x_225_ = l_List_reverse___redArg(v_r_222_);
return v___x_225_;
}
else
{
lean_object* v___x_226_; lean_object* v___x_227_; uint8_t v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_226_ = lean_unsigned_to_nat(1u);
v___x_227_ = lean_nat_add(v_i_221_, v___x_226_);
v___x_228_ = lean_byte_array_get(v_bs_220_, v_i_221_);
lean_dec(v_i_221_);
v___x_229_ = lean_box(v___x_228_);
v___x_230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_230_, 0, v___x_229_);
lean_ctor_set(v___x_230_, 1, v_r_222_);
v_i_221_ = v___x_227_;
v_r_222_ = v___x_230_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_toList_loop___boxed(lean_object* v_bs_232_, lean_object* v_i_233_, lean_object* v_r_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_ByteArray_toList_loop(v_bs_232_, v_i_233_, v_r_234_);
lean_dec_ref(v_bs_232_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_toList(lean_object* v_bs_236_){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_237_ = lean_unsigned_to_nat(0u);
v___x_238_ = lean_box(0);
v___x_239_ = l_ByteArray_toList_loop(v_bs_236_, v___x_237_, v___x_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_toList___boxed(lean_object* v_bs_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_ByteArray_toList(v_bs_240_);
lean_dec_ref(v_bs_240_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findFinIdx_x3f_loop(lean_object* v_a_242_, lean_object* v_p_243_, lean_object* v_i_244_){
_start:
{
lean_object* v___x_245_; uint8_t v___x_246_; 
v___x_245_ = lean_byte_array_size(v_a_242_);
v___x_246_ = lean_nat_dec_lt(v_i_244_, v___x_245_);
if (v___x_246_ == 0)
{
lean_object* v___x_247_; 
lean_dec(v_i_244_);
lean_dec_ref(v_p_243_);
v___x_247_ = lean_box(0);
return v___x_247_;
}
else
{
uint8_t v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; uint8_t v___x_251_; 
v___x_248_ = lean_byte_array_fget(v_a_242_, v_i_244_);
v___x_249_ = lean_box(v___x_248_);
lean_inc_ref(v_p_243_);
v___x_250_ = lean_apply_1(v_p_243_, v___x_249_);
v___x_251_ = lean_unbox(v___x_250_);
if (v___x_251_ == 0)
{
lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_252_ = lean_unsigned_to_nat(1u);
v___x_253_ = lean_nat_add(v_i_244_, v___x_252_);
lean_dec(v_i_244_);
v_i_244_ = v___x_253_;
goto _start;
}
else
{
lean_object* v___x_255_; 
lean_dec_ref(v_p_243_);
v___x_255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_255_, 0, v_i_244_);
return v___x_255_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_findFinIdx_x3f_loop___boxed(lean_object* v_a_256_, lean_object* v_p_257_, lean_object* v_i_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_ByteArray_findFinIdx_x3f_loop(v_a_256_, v_p_257_, v_i_258_);
lean_dec_ref(v_a_256_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findFinIdx_x3f(lean_object* v_a_260_, lean_object* v_p_261_, lean_object* v_start_262_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = l_ByteArray_findFinIdx_x3f_loop(v_a_260_, v_p_261_, v_start_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findFinIdx_x3f___boxed(lean_object* v_a_264_, lean_object* v_p_265_, lean_object* v_start_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_ByteArray_findFinIdx_x3f(v_a_264_, v_p_265_, v_start_266_);
lean_dec_ref(v_a_264_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop(lean_object* v_a_268_, lean_object* v_p_269_, lean_object* v_i_270_){
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
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___boxed(lean_object* v_a_282_, lean_object* v_p_283_, lean_object* v_i_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_ByteArray_findIdx_x3f_loop(v_a_282_, v_p_283_, v_i_284_);
lean_dec_ref(v_a_282_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f(lean_object* v_a_286_, lean_object* v_p_287_, lean_object* v_start_288_){
_start:
{
lean_object* v___x_289_; 
v___x_289_ = l_ByteArray_findIdx_x3f_loop(v_a_286_, v_p_287_, v_start_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f___boxed(lean_object* v_a_290_, lean_object* v_p_291_, lean_object* v_start_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_ByteArray_findIdx_x3f(v_a_290_, v_p_291_, v_start_292_);
lean_dec_ref(v_a_290_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe_loop___redArg___lam__0___boxed(lean_object* v_toPure_294_, lean_object* v_i_295_, lean_object* v_inst_296_, lean_object* v_as_297_, lean_object* v_f_298_, lean_object* v_sz_299_, lean_object* v_____do__lift_300_){
_start:
{
size_t v_i_boxed_301_; size_t v_sz_boxed_302_; lean_object* v_res_303_; 
v_i_boxed_301_ = lean_unbox_usize(v_i_295_);
lean_dec(v_i_295_);
v_sz_boxed_302_ = lean_unbox_usize(v_sz_299_);
lean_dec(v_sz_299_);
v_res_303_ = l_ByteArray_forInUnsafe_loop___redArg___lam__0(v_toPure_294_, v_i_boxed_301_, v_inst_296_, v_as_297_, v_f_298_, v_sz_boxed_302_, v_____do__lift_300_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe_loop___redArg(lean_object* v_inst_304_, lean_object* v_as_305_, lean_object* v_f_306_, size_t v_sz_307_, size_t v_i_308_, lean_object* v_b_309_){
_start:
{
lean_object* v_toApplicative_310_; lean_object* v_toBind_311_; lean_object* v_toPure_312_; uint8_t v___x_313_; 
v_toApplicative_310_ = lean_ctor_get(v_inst_304_, 0);
v_toBind_311_ = lean_ctor_get(v_inst_304_, 1);
lean_inc(v_toBind_311_);
v_toPure_312_ = lean_ctor_get(v_toApplicative_310_, 1);
lean_inc(v_toPure_312_);
v___x_313_ = lean_usize_dec_lt(v_i_308_, v_sz_307_);
if (v___x_313_ == 0)
{
lean_object* v___x_314_; 
lean_dec(v_toBind_311_);
lean_dec(v_f_306_);
lean_dec_ref(v_as_305_);
lean_dec_ref(v_inst_304_);
v___x_314_ = lean_apply_2(v_toPure_312_, lean_box(0), v_b_309_);
return v___x_314_;
}
else
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___f_317_; uint8_t v_a_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_315_ = lean_box_usize(v_i_308_);
v___x_316_ = lean_box_usize(v_sz_307_);
lean_inc(v_f_306_);
lean_inc_ref(v_as_305_);
v___f_317_ = lean_alloc_closure((void*)(l_ByteArray_forInUnsafe_loop___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_317_, 0, v_toPure_312_);
lean_closure_set(v___f_317_, 1, v___x_315_);
lean_closure_set(v___f_317_, 2, v_inst_304_);
lean_closure_set(v___f_317_, 3, v_as_305_);
lean_closure_set(v___f_317_, 4, v_f_306_);
lean_closure_set(v___f_317_, 5, v___x_316_);
v_a_318_ = lean_byte_array_uget(v_as_305_, v_i_308_);
lean_dec_ref(v_as_305_);
v___x_319_ = lean_box(v_a_318_);
v___x_320_ = lean_apply_2(v_f_306_, v___x_319_, v_b_309_);
v___x_321_ = lean_apply_4(v_toBind_311_, lean_box(0), lean_box(0), v___x_320_, v___f_317_);
return v___x_321_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe_loop___redArg___lam__0(lean_object* v_toPure_322_, size_t v_i_323_, lean_object* v_inst_324_, lean_object* v_as_325_, lean_object* v_f_326_, size_t v_sz_327_, lean_object* v_____do__lift_328_){
_start:
{
if (lean_obj_tag(v_____do__lift_328_) == 0)
{
lean_object* v_a_329_; lean_object* v___x_330_; 
lean_dec(v_f_326_);
lean_dec_ref(v_as_325_);
lean_dec_ref(v_inst_324_);
v_a_329_ = lean_ctor_get(v_____do__lift_328_, 0);
lean_inc(v_a_329_);
lean_dec_ref_known(v_____do__lift_328_, 1);
v___x_330_ = lean_apply_2(v_toPure_322_, lean_box(0), v_a_329_);
return v___x_330_;
}
else
{
lean_object* v_a_331_; size_t v___x_332_; size_t v___x_333_; lean_object* v___x_334_; 
lean_dec(v_toPure_322_);
v_a_331_ = lean_ctor_get(v_____do__lift_328_, 0);
lean_inc(v_a_331_);
lean_dec_ref_known(v_____do__lift_328_, 1);
v___x_332_ = ((size_t)1ULL);
v___x_333_ = lean_usize_add(v_i_323_, v___x_332_);
v___x_334_ = l_ByteArray_forInUnsafe_loop___redArg(v_inst_324_, v_as_325_, v_f_326_, v_sz_327_, v___x_333_, v_a_331_);
return v___x_334_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe_loop___redArg___boxed(lean_object* v_inst_335_, lean_object* v_as_336_, lean_object* v_f_337_, lean_object* v_sz_338_, lean_object* v_i_339_, lean_object* v_b_340_){
_start:
{
size_t v_sz_boxed_341_; size_t v_i_boxed_342_; lean_object* v_res_343_; 
v_sz_boxed_341_ = lean_unbox_usize(v_sz_338_);
lean_dec(v_sz_338_);
v_i_boxed_342_ = lean_unbox_usize(v_i_339_);
lean_dec(v_i_339_);
v_res_343_ = l_ByteArray_forInUnsafe_loop___redArg(v_inst_335_, v_as_336_, v_f_337_, v_sz_boxed_341_, v_i_boxed_342_, v_b_340_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe_loop(lean_object* v_00_u03b2_344_, lean_object* v_m_345_, lean_object* v_inst_346_, lean_object* v_as_347_, lean_object* v_f_348_, size_t v_sz_349_, size_t v_i_350_, lean_object* v_b_351_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = l_ByteArray_forInUnsafe_loop___redArg(v_inst_346_, v_as_347_, v_f_348_, v_sz_349_, v_i_350_, v_b_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe_loop___boxed(lean_object* v_00_u03b2_353_, lean_object* v_m_354_, lean_object* v_inst_355_, lean_object* v_as_356_, lean_object* v_f_357_, lean_object* v_sz_358_, lean_object* v_i_359_, lean_object* v_b_360_){
_start:
{
size_t v_sz_boxed_361_; size_t v_i_boxed_362_; lean_object* v_res_363_; 
v_sz_boxed_361_ = lean_unbox_usize(v_sz_358_);
lean_dec(v_sz_358_);
v_i_boxed_362_ = lean_unbox_usize(v_i_359_);
lean_dec(v_i_359_);
v_res_363_ = l_ByteArray_forInUnsafe_loop(v_00_u03b2_353_, v_m_354_, v_inst_355_, v_as_356_, v_f_357_, v_sz_boxed_361_, v_i_boxed_362_, v_b_360_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe___redArg(lean_object* v_inst_364_, lean_object* v_as_365_, lean_object* v_b_366_, lean_object* v_f_367_){
_start:
{
size_t v_sz_368_; size_t v___x_369_; lean_object* v___x_370_; 
v_sz_368_ = lean_sarray_size(v_as_365_);
v___x_369_ = ((size_t)0ULL);
v___x_370_ = l_ByteArray_forInUnsafe_loop___redArg(v_inst_364_, v_as_365_, v_f_367_, v_sz_368_, v___x_369_, v_b_366_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe(lean_object* v_00_u03b2_371_, lean_object* v_m_372_, lean_object* v_inst_373_, lean_object* v_as_374_, lean_object* v_b_375_, lean_object* v_f_376_){
_start:
{
size_t v_sz_377_; size_t v___x_378_; lean_object* v___x_379_; 
v_sz_377_ = lean_sarray_size(v_as_374_);
v___x_378_ = ((size_t)0ULL);
v___x_379_ = l_ByteArray_forInUnsafe_loop___redArg(v_inst_373_, v_as_374_, v_f_376_, v_sz_377_, v___x_378_, v_b_375_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_forIn_loop___redArg___lam__0___boxed(lean_object* v_toPure_380_, lean_object* v_inst_381_, lean_object* v_as_382_, lean_object* v_f_383_, lean_object* v_n_384_, lean_object* v_____do__lift_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_ByteArray_forIn_loop___redArg___lam__0(v_toPure_380_, v_inst_381_, v_as_382_, v_f_383_, v_n_384_, v_____do__lift_385_);
lean_dec(v_n_384_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_forIn_loop___redArg(lean_object* v_inst_387_, lean_object* v_as_388_, lean_object* v_f_389_, lean_object* v_i_390_, lean_object* v_b_391_){
_start:
{
lean_object* v_toApplicative_392_; lean_object* v_toBind_393_; lean_object* v_toPure_394_; lean_object* v_zero_395_; uint8_t v_isZero_396_; 
v_toApplicative_392_ = lean_ctor_get(v_inst_387_, 0);
v_toBind_393_ = lean_ctor_get(v_inst_387_, 1);
lean_inc(v_toBind_393_);
v_toPure_394_ = lean_ctor_get(v_toApplicative_392_, 1);
lean_inc(v_toPure_394_);
v_zero_395_ = lean_unsigned_to_nat(0u);
v_isZero_396_ = lean_nat_dec_eq(v_i_390_, v_zero_395_);
if (v_isZero_396_ == 1)
{
lean_object* v___x_397_; 
lean_dec(v_toBind_393_);
lean_dec(v_f_389_);
lean_dec_ref(v_as_388_);
lean_dec_ref(v_inst_387_);
v___x_397_ = lean_apply_2(v_toPure_394_, lean_box(0), v_b_391_);
return v___x_397_;
}
else
{
lean_object* v_one_398_; lean_object* v_n_399_; lean_object* v___f_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; uint8_t v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v_one_398_ = lean_unsigned_to_nat(1u);
v_n_399_ = lean_nat_sub(v_i_390_, v_one_398_);
lean_inc(v_n_399_);
lean_inc(v_f_389_);
lean_inc_ref(v_as_388_);
v___f_400_ = lean_alloc_closure((void*)(l_ByteArray_forIn_loop___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_400_, 0, v_toPure_394_);
lean_closure_set(v___f_400_, 1, v_inst_387_);
lean_closure_set(v___f_400_, 2, v_as_388_);
lean_closure_set(v___f_400_, 3, v_f_389_);
lean_closure_set(v___f_400_, 4, v_n_399_);
v___x_401_ = lean_byte_array_size(v_as_388_);
v___x_402_ = lean_nat_sub(v___x_401_, v_one_398_);
v___x_403_ = lean_nat_sub(v___x_402_, v_n_399_);
lean_dec(v_n_399_);
lean_dec(v___x_402_);
v___x_404_ = lean_byte_array_fget(v_as_388_, v___x_403_);
lean_dec(v___x_403_);
lean_dec_ref(v_as_388_);
v___x_405_ = lean_box(v___x_404_);
v___x_406_ = lean_apply_2(v_f_389_, v___x_405_, v_b_391_);
v___x_407_ = lean_apply_4(v_toBind_393_, lean_box(0), lean_box(0), v___x_406_, v___f_400_);
return v___x_407_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_forIn_loop___redArg___lam__0(lean_object* v_toPure_408_, lean_object* v_inst_409_, lean_object* v_as_410_, lean_object* v_f_411_, lean_object* v_n_412_, lean_object* v_____do__lift_413_){
_start:
{
if (lean_obj_tag(v_____do__lift_413_) == 0)
{
lean_object* v_a_414_; lean_object* v___x_415_; 
lean_dec(v_f_411_);
lean_dec_ref(v_as_410_);
lean_dec_ref(v_inst_409_);
v_a_414_ = lean_ctor_get(v_____do__lift_413_, 0);
lean_inc(v_a_414_);
lean_dec_ref_known(v_____do__lift_413_, 1);
v___x_415_ = lean_apply_2(v_toPure_408_, lean_box(0), v_a_414_);
return v___x_415_;
}
else
{
lean_object* v_a_416_; lean_object* v___x_417_; 
lean_dec(v_toPure_408_);
v_a_416_ = lean_ctor_get(v_____do__lift_413_, 0);
lean_inc(v_a_416_);
lean_dec_ref_known(v_____do__lift_413_, 1);
v___x_417_ = l_ByteArray_forIn_loop___redArg(v_inst_409_, v_as_410_, v_f_411_, v_n_412_, v_a_416_);
return v___x_417_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_forIn_loop___redArg___boxed(lean_object* v_inst_418_, lean_object* v_as_419_, lean_object* v_f_420_, lean_object* v_i_421_, lean_object* v_b_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_ByteArray_forIn_loop___redArg(v_inst_418_, v_as_419_, v_f_420_, v_i_421_, v_b_422_);
lean_dec(v_i_421_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_forIn_loop(lean_object* v_00_u03b2_424_, lean_object* v_m_425_, lean_object* v_inst_426_, lean_object* v_as_427_, lean_object* v_f_428_, lean_object* v_i_429_, lean_object* v_h_430_, lean_object* v_b_431_){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = l_ByteArray_forIn_loop___redArg(v_inst_426_, v_as_427_, v_f_428_, v_i_429_, v_b_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_forIn_loop___boxed(lean_object* v_00_u03b2_433_, lean_object* v_m_434_, lean_object* v_inst_435_, lean_object* v_as_436_, lean_object* v_f_437_, lean_object* v_i_438_, lean_object* v_h_439_, lean_object* v_b_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_ByteArray_forIn_loop(v_00_u03b2_433_, v_m_434_, v_inst_435_, v_as_436_, v_f_437_, v_i_438_, v_h_439_, v_b_440_);
lean_dec(v_i_438_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_instForInUInt8OfMonad___redArg___lam__0(lean_object* v_inst_442_, lean_object* v_00_u03b2_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
size_t v_sz_447_; size_t v___x_448_; lean_object* v___x_449_; 
v_sz_447_ = lean_sarray_size(v___y_444_);
v___x_448_ = ((size_t)0ULL);
v___x_449_ = l_ByteArray_forInUnsafe_loop___redArg(v_inst_442_, v___y_444_, v___y_446_, v_sz_447_, v___x_448_, v___y_445_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_instForInUInt8OfMonad___redArg(lean_object* v_inst_450_){
_start:
{
lean_object* v___f_451_; 
v___f_451_ = lean_alloc_closure((void*)(l_ByteArray_instForInUInt8OfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_451_, 0, v_inst_450_);
return v___f_451_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_instForInUInt8OfMonad(lean_object* v_m_452_, lean_object* v_inst_453_){
_start:
{
lean_object* v___f_454_; 
v___f_454_ = lean_alloc_closure((void*)(l_ByteArray_instForInUInt8OfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_454_, 0, v_inst_453_);
return v___f_454_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___redArg___lam__0___boxed(lean_object* v_i_455_, lean_object* v_inst_456_, lean_object* v_f_457_, lean_object* v_as_458_, lean_object* v_stop_459_, lean_object* v_____do__lift_460_){
_start:
{
size_t v_i_boxed_461_; size_t v_stop_boxed_462_; lean_object* v_res_463_; 
v_i_boxed_461_ = lean_unbox_usize(v_i_455_);
lean_dec(v_i_455_);
v_stop_boxed_462_ = lean_unbox_usize(v_stop_459_);
lean_dec(v_stop_459_);
v_res_463_ = l_ByteArray_foldlMUnsafe_fold___redArg___lam__0(v_i_boxed_461_, v_inst_456_, v_f_457_, v_as_458_, v_stop_boxed_462_, v_____do__lift_460_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___redArg(lean_object* v_inst_464_, lean_object* v_f_465_, lean_object* v_as_466_, size_t v_i_467_, size_t v_stop_468_, lean_object* v_b_469_){
_start:
{
lean_object* v_toApplicative_470_; lean_object* v_toBind_471_; lean_object* v_toPure_472_; uint8_t v___x_473_; 
v_toApplicative_470_ = lean_ctor_get(v_inst_464_, 0);
v_toBind_471_ = lean_ctor_get(v_inst_464_, 1);
lean_inc(v_toBind_471_);
v_toPure_472_ = lean_ctor_get(v_toApplicative_470_, 1);
v___x_473_ = lean_usize_dec_eq(v_i_467_, v_stop_468_);
if (v___x_473_ == 0)
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___f_476_; uint8_t v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_474_ = lean_box_usize(v_i_467_);
v___x_475_ = lean_box_usize(v_stop_468_);
lean_inc_ref(v_as_466_);
lean_inc(v_f_465_);
v___f_476_ = lean_alloc_closure((void*)(l_ByteArray_foldlMUnsafe_fold___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_476_, 0, v___x_474_);
lean_closure_set(v___f_476_, 1, v_inst_464_);
lean_closure_set(v___f_476_, 2, v_f_465_);
lean_closure_set(v___f_476_, 3, v_as_466_);
lean_closure_set(v___f_476_, 4, v___x_475_);
v___x_477_ = lean_byte_array_uget(v_as_466_, v_i_467_);
lean_dec_ref(v_as_466_);
v___x_478_ = lean_box(v___x_477_);
v___x_479_ = lean_apply_2(v_f_465_, v_b_469_, v___x_478_);
v___x_480_ = lean_apply_4(v_toBind_471_, lean_box(0), lean_box(0), v___x_479_, v___f_476_);
return v___x_480_;
}
else
{
lean_object* v___x_481_; 
lean_inc(v_toPure_472_);
lean_dec(v_toBind_471_);
lean_dec_ref(v_as_466_);
lean_dec(v_f_465_);
lean_dec_ref(v_inst_464_);
v___x_481_ = lean_apply_2(v_toPure_472_, lean_box(0), v_b_469_);
return v___x_481_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___redArg___lam__0(size_t v_i_482_, lean_object* v_inst_483_, lean_object* v_f_484_, lean_object* v_as_485_, size_t v_stop_486_, lean_object* v_____do__lift_487_){
_start:
{
size_t v___x_488_; size_t v___x_489_; lean_object* v___x_490_; 
v___x_488_ = ((size_t)1ULL);
v___x_489_ = lean_usize_add(v_i_482_, v___x_488_);
v___x_490_ = l_ByteArray_foldlMUnsafe_fold___redArg(v_inst_483_, v_f_484_, v_as_485_, v___x_489_, v_stop_486_, v_____do__lift_487_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___redArg___boxed(lean_object* v_inst_491_, lean_object* v_f_492_, lean_object* v_as_493_, lean_object* v_i_494_, lean_object* v_stop_495_, lean_object* v_b_496_){
_start:
{
size_t v_i_boxed_497_; size_t v_stop_boxed_498_; lean_object* v_res_499_; 
v_i_boxed_497_ = lean_unbox_usize(v_i_494_);
lean_dec(v_i_494_);
v_stop_boxed_498_ = lean_unbox_usize(v_stop_495_);
lean_dec(v_stop_495_);
v_res_499_ = l_ByteArray_foldlMUnsafe_fold___redArg(v_inst_491_, v_f_492_, v_as_493_, v_i_boxed_497_, v_stop_boxed_498_, v_b_496_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold(lean_object* v_00_u03b2_500_, lean_object* v_m_501_, lean_object* v_inst_502_, lean_object* v_f_503_, lean_object* v_as_504_, size_t v_i_505_, size_t v_stop_506_, lean_object* v_b_507_){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = l_ByteArray_foldlMUnsafe_fold___redArg(v_inst_502_, v_f_503_, v_as_504_, v_i_505_, v_stop_506_, v_b_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___boxed(lean_object* v_00_u03b2_509_, lean_object* v_m_510_, lean_object* v_inst_511_, lean_object* v_f_512_, lean_object* v_as_513_, lean_object* v_i_514_, lean_object* v_stop_515_, lean_object* v_b_516_){
_start:
{
size_t v_i_boxed_517_; size_t v_stop_boxed_518_; lean_object* v_res_519_; 
v_i_boxed_517_ = lean_unbox_usize(v_i_514_);
lean_dec(v_i_514_);
v_stop_boxed_518_ = lean_unbox_usize(v_stop_515_);
lean_dec(v_stop_515_);
v_res_519_ = l_ByteArray_foldlMUnsafe_fold(v_00_u03b2_509_, v_m_510_, v_inst_511_, v_f_512_, v_as_513_, v_i_boxed_517_, v_stop_boxed_518_, v_b_516_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe___redArg(lean_object* v_inst_520_, lean_object* v_f_521_, lean_object* v_init_522_, lean_object* v_as_523_, lean_object* v_start_524_, lean_object* v_stop_525_){
_start:
{
lean_object* v_toApplicative_526_; lean_object* v_toPure_527_; uint8_t v___x_528_; 
v_toApplicative_526_ = lean_ctor_get(v_inst_520_, 0);
v_toPure_527_ = lean_ctor_get(v_toApplicative_526_, 1);
v___x_528_ = lean_nat_dec_lt(v_start_524_, v_stop_525_);
if (v___x_528_ == 0)
{
lean_object* v___x_529_; 
lean_inc(v_toPure_527_);
lean_dec_ref(v_as_523_);
lean_dec(v_f_521_);
lean_dec_ref(v_inst_520_);
v___x_529_ = lean_apply_2(v_toPure_527_, lean_box(0), v_init_522_);
return v___x_529_;
}
else
{
lean_object* v___x_530_; uint8_t v___x_531_; 
v___x_530_ = lean_byte_array_size(v_as_523_);
v___x_531_ = lean_nat_dec_le(v_stop_525_, v___x_530_);
if (v___x_531_ == 0)
{
uint8_t v___x_532_; 
v___x_532_ = lean_nat_dec_lt(v_start_524_, v___x_530_);
if (v___x_532_ == 0)
{
lean_object* v___x_533_; 
lean_inc(v_toPure_527_);
lean_dec_ref(v_as_523_);
lean_dec(v_f_521_);
lean_dec_ref(v_inst_520_);
v___x_533_ = lean_apply_2(v_toPure_527_, lean_box(0), v_init_522_);
return v___x_533_;
}
else
{
size_t v___x_534_; size_t v___x_535_; lean_object* v___x_536_; 
v___x_534_ = lean_usize_of_nat(v_start_524_);
v___x_535_ = lean_usize_of_nat(v___x_530_);
v___x_536_ = l_ByteArray_foldlMUnsafe_fold___redArg(v_inst_520_, v_f_521_, v_as_523_, v___x_534_, v___x_535_, v_init_522_);
return v___x_536_;
}
}
else
{
size_t v___x_537_; size_t v___x_538_; lean_object* v___x_539_; 
v___x_537_ = lean_usize_of_nat(v_start_524_);
v___x_538_ = lean_usize_of_nat(v_stop_525_);
v___x_539_ = l_ByteArray_foldlMUnsafe_fold___redArg(v_inst_520_, v_f_521_, v_as_523_, v___x_537_, v___x_538_, v_init_522_);
return v___x_539_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe___redArg___boxed(lean_object* v_inst_540_, lean_object* v_f_541_, lean_object* v_init_542_, lean_object* v_as_543_, lean_object* v_start_544_, lean_object* v_stop_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_ByteArray_foldlMUnsafe___redArg(v_inst_540_, v_f_541_, v_init_542_, v_as_543_, v_start_544_, v_stop_545_);
lean_dec(v_stop_545_);
lean_dec(v_start_544_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe(lean_object* v_00_u03b2_547_, lean_object* v_m_548_, lean_object* v_inst_549_, lean_object* v_f_550_, lean_object* v_init_551_, lean_object* v_as_552_, lean_object* v_start_553_, lean_object* v_stop_554_){
_start:
{
lean_object* v_toApplicative_555_; lean_object* v_toPure_556_; uint8_t v___x_557_; 
v_toApplicative_555_ = lean_ctor_get(v_inst_549_, 0);
v_toPure_556_ = lean_ctor_get(v_toApplicative_555_, 1);
v___x_557_ = lean_nat_dec_lt(v_start_553_, v_stop_554_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; 
lean_inc(v_toPure_556_);
lean_dec_ref(v_as_552_);
lean_dec(v_f_550_);
lean_dec_ref(v_inst_549_);
v___x_558_ = lean_apply_2(v_toPure_556_, lean_box(0), v_init_551_);
return v___x_558_;
}
else
{
lean_object* v___x_559_; uint8_t v___x_560_; 
v___x_559_ = lean_byte_array_size(v_as_552_);
v___x_560_ = lean_nat_dec_le(v_stop_554_, v___x_559_);
if (v___x_560_ == 0)
{
uint8_t v___x_561_; 
v___x_561_ = lean_nat_dec_lt(v_start_553_, v___x_559_);
if (v___x_561_ == 0)
{
lean_object* v___x_562_; 
lean_inc(v_toPure_556_);
lean_dec_ref(v_as_552_);
lean_dec(v_f_550_);
lean_dec_ref(v_inst_549_);
v___x_562_ = lean_apply_2(v_toPure_556_, lean_box(0), v_init_551_);
return v___x_562_;
}
else
{
size_t v___x_563_; size_t v___x_564_; lean_object* v___x_565_; 
v___x_563_ = lean_usize_of_nat(v_start_553_);
v___x_564_ = lean_usize_of_nat(v___x_559_);
v___x_565_ = l_ByteArray_foldlMUnsafe_fold___redArg(v_inst_549_, v_f_550_, v_as_552_, v___x_563_, v___x_564_, v_init_551_);
return v___x_565_;
}
}
else
{
size_t v___x_566_; size_t v___x_567_; lean_object* v___x_568_; 
v___x_566_ = lean_usize_of_nat(v_start_553_);
v___x_567_ = lean_usize_of_nat(v_stop_554_);
v___x_568_ = l_ByteArray_foldlMUnsafe_fold___redArg(v_inst_549_, v_f_550_, v_as_552_, v___x_566_, v___x_567_, v_init_551_);
return v___x_568_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe___boxed(lean_object* v_00_u03b2_569_, lean_object* v_m_570_, lean_object* v_inst_571_, lean_object* v_f_572_, lean_object* v_init_573_, lean_object* v_as_574_, lean_object* v_start_575_, lean_object* v_stop_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_ByteArray_foldlMUnsafe(v_00_u03b2_569_, v_m_570_, v_inst_571_, v_f_572_, v_init_573_, v_as_574_, v_start_575_, v_stop_576_);
lean_dec(v_stop_576_);
lean_dec(v_start_575_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlM_loop___redArg___lam__0___boxed(lean_object* v_j_578_, lean_object* v_inst_579_, lean_object* v_f_580_, lean_object* v_as_581_, lean_object* v_stop_582_, lean_object* v_n_583_, lean_object* v_____do__lift_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_ByteArray_foldlM_loop___redArg___lam__0(v_j_578_, v_inst_579_, v_f_580_, v_as_581_, v_stop_582_, v_n_583_, v_____do__lift_584_);
lean_dec(v_n_583_);
lean_dec(v_j_578_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlM_loop___redArg(lean_object* v_inst_586_, lean_object* v_f_587_, lean_object* v_as_588_, lean_object* v_stop_589_, lean_object* v_i_590_, lean_object* v_j_591_, lean_object* v_b_592_){
_start:
{
lean_object* v_toApplicative_593_; lean_object* v_toBind_594_; lean_object* v_toPure_595_; uint8_t v___x_596_; 
v_toApplicative_593_ = lean_ctor_get(v_inst_586_, 0);
v_toBind_594_ = lean_ctor_get(v_inst_586_, 1);
lean_inc(v_toBind_594_);
v_toPure_595_ = lean_ctor_get(v_toApplicative_593_, 1);
v___x_596_ = lean_nat_dec_lt(v_j_591_, v_stop_589_);
if (v___x_596_ == 0)
{
lean_object* v___x_597_; 
lean_inc(v_toPure_595_);
lean_dec(v_toBind_594_);
lean_dec(v_j_591_);
lean_dec(v_stop_589_);
lean_dec_ref(v_as_588_);
lean_dec(v_f_587_);
lean_dec_ref(v_inst_586_);
v___x_597_ = lean_apply_2(v_toPure_595_, lean_box(0), v_b_592_);
return v___x_597_;
}
else
{
lean_object* v_zero_598_; uint8_t v_isZero_599_; 
v_zero_598_ = lean_unsigned_to_nat(0u);
v_isZero_599_ = lean_nat_dec_eq(v_i_590_, v_zero_598_);
if (v_isZero_599_ == 1)
{
lean_object* v___x_600_; 
lean_inc(v_toPure_595_);
lean_dec(v_toBind_594_);
lean_dec(v_j_591_);
lean_dec(v_stop_589_);
lean_dec_ref(v_as_588_);
lean_dec(v_f_587_);
lean_dec_ref(v_inst_586_);
v___x_600_ = lean_apply_2(v_toPure_595_, lean_box(0), v_b_592_);
return v___x_600_;
}
else
{
lean_object* v_one_601_; lean_object* v_n_602_; lean_object* v___f_603_; uint8_t v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v_one_601_ = lean_unsigned_to_nat(1u);
v_n_602_ = lean_nat_sub(v_i_590_, v_one_601_);
lean_inc_ref(v_as_588_);
lean_inc(v_f_587_);
lean_inc(v_j_591_);
v___f_603_ = lean_alloc_closure((void*)(l_ByteArray_foldlM_loop___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_603_, 0, v_j_591_);
lean_closure_set(v___f_603_, 1, v_inst_586_);
lean_closure_set(v___f_603_, 2, v_f_587_);
lean_closure_set(v___f_603_, 3, v_as_588_);
lean_closure_set(v___f_603_, 4, v_stop_589_);
lean_closure_set(v___f_603_, 5, v_n_602_);
v___x_604_ = lean_byte_array_fget(v_as_588_, v_j_591_);
lean_dec(v_j_591_);
lean_dec_ref(v_as_588_);
v___x_605_ = lean_box(v___x_604_);
v___x_606_ = lean_apply_2(v_f_587_, v_b_592_, v___x_605_);
v___x_607_ = lean_apply_4(v_toBind_594_, lean_box(0), lean_box(0), v___x_606_, v___f_603_);
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
uint8_t v_x2_185__boxed_656_; lean_object* v_res_657_; 
v_x2_185__boxed_656_ = lean_unbox(v_x2_655_);
v_res_657_ = l_ByteArray_foldl___redArg___lam__0(v_f_653_, v_x1_654_, v_x2_185__boxed_656_);
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
LEAN_EXPORT uint8_t l_ByteArray_Iterator_curr(lean_object* v_x_763_){
_start:
{
lean_object* v_array_764_; lean_object* v_idx_765_; lean_object* v___x_766_; uint8_t v___x_767_; 
v_array_764_ = lean_ctor_get(v_x_763_, 0);
v_idx_765_ = lean_ctor_get(v_x_763_, 1);
v___x_766_ = lean_byte_array_size(v_array_764_);
v___x_767_ = lean_nat_dec_lt(v_idx_765_, v___x_766_);
if (v___x_767_ == 0)
{
uint8_t v___x_768_; 
v___x_768_ = 0;
return v___x_768_;
}
else
{
uint8_t v___x_769_; 
v___x_769_ = lean_byte_array_fget(v_array_764_, v_idx_765_);
return v___x_769_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_curr___boxed(lean_object* v_x_770_){
_start:
{
uint8_t v_res_771_; lean_object* v_r_772_; 
v_res_771_ = l_ByteArray_Iterator_curr(v_x_770_);
lean_dec_ref(v_x_770_);
v_r_772_ = lean_box(v_res_771_);
return v_r_772_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_next(lean_object* v_x_773_){
_start:
{
lean_object* v_array_774_; lean_object* v_idx_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_784_; 
v_array_774_ = lean_ctor_get(v_x_773_, 0);
v_idx_775_ = lean_ctor_get(v_x_773_, 1);
v_isSharedCheck_784_ = !lean_is_exclusive(v_x_773_);
if (v_isSharedCheck_784_ == 0)
{
v___x_777_ = v_x_773_;
v_isShared_778_ = v_isSharedCheck_784_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_idx_775_);
lean_inc(v_array_774_);
lean_dec(v_x_773_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_784_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_782_; 
v___x_779_ = lean_unsigned_to_nat(1u);
v___x_780_ = lean_nat_add(v_idx_775_, v___x_779_);
lean_dec(v_idx_775_);
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 1, v___x_780_);
v___x_782_ = v___x_777_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_array_774_);
lean_ctor_set(v_reuseFailAlloc_783_, 1, v___x_780_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_prev(lean_object* v_x_785_){
_start:
{
lean_object* v_array_786_; lean_object* v_idx_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_796_; 
v_array_786_ = lean_ctor_get(v_x_785_, 0);
v_idx_787_ = lean_ctor_get(v_x_785_, 1);
v_isSharedCheck_796_ = !lean_is_exclusive(v_x_785_);
if (v_isSharedCheck_796_ == 0)
{
v___x_789_ = v_x_785_;
v_isShared_790_ = v_isSharedCheck_796_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_idx_787_);
lean_inc(v_array_786_);
lean_dec(v_x_785_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_796_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_794_; 
v___x_791_ = lean_unsigned_to_nat(1u);
v___x_792_ = lean_nat_sub(v_idx_787_, v___x_791_);
lean_dec(v_idx_787_);
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 1, v___x_792_);
v___x_794_ = v___x_789_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_array_786_);
lean_ctor_set(v_reuseFailAlloc_795_, 1, v___x_792_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
}
LEAN_EXPORT uint8_t l_ByteArray_Iterator_hasNext(lean_object* v_x_797_){
_start:
{
lean_object* v_array_798_; lean_object* v_idx_799_; lean_object* v___x_800_; uint8_t v___x_801_; 
v_array_798_ = lean_ctor_get(v_x_797_, 0);
v_idx_799_ = lean_ctor_get(v_x_797_, 1);
v___x_800_ = lean_byte_array_size(v_array_798_);
v___x_801_ = lean_nat_dec_lt(v_idx_799_, v___x_800_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_hasNext___boxed(lean_object* v_x_802_){
_start:
{
uint8_t v_res_803_; lean_object* v_r_804_; 
v_res_803_ = l_ByteArray_Iterator_hasNext(v_x_802_);
lean_dec_ref(v_x_802_);
v_r_804_ = lean_box(v_res_803_);
return v_r_804_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Basic_0__ByteArray_Iterator_remainingBytes_match__1_splitter___redArg(lean_object* v_x_805_, lean_object* v_h__1_806_){
_start:
{
lean_object* v_array_807_; lean_object* v_idx_808_; lean_object* v___x_809_; 
v_array_807_ = lean_ctor_get(v_x_805_, 0);
lean_inc_ref(v_array_807_);
v_idx_808_ = lean_ctor_get(v_x_805_, 1);
lean_inc(v_idx_808_);
lean_dec_ref(v_x_805_);
v___x_809_ = lean_apply_2(v_h__1_806_, v_array_807_, v_idx_808_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Basic_0__ByteArray_Iterator_remainingBytes_match__1_splitter(lean_object* v_motive_810_, lean_object* v_x_811_, lean_object* v_h__1_812_){
_start:
{
lean_object* v_array_813_; lean_object* v_idx_814_; lean_object* v___x_815_; 
v_array_813_ = lean_ctor_get(v_x_811_, 0);
lean_inc_ref(v_array_813_);
v_idx_814_ = lean_ctor_get(v_x_811_, 1);
lean_inc(v_idx_814_);
lean_dec_ref(v_x_811_);
v___x_815_ = lean_apply_2(v_h__1_812_, v_array_813_, v_idx_814_);
return v___x_815_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_Iterator_curr_x27___redArg(lean_object* v_it_816_){
_start:
{
lean_object* v_array_817_; lean_object* v_idx_818_; uint8_t v___x_819_; 
v_array_817_ = lean_ctor_get(v_it_816_, 0);
v_idx_818_ = lean_ctor_get(v_it_816_, 1);
v___x_819_ = lean_byte_array_fget(v_array_817_, v_idx_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_curr_x27___redArg___boxed(lean_object* v_it_820_){
_start:
{
uint8_t v_res_821_; lean_object* v_r_822_; 
v_res_821_ = l_ByteArray_Iterator_curr_x27___redArg(v_it_820_);
lean_dec_ref(v_it_820_);
v_r_822_ = lean_box(v_res_821_);
return v_r_822_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_Iterator_curr_x27(lean_object* v_it_823_, lean_object* v_h_824_){
_start:
{
lean_object* v_array_825_; lean_object* v_idx_826_; uint8_t v___x_827_; 
v_array_825_ = lean_ctor_get(v_it_823_, 0);
v_idx_826_ = lean_ctor_get(v_it_823_, 1);
v___x_827_ = lean_byte_array_fget(v_array_825_, v_idx_826_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_curr_x27___boxed(lean_object* v_it_828_, lean_object* v_h_829_){
_start:
{
uint8_t v_res_830_; lean_object* v_r_831_; 
v_res_830_ = l_ByteArray_Iterator_curr_x27(v_it_828_, v_h_829_);
lean_dec_ref(v_it_828_);
v_r_831_ = lean_box(v_res_830_);
return v_r_831_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_next_x27___redArg(lean_object* v_it_832_){
_start:
{
lean_object* v_array_833_; lean_object* v_idx_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_843_; 
v_array_833_ = lean_ctor_get(v_it_832_, 0);
v_idx_834_ = lean_ctor_get(v_it_832_, 1);
v_isSharedCheck_843_ = !lean_is_exclusive(v_it_832_);
if (v_isSharedCheck_843_ == 0)
{
v___x_836_ = v_it_832_;
v_isShared_837_ = v_isSharedCheck_843_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_idx_834_);
lean_inc(v_array_833_);
lean_dec(v_it_832_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_843_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_841_; 
v___x_838_ = lean_unsigned_to_nat(1u);
v___x_839_ = lean_nat_add(v_idx_834_, v___x_838_);
lean_dec(v_idx_834_);
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 1, v___x_839_);
v___x_841_ = v___x_836_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_array_833_);
lean_ctor_set(v_reuseFailAlloc_842_, 1, v___x_839_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_next_x27(lean_object* v_it_844_, lean_object* v___h_845_){
_start:
{
lean_object* v_array_846_; lean_object* v_idx_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_856_; 
v_array_846_ = lean_ctor_get(v_it_844_, 0);
v_idx_847_ = lean_ctor_get(v_it_844_, 1);
v_isSharedCheck_856_ = !lean_is_exclusive(v_it_844_);
if (v_isSharedCheck_856_ == 0)
{
v___x_849_ = v_it_844_;
v_isShared_850_ = v_isSharedCheck_856_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_idx_847_);
lean_inc(v_array_846_);
lean_dec(v_it_844_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_856_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_854_; 
v___x_851_ = lean_unsigned_to_nat(1u);
v___x_852_ = lean_nat_add(v_idx_847_, v___x_851_);
lean_dec(v_idx_847_);
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 1, v___x_852_);
v___x_854_ = v___x_849_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_array_846_);
lean_ctor_set(v_reuseFailAlloc_855_, 1, v___x_852_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
}
LEAN_EXPORT uint8_t l_ByteArray_Iterator_hasPrev(lean_object* v_x_857_){
_start:
{
lean_object* v_idx_858_; lean_object* v___x_859_; uint8_t v___x_860_; 
v_idx_858_ = lean_ctor_get(v_x_857_, 1);
v___x_859_ = lean_unsigned_to_nat(0u);
v___x_860_ = lean_nat_dec_lt(v___x_859_, v_idx_858_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_hasPrev___boxed(lean_object* v_x_861_){
_start:
{
uint8_t v_res_862_; lean_object* v_r_863_; 
v_res_862_ = l_ByteArray_Iterator_hasPrev(v_x_861_);
lean_dec_ref(v_x_861_);
v_r_863_ = lean_box(v_res_862_);
return v_r_863_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_toEnd(lean_object* v_x_864_){
_start:
{
lean_object* v_array_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_873_; 
v_array_865_ = lean_ctor_get(v_x_864_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v_x_864_);
if (v_isSharedCheck_873_ == 0)
{
lean_object* v_unused_874_; 
v_unused_874_ = lean_ctor_get(v_x_864_, 1);
lean_dec(v_unused_874_);
v___x_867_ = v_x_864_;
v_isShared_868_ = v_isSharedCheck_873_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_array_865_);
lean_dec(v_x_864_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_873_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_869_; lean_object* v___x_871_; 
v___x_869_ = lean_byte_array_size(v_array_865_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 1, v___x_869_);
v___x_871_ = v___x_867_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_array_865_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v___x_869_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_forward(lean_object* v_x_875_, lean_object* v_x_876_){
_start:
{
lean_object* v_array_877_; lean_object* v_idx_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_886_; 
v_array_877_ = lean_ctor_get(v_x_875_, 0);
v_idx_878_ = lean_ctor_get(v_x_875_, 1);
v_isSharedCheck_886_ = !lean_is_exclusive(v_x_875_);
if (v_isSharedCheck_886_ == 0)
{
v___x_880_ = v_x_875_;
v_isShared_881_ = v_isSharedCheck_886_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_idx_878_);
lean_inc(v_array_877_);
lean_dec(v_x_875_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_886_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_882_; lean_object* v___x_884_; 
v___x_882_ = lean_nat_add(v_idx_878_, v_x_876_);
lean_dec(v_idx_878_);
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 1, v___x_882_);
v___x_884_ = v___x_880_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_array_877_);
lean_ctor_set(v_reuseFailAlloc_885_, 1, v___x_882_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_forward___boxed(lean_object* v_x_887_, lean_object* v_x_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_ByteArray_Iterator_forward(v_x_887_, v_x_888_);
lean_dec(v_x_888_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_nextn(lean_object* v_a_890_, lean_object* v_a_891_){
_start:
{
lean_object* v_array_892_; lean_object* v_idx_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_901_; 
v_array_892_ = lean_ctor_get(v_a_890_, 0);
v_idx_893_ = lean_ctor_get(v_a_890_, 1);
v_isSharedCheck_901_ = !lean_is_exclusive(v_a_890_);
if (v_isSharedCheck_901_ == 0)
{
v___x_895_ = v_a_890_;
v_isShared_896_ = v_isSharedCheck_901_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_idx_893_);
lean_inc(v_array_892_);
lean_dec(v_a_890_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_901_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_897_; lean_object* v___x_899_; 
v___x_897_ = lean_nat_add(v_idx_893_, v_a_891_);
lean_dec(v_idx_893_);
if (v_isShared_896_ == 0)
{
lean_ctor_set(v___x_895_, 1, v___x_897_);
v___x_899_ = v___x_895_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_array_892_);
lean_ctor_set(v_reuseFailAlloc_900_, 1, v___x_897_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_nextn___boxed(lean_object* v_a_902_, lean_object* v_a_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l_ByteArray_Iterator_nextn(v_a_902_, v_a_903_);
lean_dec(v_a_903_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_prevn(lean_object* v_x_905_, lean_object* v_x_906_){
_start:
{
lean_object* v_array_907_; lean_object* v_idx_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_916_; 
v_array_907_ = lean_ctor_get(v_x_905_, 0);
v_idx_908_ = lean_ctor_get(v_x_905_, 1);
v_isSharedCheck_916_ = !lean_is_exclusive(v_x_905_);
if (v_isSharedCheck_916_ == 0)
{
v___x_910_ = v_x_905_;
v_isShared_911_ = v_isSharedCheck_916_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_idx_908_);
lean_inc(v_array_907_);
lean_dec(v_x_905_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_916_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_912_; lean_object* v___x_914_; 
v___x_912_ = lean_nat_sub(v_idx_908_, v_x_906_);
lean_dec(v_idx_908_);
if (v_isShared_911_ == 0)
{
lean_ctor_set(v___x_910_, 1, v___x_912_);
v___x_914_ = v___x_910_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_array_907_);
lean_ctor_set(v_reuseFailAlloc_915_, 1, v___x_912_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_Iterator_prevn___boxed(lean_object* v_x_917_, lean_object* v_x_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_ByteArray_Iterator_prevn(v_x_917_, v_x_918_);
lean_dec(v_x_918_);
return v_res_919_;
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
