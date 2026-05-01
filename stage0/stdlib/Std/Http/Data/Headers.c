// Lean compiler output
// Module: Std.Http.Data.Headers
// Imports: public import Std.Http.Data.Headers.Basic public import Std.Http.Data.Headers.Name public import Std.Http.Data.Headers.Value
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_String_decEq___boxed(lean_object*, lean_object*);
lean_object* l_String_hash___boxed(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Internal_IndexMultiMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Std_Http_Header_instReprName_repr___redArg(lean_object*);
lean_object* l_Std_Http_Header_instReprValue_repr___redArg(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_mapFinIdxM_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_Http_Header_instBEqValue_beq(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___lam__0___boxed(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_byte_array_size(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_splitToSubslice___redArg(lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Std_Http_Header_Name_ofString_x21(lean_object*);
lean_object* l_Std_Http_Header_Value_ofString_x21(lean_object*);
lean_object* l_Std_Http_Header_Name_ofString_x3f(lean_object*);
lean_object* l_Std_Http_Header_Value_ofString_x3f(lean_object*);
static const lean_array_object l_Std_Http_instInhabitedHeaders_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Http_instInhabitedHeaders_default___closed__0 = (const lean_object*)&l_Std_Http_instInhabitedHeaders_default___closed__0_value;
static lean_once_cell_t l_Std_Http_instInhabitedHeaders_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_instInhabitedHeaders_default___closed__1;
static lean_once_cell_t l_Std_Http_instInhabitedHeaders_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_instInhabitedHeaders_default___closed__2;
static lean_once_cell_t l_Std_Http_instInhabitedHeaders_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_instInhabitedHeaders_default___closed__3;
LEAN_EXPORT lean_object* l_Std_Http_instInhabitedHeaders_default;
LEAN_EXPORT lean_object* l_Std_Http_instInhabitedHeaders;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Http_instReprHeaders_repr_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8_spec__13_spec__15_spec__17(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8_spec__13_spec__15(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8_spec__13___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8_spec__13(lean_object*, lean_object*);
static const lean_string_object l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__0 = (const lean_object*)&l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__0_value;
static const lean_string_object l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__1 = (const lean_object*)&l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__1_value;
static const lean_ctor_object l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__1_value)}};
static const lean_object* l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__2 = (const lean_object*)&l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__2_value;
static const lean_ctor_object l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__3 = (const lean_object*)&l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__3_value;
static const lean_string_object l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__4 = (const lean_object*)&l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__4_value;
static lean_once_cell_t l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__5;
static lean_once_cell_t l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__6;
static const lean_ctor_object l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__0_value)}};
static const lean_object* l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__7 = (const lean_object*)&l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__7_value;
static const lean_ctor_object l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__4_value)}};
static const lean_object* l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__8 = (const lean_object*)&l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__8_value;
static const lean_string_object l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "#[]"};
static const lean_object* l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__9 = (const lean_object*)&l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__9_value;
static const lean_ctor_object l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__9_value)}};
static const lean_object* l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__10 = (const lean_object*)&l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__10_value;
LEAN_EXPORT lean_object* l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2_spec__3_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*);
static const lean_string_object l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__0 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__0_value;
static const lean_string_object l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__1 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__1_value;
static lean_once_cell_t l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__2;
static lean_once_cell_t l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__3;
static const lean_ctor_object l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__0_value)}};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__4 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__4_value;
static const lean_ctor_object l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__1_value)}};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__5 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__6_spec__10_spec__16(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__6_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__6(lean_object*, lean_object*);
static const lean_string_object l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__0_value)}};
static const lean_object* l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__1 = (const lean_object*)&l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__1_value;
static const lean_string_object l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__2 = (const lean_object*)&l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__2_value;
static lean_once_cell_t l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__3;
static lean_once_cell_t l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__4;
static const lean_ctor_object l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__2_value)}};
static const lean_object* l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__5 = (const lean_object*)&l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__3_spec__5_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "entries"};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__0 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__0_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__1 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__1_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__1_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__2 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__2_value;
static const lean_string_object l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__3 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__3_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__3_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__4 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__4_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__2_value),((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__4_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__5 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__5_value;
static const lean_string_object l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__6 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__6_value;
static lean_once_cell_t l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__7;
static const lean_string_object l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "indexes"};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__8 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__8_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__8_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__9 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__9_value;
static const lean_string_object l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.HashMap.ofList "};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__10 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__10_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__10_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__11 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__11_value;
static const lean_string_object l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "validity"};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__12 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__12_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__12_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__13 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__13_value;
static const lean_string_object l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__14 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__14_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__14_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__15 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__15_value;
static const lean_string_object l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__16 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__16_value;
static lean_once_cell_t l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__17;
static lean_once_cell_t l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__18;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__6_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__19 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__19_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__16_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__20 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__20_value;
LEAN_EXPORT lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg(lean_object*);
static const lean_string_object l_Std_Http_instReprHeaders_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "map"};
static const lean_object* l_Std_Http_instReprHeaders_repr___redArg___closed__0 = (const lean_object*)&l_Std_Http_instReprHeaders_repr___redArg___closed__0_value;
static const lean_ctor_object l_Std_Http_instReprHeaders_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_instReprHeaders_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Http_instReprHeaders_repr___redArg___closed__1 = (const lean_object*)&l_Std_Http_instReprHeaders_repr___redArg___closed__1_value;
static const lean_ctor_object l_Std_Http_instReprHeaders_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_instReprHeaders_repr___redArg___closed__1_value)}};
static const lean_object* l_Std_Http_instReprHeaders_repr___redArg___closed__2 = (const lean_object*)&l_Std_Http_instReprHeaders_repr___redArg___closed__2_value;
static const lean_ctor_object l_Std_Http_instReprHeaders_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Http_instReprHeaders_repr___redArg___closed__2_value),((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__4_value)}};
static const lean_object* l_Std_Http_instReprHeaders_repr___redArg___closed__3 = (const lean_object*)&l_Std_Http_instReprHeaders_repr___redArg___closed__3_value;
static lean_once_cell_t l_Std_Http_instReprHeaders_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_instReprHeaders_repr___redArg___closed__4;
LEAN_EXPORT lean_object* l_Std_Http_instReprHeaders_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instReprHeaders_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instReprHeaders_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_instReprHeaders___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_instReprHeaders_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_instReprHeaders___closed__0 = (const lean_object*)&l_Std_Http_instReprHeaders___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_instReprHeaders = (const lean_object*)&l_Std_Http_instReprHeaders___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_instMembershipNameHeaders;
static const lean_closure_object l_Std_Http_instDecidableMemNameHeaders___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_decEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_instDecidableMemNameHeaders___closed__0 = (const lean_object*)&l_Std_Http_instDecidableMemNameHeaders___closed__0_value;
static const lean_closure_object l_Std_Http_instDecidableMemNameHeaders___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_instDecidableMemNameHeaders___closed__1 = (const lean_object*)&l_Std_Http_instDecidableMemNameHeaders___closed__1_value;
LEAN_EXPORT uint8_t l_Std_Http_instDecidableMemNameHeaders(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instDecidableMemNameHeaders___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_get___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_get___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_get___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_getAll___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_getAll___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Headers_getAll___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Headers_getAll___redArg___closed__0 = (const lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__0_value;
static const lean_closure_object l_Std_Http_Headers_getAll___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Headers_getAll___redArg___closed__1 = (const lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__1_value;
static const lean_closure_object l_Std_Http_Headers_getAll___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Headers_getAll___redArg___closed__2 = (const lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__2_value;
static const lean_closure_object l_Std_Http_Headers_getAll___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Headers_getAll___redArg___closed__3 = (const lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__3_value;
static const lean_closure_object l_Std_Http_Headers_getAll___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Headers_getAll___redArg___closed__4 = (const lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__4_value;
static const lean_closure_object l_Std_Http_Headers_getAll___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Headers_getAll___redArg___closed__5 = (const lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__5_value;
static const lean_closure_object l_Std_Http_Headers_getAll___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Headers_getAll___redArg___closed__6 = (const lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__6_value;
static const lean_ctor_object l_Std_Http_Headers_getAll___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__0_value),((lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__1_value)}};
static const lean_object* l_Std_Http_Headers_getAll___redArg___closed__7 = (const lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__7_value;
static const lean_ctor_object l_Std_Http_Headers_getAll___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__7_value),((lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__2_value),((lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__3_value),((lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__4_value),((lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__5_value)}};
static const lean_object* l_Std_Http_Headers_getAll___redArg___closed__8 = (const lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__8_value;
static const lean_ctor_object l_Std_Http_Headers_getAll___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__8_value),((lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__6_value)}};
static const lean_object* l_Std_Http_Headers_getAll___redArg___closed__9 = (const lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Std_Http_Headers_getAll___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_getAll(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_getAll_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_get_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_get_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_hasEntry___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_hasEntry___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Http_Headers_hasEntry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_Headers_hasEntry___closed__0 = (const lean_object*)&l_Std_Http_Headers_hasEntry___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Http_Headers_hasEntry(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_hasEntry___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_getLast_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_getD(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_getD___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Http_Headers_get_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_Http_Headers_get_x21___closed__0 = (const lean_object*)&l_Std_Http_Headers_get_x21___closed__0_value;
static const lean_string_object l_Std_Http_Headers_get_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l_Std_Http_Headers_get_x21___closed__1 = (const lean_object*)&l_Std_Http_Headers_get_x21___closed__1_value;
static const lean_string_object l_Std_Http_Headers_get_x21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l_Std_Http_Headers_get_x21___closed__2 = (const lean_object*)&l_Std_Http_Headers_get_x21___closed__2_value;
static const lean_string_object l_Std_Http_Headers_get_x21___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l_Std_Http_Headers_get_x21___closed__3 = (const lean_object*)&l_Std_Http_Headers_get_x21___closed__3_value;
static lean_once_cell_t l_Std_Http_Headers_get_x21___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Headers_get_x21___closed__4;
LEAN_EXPORT lean_object* l_Std_Http_Headers_get_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_get_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_insert___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_insert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_insert_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_insert_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_insertMany___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_insertMany(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__0 = (const lean_object*)&l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__0_value;
static lean_once_cell_t l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0(lean_object*);
static lean_once_cell_t l_Std_Http_Headers_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Headers_empty___closed__0;
LEAN_EXPORT lean_object* l_Std_Http_Headers_empty;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1___redArg(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_ofList(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Headers_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_contains___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_erase___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_erase___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_erase___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Headers_erase___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Headers_erase___lam__1, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_Http_instDecidableMemNameHeaders___closed__0_value),((lean_object*)&l_Std_Http_instDecidableMemNameHeaders___closed__1_value)} };
static const lean_object* l_Std_Http_Headers_erase___closed__0 = (const lean_object*)&l_Std_Http_Headers_erase___closed__0_value;
static lean_once_cell_t l_Std_Http_Headers_erase___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Headers_erase___closed__1;
LEAN_EXPORT lean_object* l_Std_Http_Headers_erase(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_size___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Headers_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_isEmpty___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_merge(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_merge___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toList___at___00Std_Http_Headers_toList_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toList___at___00Std_Http_Headers_toList_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_toList(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_toArray(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_toArray___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_fold___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_fold___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_fold(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_fold___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Headers_mapValues_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Headers_mapValues_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_mapValues_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_mapValues_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_mapValues(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_filterMap(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_filterMap___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_filter___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_filter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_filter___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_update_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_update_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_update(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_update___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_replaceLast(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_instToString___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_instToString___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Http_Headers_instToString___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Std_Http_Headers_instToString___lam__1___closed__0 = (const lean_object*)&l_Std_Http_Headers_instToString___lam__1___closed__0_value;
static const lean_closure_object l_Std_Http_Headers_instToString___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Headers_instToString___lam__1___closed__1 = (const lean_object*)&l_Std_Http_Headers_instToString___lam__1___closed__1_value;
static const lean_string_object l_Std_Http_Headers_instToString___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Std_Http_Headers_instToString___lam__1___closed__2 = (const lean_object*)&l_Std_Http_Headers_instToString___lam__1___closed__2_value;
static lean_once_cell_t l_Std_Http_Headers_instToString___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Headers_instToString___lam__1___closed__3;
LEAN_EXPORT lean_object* l_Std_Http_Headers_instToString___lam__1___boxed__const__1;
LEAN_EXPORT lean_object* l_Std_Http_Headers_instToString___lam__1(lean_object*);
static const lean_string_object l_Std_Http_Headers_instToString___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\r\n"};
static const lean_object* l_Std_Http_Headers_instToString___lam__2___closed__0 = (const lean_object*)&l_Std_Http_Headers_instToString___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Headers_instToString___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Headers_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Headers_instToString___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Headers_instToString___closed__0 = (const lean_object*)&l_Std_Http_Headers_instToString___closed__0_value;
static const lean_closure_object l_Std_Http_Headers_instToString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Headers_instToString___lam__2, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Headers_instToString___closed__0_value)} };
static const lean_object* l_Std_Http_Headers_instToString___closed__1 = (const lean_object*)&l_Std_Http_Headers_instToString___closed__1_value;
LEAN_EXPORT const lean_object* l_Std_Http_Headers_instToString = (const lean_object*)&l_Std_Http_Headers_instToString___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Headers_instEncodeV11___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_instEncodeV11___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_instEncodeV11___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_instEncodeV11___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_instEncodeV11___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_instEncodeV11___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Headers_instEncodeV11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Headers_instEncodeV11___lam__1___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Headers_instEncodeV11___closed__0 = (const lean_object*)&l_Std_Http_Headers_instEncodeV11___closed__0_value;
static const lean_closure_object l_Std_Http_Headers_instEncodeV11___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Headers_instEncodeV11___lam__2___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Headers_instEncodeV11___closed__0_value)} };
static const lean_object* l_Std_Http_Headers_instEncodeV11___closed__1 = (const lean_object*)&l_Std_Http_Headers_instEncodeV11___closed__1_value;
LEAN_EXPORT const lean_object* l_Std_Http_Headers_instEncodeV11 = (const lean_object*)&l_Std_Http_Headers_instEncodeV11___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Headers_instEmptyCollection;
LEAN_EXPORT lean_object* l_Std_Http_Headers_instSingletonProdNameValue___lam__1(lean_object*);
static const lean_closure_object l_Std_Http_Headers_instSingletonProdNameValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Headers_instSingletonProdNameValue___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Headers_instSingletonProdNameValue___closed__0 = (const lean_object*)&l_Std_Http_Headers_instSingletonProdNameValue___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Headers_instSingletonProdNameValue = (const lean_object*)&l_Std_Http_Headers_instSingletonProdNameValue___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Headers_instInsertProdNameValue___lam__1(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Headers_instInsertProdNameValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Headers_instInsertProdNameValue___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Headers_instInsertProdNameValue___closed__0 = (const lean_object*)&l_Std_Http_Headers_instInsertProdNameValue___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Headers_instInsertProdNameValue = (const lean_object*)&l_Std_Http_Headers_instInsertProdNameValue___closed__0_value;
static const lean_closure_object l_Std_Http_Headers_instUnion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Headers_merge___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Headers_instUnion___closed__0 = (const lean_object*)&l_Std_Http_Headers_instUnion___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Headers_instUnion = (const lean_object*)&l_Std_Http_Headers_instUnion___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Headers_instForInProdNameValueOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_instForInProdNameValueOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_instForInProdNameValueOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_instForInProdNameValueOfMonad(lean_object*, lean_object*);
static lean_object* _init_l_Std_Http_instInhabitedHeaders_default___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_3_ = lean_box(0);
v___x_4_ = lean_unsigned_to_nat(16u);
v___x_5_ = lean_mk_array(v___x_4_, v___x_3_);
return v___x_5_;
}
}
static lean_object* _init_l_Std_Http_instInhabitedHeaders_default___closed__2(void){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_6_ = lean_obj_once(&l_Std_Http_instInhabitedHeaders_default___closed__1, &l_Std_Http_instInhabitedHeaders_default___closed__1_once, _init_l_Std_Http_instInhabitedHeaders_default___closed__1);
v___x_7_ = lean_unsigned_to_nat(0u);
v___x_8_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_8_, 0, v___x_7_);
lean_ctor_set(v___x_8_, 1, v___x_6_);
return v___x_8_;
}
}
static lean_object* _init_l_Std_Http_instInhabitedHeaders_default___closed__3(void){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_9_ = lean_obj_once(&l_Std_Http_instInhabitedHeaders_default___closed__2, &l_Std_Http_instInhabitedHeaders_default___closed__2_once, _init_l_Std_Http_instInhabitedHeaders_default___closed__2);
v___x_10_ = ((lean_object*)(l_Std_Http_instInhabitedHeaders_default___closed__0));
v___x_11_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_11_, 0, v___x_10_);
lean_ctor_set(v___x_11_, 1, v___x_9_);
return v___x_11_;
}
}
static lean_object* _init_l_Std_Http_instInhabitedHeaders_default(void){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lean_obj_once(&l_Std_Http_instInhabitedHeaders_default___closed__3, &l_Std_Http_instInhabitedHeaders_default___closed__3_once, _init_l_Std_Http_instInhabitedHeaders_default___closed__3);
return v___x_12_;
}
}
static lean_object* _init_l_Std_Http_instInhabitedHeaders(void){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = l_Std_Http_instInhabitedHeaders_default;
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Http_instReprHeaders_repr_spec__1(lean_object* v_a_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = lean_nat_to_int(v_a_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8_spec__13_spec__15_spec__17(lean_object* v_x_16_, lean_object* v_x_17_, lean_object* v_x_18_){
_start:
{
if (lean_obj_tag(v_x_18_) == 0)
{
lean_dec(v_x_16_);
return v_x_17_;
}
else
{
lean_object* v_head_19_; lean_object* v_tail_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_31_; 
v_head_19_ = lean_ctor_get(v_x_18_, 0);
v_tail_20_ = lean_ctor_get(v_x_18_, 1);
v_isSharedCheck_31_ = !lean_is_exclusive(v_x_18_);
if (v_isSharedCheck_31_ == 0)
{
v___x_22_ = v_x_18_;
v_isShared_23_ = v_isSharedCheck_31_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_tail_20_);
lean_inc(v_head_19_);
lean_dec(v_x_18_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_31_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
lean_object* v___x_25_; 
lean_inc(v_x_16_);
if (v_isShared_23_ == 0)
{
lean_ctor_set_tag(v___x_22_, 5);
lean_ctor_set(v___x_22_, 1, v_x_16_);
lean_ctor_set(v___x_22_, 0, v_x_17_);
v___x_25_ = v___x_22_;
goto v_reusejp_24_;
}
else
{
lean_object* v_reuseFailAlloc_30_; 
v_reuseFailAlloc_30_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_30_, 0, v_x_17_);
lean_ctor_set(v_reuseFailAlloc_30_, 1, v_x_16_);
v___x_25_ = v_reuseFailAlloc_30_;
goto v_reusejp_24_;
}
v_reusejp_24_:
{
lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_26_ = l_Nat_reprFast(v_head_19_);
v___x_27_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_27_, 0, v___x_26_);
v___x_28_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_28_, 0, v___x_25_);
lean_ctor_set(v___x_28_, 1, v___x_27_);
v_x_17_ = v___x_28_;
v_x_18_ = v_tail_20_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8_spec__13_spec__15(lean_object* v_x_32_, lean_object* v_x_33_, lean_object* v_x_34_){
_start:
{
if (lean_obj_tag(v_x_34_) == 0)
{
lean_dec(v_x_32_);
return v_x_33_;
}
else
{
lean_object* v_head_35_; lean_object* v_tail_36_; lean_object* v___x_38_; uint8_t v_isShared_39_; uint8_t v_isSharedCheck_47_; 
v_head_35_ = lean_ctor_get(v_x_34_, 0);
v_tail_36_ = lean_ctor_get(v_x_34_, 1);
v_isSharedCheck_47_ = !lean_is_exclusive(v_x_34_);
if (v_isSharedCheck_47_ == 0)
{
v___x_38_ = v_x_34_;
v_isShared_39_ = v_isSharedCheck_47_;
goto v_resetjp_37_;
}
else
{
lean_inc(v_tail_36_);
lean_inc(v_head_35_);
lean_dec(v_x_34_);
v___x_38_ = lean_box(0);
v_isShared_39_ = v_isSharedCheck_47_;
goto v_resetjp_37_;
}
v_resetjp_37_:
{
lean_object* v___x_41_; 
lean_inc(v_x_32_);
if (v_isShared_39_ == 0)
{
lean_ctor_set_tag(v___x_38_, 5);
lean_ctor_set(v___x_38_, 1, v_x_32_);
lean_ctor_set(v___x_38_, 0, v_x_33_);
v___x_41_ = v___x_38_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_46_; 
v_reuseFailAlloc_46_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_46_, 0, v_x_33_);
lean_ctor_set(v_reuseFailAlloc_46_, 1, v_x_32_);
v___x_41_ = v_reuseFailAlloc_46_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_42_ = l_Nat_reprFast(v_head_35_);
v___x_43_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_43_, 0, v___x_42_);
v___x_44_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_44_, 0, v___x_41_);
lean_ctor_set(v___x_44_, 1, v___x_43_);
v___x_45_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8_spec__13_spec__15_spec__17(v_x_32_, v___x_44_, v_tail_36_);
return v___x_45_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8_spec__13___lam__0(lean_object* v___y_48_){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_49_ = l_Nat_reprFast(v___y_48_);
v___x_50_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_50_, 0, v___x_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8_spec__13(lean_object* v_x_51_, lean_object* v_x_52_){
_start:
{
if (lean_obj_tag(v_x_51_) == 0)
{
lean_object* v___x_53_; 
lean_dec(v_x_52_);
v___x_53_ = lean_box(0);
return v___x_53_;
}
else
{
lean_object* v_tail_54_; 
v_tail_54_ = lean_ctor_get(v_x_51_, 1);
if (lean_obj_tag(v_tail_54_) == 0)
{
lean_object* v_head_55_; lean_object* v___x_56_; 
lean_dec(v_x_52_);
v_head_55_ = lean_ctor_get(v_x_51_, 0);
lean_inc(v_head_55_);
lean_dec_ref(v_x_51_);
v___x_56_ = l_Std_Format_joinSep___at___00Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8_spec__13___lam__0(v_head_55_);
return v___x_56_;
}
else
{
lean_object* v_head_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
lean_inc(v_tail_54_);
v_head_57_ = lean_ctor_get(v_x_51_, 0);
lean_inc(v_head_57_);
lean_dec_ref(v_x_51_);
v___x_58_ = l_Std_Format_joinSep___at___00Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8_spec__13___lam__0(v_head_57_);
v___x_59_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8_spec__13_spec__15(v_x_52_, v___x_58_, v_tail_54_);
return v___x_59_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__5(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_68_ = ((lean_object*)(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__0));
v___x_69_ = lean_string_length(v___x_68_);
return v___x_69_;
}
}
static lean_object* _init_l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__6(void){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_70_ = lean_obj_once(&l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__5, &l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__5_once, _init_l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__5);
v___x_71_ = lean_nat_to_int(v___x_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8(lean_object* v_xs_79_){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; uint8_t v___x_82_; 
v___x_80_ = lean_array_get_size(v_xs_79_);
v___x_81_ = lean_unsigned_to_nat(0u);
v___x_82_ = lean_nat_dec_eq(v___x_80_, v___x_81_);
if (v___x_82_ == 0)
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_83_ = lean_array_to_list(v_xs_79_);
v___x_84_ = ((lean_object*)(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__3));
v___x_85_ = l_Std_Format_joinSep___at___00Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8_spec__13(v___x_83_, v___x_84_);
v___x_86_ = lean_obj_once(&l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__6, &l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__6_once, _init_l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__6);
v___x_87_ = ((lean_object*)(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__7));
v___x_88_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_88_, 0, v___x_87_);
lean_ctor_set(v___x_88_, 1, v___x_85_);
v___x_89_ = ((lean_object*)(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__8));
v___x_90_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_90_, 0, v___x_88_);
lean_ctor_set(v___x_90_, 1, v___x_89_);
v___x_91_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_91_, 0, v___x_86_);
lean_ctor_set(v___x_91_, 1, v___x_90_);
v___x_92_ = l_Std_Format_fill(v___x_91_);
return v___x_92_;
}
else
{
lean_object* v___x_93_; 
lean_dec_ref(v_xs_79_);
v___x_93_ = ((lean_object*)(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__10));
return v___x_93_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2_spec__3_spec__7(lean_object* v_x_94_, lean_object* v_x_95_, lean_object* v_x_96_){
_start:
{
if (lean_obj_tag(v_x_96_) == 0)
{
lean_dec(v_x_94_);
return v_x_95_;
}
else
{
lean_object* v_head_97_; lean_object* v_tail_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_107_; 
v_head_97_ = lean_ctor_get(v_x_96_, 0);
v_tail_98_ = lean_ctor_get(v_x_96_, 1);
v_isSharedCheck_107_ = !lean_is_exclusive(v_x_96_);
if (v_isSharedCheck_107_ == 0)
{
v___x_100_ = v_x_96_;
v_isShared_101_ = v_isSharedCheck_107_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_tail_98_);
lean_inc(v_head_97_);
lean_dec(v_x_96_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_107_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v___x_103_; 
lean_inc(v_x_94_);
if (v_isShared_101_ == 0)
{
lean_ctor_set_tag(v___x_100_, 5);
lean_ctor_set(v___x_100_, 1, v_x_94_);
lean_ctor_set(v___x_100_, 0, v_x_95_);
v___x_103_ = v___x_100_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v_x_95_);
lean_ctor_set(v_reuseFailAlloc_106_, 1, v_x_94_);
v___x_103_ = v_reuseFailAlloc_106_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
lean_object* v___x_104_; 
v___x_104_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_104_, 0, v___x_103_);
lean_ctor_set(v___x_104_, 1, v_head_97_);
v_x_95_ = v___x_104_;
v_x_96_ = v_tail_98_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2_spec__3(lean_object* v_x_108_, lean_object* v_x_109_){
_start:
{
if (lean_obj_tag(v_x_108_) == 0)
{
lean_object* v___x_110_; 
lean_dec(v_x_109_);
v___x_110_ = lean_box(0);
return v___x_110_;
}
else
{
lean_object* v_tail_111_; 
v_tail_111_ = lean_ctor_get(v_x_108_, 1);
if (lean_obj_tag(v_tail_111_) == 0)
{
lean_object* v_head_112_; 
lean_dec(v_x_109_);
v_head_112_ = lean_ctor_get(v_x_108_, 0);
lean_inc(v_head_112_);
lean_dec_ref(v_x_108_);
return v_head_112_;
}
else
{
lean_object* v_head_113_; lean_object* v___x_114_; 
lean_inc(v_tail_111_);
v_head_113_ = lean_ctor_get(v_x_108_, 0);
lean_inc(v_head_113_);
lean_dec_ref(v_x_108_);
v___x_114_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2_spec__3_spec__7(v_x_109_, v_head_113_, v_tail_111_);
return v___x_114_;
}
}
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_117_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__0));
v___x_118_ = lean_string_length(v___x_117_);
return v___x_118_;
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_119_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__2, &l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__2_once, _init_l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__2);
v___x_120_ = lean_nat_to_int(v___x_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg(lean_object* v_x_125_){
_start:
{
lean_object* v_fst_126_; lean_object* v_snd_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_149_; 
v_fst_126_ = lean_ctor_get(v_x_125_, 0);
v_snd_127_ = lean_ctor_get(v_x_125_, 1);
v_isSharedCheck_149_ = !lean_is_exclusive(v_x_125_);
if (v_isSharedCheck_149_ == 0)
{
v___x_129_ = v_x_125_;
v_isShared_130_ = v_isSharedCheck_149_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_snd_127_);
lean_inc(v_fst_126_);
lean_dec(v_x_125_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_149_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_134_; 
v___x_131_ = l_Std_Http_Header_instReprName_repr___redArg(v_fst_126_);
v___x_132_ = lean_box(0);
if (v_isShared_130_ == 0)
{
lean_ctor_set_tag(v___x_129_, 1);
lean_ctor_set(v___x_129_, 1, v___x_132_);
lean_ctor_set(v___x_129_, 0, v___x_131_);
v___x_134_ = v___x_129_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v___x_131_);
lean_ctor_set(v_reuseFailAlloc_148_, 1, v___x_132_);
v___x_134_ = v_reuseFailAlloc_148_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; uint8_t v___x_146_; lean_object* v___x_147_; 
v___x_135_ = l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8(v_snd_127_);
v___x_136_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_136_, 0, v___x_135_);
lean_ctor_set(v___x_136_, 1, v___x_134_);
v___x_137_ = l_List_reverse___redArg(v___x_136_);
v___x_138_ = ((lean_object*)(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__3));
v___x_139_ = l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2_spec__3(v___x_137_, v___x_138_);
v___x_140_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__3, &l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__3_once, _init_l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__3);
v___x_141_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__4));
v___x_142_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_142_, 0, v___x_141_);
lean_ctor_set(v___x_142_, 1, v___x_139_);
v___x_143_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__5));
v___x_144_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_144_, 0, v___x_142_);
lean_ctor_set(v___x_144_, 1, v___x_143_);
v___x_145_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_145_, 0, v___x_140_);
lean_ctor_set(v___x_145_, 1, v___x_144_);
v___x_146_ = 0;
v___x_147_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_147_, 0, v___x_145_);
lean_ctor_set_uint8(v___x_147_, sizeof(void*)*1, v___x_146_);
return v___x_147_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__6_spec__10_spec__16(lean_object* v_x_150_, lean_object* v_x_151_, lean_object* v_x_152_){
_start:
{
if (lean_obj_tag(v_x_152_) == 0)
{
lean_dec(v_x_150_);
return v_x_151_;
}
else
{
lean_object* v_head_153_; lean_object* v_tail_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_164_; 
v_head_153_ = lean_ctor_get(v_x_152_, 0);
v_tail_154_ = lean_ctor_get(v_x_152_, 1);
v_isSharedCheck_164_ = !lean_is_exclusive(v_x_152_);
if (v_isSharedCheck_164_ == 0)
{
v___x_156_ = v_x_152_;
v_isShared_157_ = v_isSharedCheck_164_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_tail_154_);
lean_inc(v_head_153_);
lean_dec(v_x_152_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_164_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_159_; 
lean_inc(v_x_150_);
if (v_isShared_157_ == 0)
{
lean_ctor_set_tag(v___x_156_, 5);
lean_ctor_set(v___x_156_, 1, v_x_150_);
lean_ctor_set(v___x_156_, 0, v_x_151_);
v___x_159_ = v___x_156_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_x_151_);
lean_ctor_set(v_reuseFailAlloc_163_, 1, v_x_150_);
v___x_159_ = v_reuseFailAlloc_163_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_160_ = l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg(v_head_153_);
v___x_161_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_161_, 0, v___x_159_);
lean_ctor_set(v___x_161_, 1, v___x_160_);
v_x_151_ = v___x_161_;
v_x_152_ = v_tail_154_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__6_spec__10(lean_object* v_x_165_, lean_object* v_x_166_, lean_object* v_x_167_){
_start:
{
if (lean_obj_tag(v_x_167_) == 0)
{
lean_dec(v_x_165_);
return v_x_166_;
}
else
{
lean_object* v_head_168_; lean_object* v_tail_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_179_; 
v_head_168_ = lean_ctor_get(v_x_167_, 0);
v_tail_169_ = lean_ctor_get(v_x_167_, 1);
v_isSharedCheck_179_ = !lean_is_exclusive(v_x_167_);
if (v_isSharedCheck_179_ == 0)
{
v___x_171_ = v_x_167_;
v_isShared_172_ = v_isSharedCheck_179_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_tail_169_);
lean_inc(v_head_168_);
lean_dec(v_x_167_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_179_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v___x_174_; 
lean_inc(v_x_165_);
if (v_isShared_172_ == 0)
{
lean_ctor_set_tag(v___x_171_, 5);
lean_ctor_set(v___x_171_, 1, v_x_165_);
lean_ctor_set(v___x_171_, 0, v_x_166_);
v___x_174_ = v___x_171_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v_x_166_);
lean_ctor_set(v_reuseFailAlloc_178_, 1, v_x_165_);
v___x_174_ = v_reuseFailAlloc_178_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_175_ = l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg(v_head_168_);
v___x_176_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_176_, 0, v___x_174_);
lean_ctor_set(v___x_176_, 1, v___x_175_);
v___x_177_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__6_spec__10_spec__16(v_x_165_, v___x_176_, v_tail_169_);
return v___x_177_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__6(lean_object* v_x_180_, lean_object* v_x_181_){
_start:
{
if (lean_obj_tag(v_x_180_) == 0)
{
lean_object* v___x_182_; 
lean_dec(v_x_181_);
v___x_182_ = lean_box(0);
return v___x_182_;
}
else
{
lean_object* v_tail_183_; 
v_tail_183_ = lean_ctor_get(v_x_180_, 1);
if (lean_obj_tag(v_tail_183_) == 0)
{
lean_object* v_head_184_; lean_object* v___x_185_; 
lean_dec(v_x_181_);
v_head_184_ = lean_ctor_get(v_x_180_, 0);
lean_inc(v_head_184_);
lean_dec_ref(v_x_180_);
v___x_185_ = l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg(v_head_184_);
return v___x_185_;
}
else
{
lean_object* v_head_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
lean_inc(v_tail_183_);
v_head_186_ = lean_ctor_get(v_x_180_, 0);
lean_inc(v_head_186_);
lean_dec_ref(v_x_180_);
v___x_187_ = l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg(v_head_186_);
v___x_188_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__6_spec__10(v_x_181_, v___x_187_, v_tail_183_);
return v___x_188_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = ((lean_object*)(l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__2));
v___x_194_ = lean_string_length(v___x_193_);
return v___x_194_;
}
}
static lean_object* _init_l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_195_ = lean_obj_once(&l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__3, &l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__3_once, _init_l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__3);
v___x_196_ = lean_nat_to_int(v___x_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg(lean_object* v_a_199_){
_start:
{
if (lean_obj_tag(v_a_199_) == 0)
{
lean_object* v___x_200_; 
v___x_200_ = ((lean_object*)(l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__1));
return v___x_200_;
}
else
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; uint8_t v___x_209_; lean_object* v___x_210_; 
v___x_201_ = ((lean_object*)(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__3));
v___x_202_ = l_Std_Format_joinSep___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__6(v_a_199_, v___x_201_);
v___x_203_ = lean_obj_once(&l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__4, &l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__4_once, _init_l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__4);
v___x_204_ = ((lean_object*)(l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__5));
v___x_205_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
lean_ctor_set(v___x_205_, 1, v___x_202_);
v___x_206_ = ((lean_object*)(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__8));
v___x_207_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_207_, 0, v___x_205_);
lean_ctor_set(v___x_207_, 1, v___x_206_);
v___x_208_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_208_, 0, v___x_203_);
lean_ctor_set(v___x_208_, 1, v___x_207_);
v___x_209_ = 0;
v___x_210_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_210_, 0, v___x_208_);
lean_ctor_set_uint8(v___x_210_, sizeof(void*)*1, v___x_209_);
return v___x_210_;
}
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg(lean_object* v_x_211_){
_start:
{
lean_object* v_fst_212_; lean_object* v_snd_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_235_; 
v_fst_212_ = lean_ctor_get(v_x_211_, 0);
v_snd_213_ = lean_ctor_get(v_x_211_, 1);
v_isSharedCheck_235_ = !lean_is_exclusive(v_x_211_);
if (v_isSharedCheck_235_ == 0)
{
v___x_215_ = v_x_211_;
v_isShared_216_ = v_isSharedCheck_235_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_snd_213_);
lean_inc(v_fst_212_);
lean_dec(v_x_211_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_235_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_220_; 
v___x_217_ = l_Std_Http_Header_instReprName_repr___redArg(v_fst_212_);
v___x_218_ = lean_box(0);
if (v_isShared_216_ == 0)
{
lean_ctor_set_tag(v___x_215_, 1);
lean_ctor_set(v___x_215_, 1, v___x_218_);
lean_ctor_set(v___x_215_, 0, v___x_217_);
v___x_220_ = v___x_215_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v___x_217_);
lean_ctor_set(v_reuseFailAlloc_234_, 1, v___x_218_);
v___x_220_ = v_reuseFailAlloc_234_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; uint8_t v___x_232_; lean_object* v___x_233_; 
v___x_221_ = l_Std_Http_Header_instReprValue_repr___redArg(v_snd_213_);
v___x_222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
lean_ctor_set(v___x_222_, 1, v___x_220_);
v___x_223_ = l_List_reverse___redArg(v___x_222_);
v___x_224_ = ((lean_object*)(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__3));
v___x_225_ = l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2_spec__3(v___x_223_, v___x_224_);
v___x_226_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__3, &l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__3_once, _init_l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__3);
v___x_227_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__4));
v___x_228_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_228_, 0, v___x_227_);
lean_ctor_set(v___x_228_, 1, v___x_225_);
v___x_229_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__5));
v___x_230_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_230_, 0, v___x_228_);
lean_ctor_set(v___x_230_, 1, v___x_229_);
v___x_231_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_231_, 0, v___x_226_);
lean_ctor_set(v___x_231_, 1, v___x_230_);
v___x_232_ = 0;
v___x_233_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_233_, 0, v___x_231_);
lean_ctor_set_uint8(v___x_233_, sizeof(void*)*1, v___x_232_);
return v___x_233_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__3_spec__5_spec__10(lean_object* v_x_236_, lean_object* v_x_237_, lean_object* v_x_238_){
_start:
{
if (lean_obj_tag(v_x_238_) == 0)
{
lean_dec(v_x_236_);
return v_x_237_;
}
else
{
lean_object* v_head_239_; lean_object* v_tail_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_250_; 
v_head_239_ = lean_ctor_get(v_x_238_, 0);
v_tail_240_ = lean_ctor_get(v_x_238_, 1);
v_isSharedCheck_250_ = !lean_is_exclusive(v_x_238_);
if (v_isSharedCheck_250_ == 0)
{
v___x_242_ = v_x_238_;
v_isShared_243_ = v_isSharedCheck_250_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_tail_240_);
lean_inc(v_head_239_);
lean_dec(v_x_238_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_250_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_245_; 
lean_inc(v_x_236_);
if (v_isShared_243_ == 0)
{
lean_ctor_set_tag(v___x_242_, 5);
lean_ctor_set(v___x_242_, 1, v_x_236_);
lean_ctor_set(v___x_242_, 0, v_x_237_);
v___x_245_ = v___x_242_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v_x_237_);
lean_ctor_set(v_reuseFailAlloc_249_, 1, v_x_236_);
v___x_245_ = v_reuseFailAlloc_249_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_246_ = l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg(v_head_239_);
v___x_247_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_245_);
lean_ctor_set(v___x_247_, 1, v___x_246_);
v_x_237_ = v___x_247_;
v_x_238_ = v_tail_240_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__3_spec__5(lean_object* v_x_251_, lean_object* v_x_252_, lean_object* v_x_253_){
_start:
{
if (lean_obj_tag(v_x_253_) == 0)
{
lean_dec(v_x_251_);
return v_x_252_;
}
else
{
lean_object* v_head_254_; lean_object* v_tail_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_265_; 
v_head_254_ = lean_ctor_get(v_x_253_, 0);
v_tail_255_ = lean_ctor_get(v_x_253_, 1);
v_isSharedCheck_265_ = !lean_is_exclusive(v_x_253_);
if (v_isSharedCheck_265_ == 0)
{
v___x_257_ = v_x_253_;
v_isShared_258_ = v_isSharedCheck_265_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_tail_255_);
lean_inc(v_head_254_);
lean_dec(v_x_253_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_265_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_260_; 
lean_inc(v_x_251_);
if (v_isShared_258_ == 0)
{
lean_ctor_set_tag(v___x_257_, 5);
lean_ctor_set(v___x_257_, 1, v_x_251_);
lean_ctor_set(v___x_257_, 0, v_x_252_);
v___x_260_ = v___x_257_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v_x_252_);
lean_ctor_set(v_reuseFailAlloc_264_, 1, v_x_251_);
v___x_260_ = v_reuseFailAlloc_264_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_261_ = l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg(v_head_254_);
v___x_262_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_262_, 0, v___x_260_);
lean_ctor_set(v___x_262_, 1, v___x_261_);
v___x_263_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__3_spec__5_spec__10(v_x_251_, v___x_262_, v_tail_255_);
return v___x_263_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__3(lean_object* v_x_266_, lean_object* v_x_267_){
_start:
{
if (lean_obj_tag(v_x_266_) == 0)
{
lean_object* v___x_268_; 
lean_dec(v_x_267_);
v___x_268_ = lean_box(0);
return v___x_268_;
}
else
{
lean_object* v_tail_269_; 
v_tail_269_ = lean_ctor_get(v_x_266_, 1);
if (lean_obj_tag(v_tail_269_) == 0)
{
lean_object* v_head_270_; lean_object* v___x_271_; 
lean_dec(v_x_267_);
v_head_270_ = lean_ctor_get(v_x_266_, 0);
lean_inc(v_head_270_);
lean_dec_ref(v_x_266_);
v___x_271_ = l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg(v_head_270_);
return v___x_271_;
}
else
{
lean_object* v_head_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
lean_inc(v_tail_269_);
v_head_272_ = lean_ctor_get(v_x_266_, 0);
lean_inc(v_head_272_);
lean_dec_ref(v_x_266_);
v___x_273_ = l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg(v_head_272_);
v___x_274_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__3_spec__5(v_x_267_, v___x_273_, v_tail_269_);
return v___x_274_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0(lean_object* v_xs_275_){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; uint8_t v___x_278_; 
v___x_276_ = lean_array_get_size(v_xs_275_);
v___x_277_ = lean_unsigned_to_nat(0u);
v___x_278_ = lean_nat_dec_eq(v___x_276_, v___x_277_);
if (v___x_278_ == 0)
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_279_ = lean_array_to_list(v_xs_275_);
v___x_280_ = ((lean_object*)(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__3));
v___x_281_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__3(v___x_279_, v___x_280_);
v___x_282_ = lean_obj_once(&l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__6, &l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__6_once, _init_l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__6);
v___x_283_ = ((lean_object*)(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__7));
v___x_284_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
lean_ctor_set(v___x_284_, 1, v___x_281_);
v___x_285_ = ((lean_object*)(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__8));
v___x_286_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_284_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
v___x_287_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_282_);
lean_ctor_set(v___x_287_, 1, v___x_286_);
v___x_288_ = l_Std_Format_fill(v___x_287_);
return v___x_288_;
}
else
{
lean_object* v___x_289_; 
lean_dec_ref(v_xs_275_);
v___x_289_ = ((lean_object*)(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__10));
return v___x_289_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2(lean_object* v_x_290_, lean_object* v_x_291_){
_start:
{
if (lean_obj_tag(v_x_291_) == 0)
{
lean_inc(v_x_290_);
return v_x_290_;
}
else
{
lean_object* v_key_292_; lean_object* v_value_293_; lean_object* v_tail_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v_key_292_ = lean_ctor_get(v_x_291_, 0);
v_value_293_ = lean_ctor_get(v_x_291_, 1);
v_tail_294_ = lean_ctor_get(v_x_291_, 2);
v___x_295_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2(v_x_290_, v_tail_294_);
lean_inc(v_value_293_);
lean_inc(v_key_292_);
v___x_296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_296_, 0, v_key_292_);
lean_ctor_set(v___x_296_, 1, v_value_293_);
v___x_297_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
lean_ctor_set(v___x_297_, 1, v___x_295_);
return v___x_297_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2___boxed(lean_object* v_x_298_, lean_object* v_x_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2(v_x_298_, v_x_299_);
lean_dec(v_x_299_);
lean_dec(v_x_298_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__3(lean_object* v_as_301_, size_t v_i_302_, size_t v_stop_303_, lean_object* v_b_304_){
_start:
{
uint8_t v___x_305_; 
v___x_305_ = lean_usize_dec_eq(v_i_302_, v_stop_303_);
if (v___x_305_ == 0)
{
size_t v___x_306_; size_t v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_306_ = ((size_t)1ULL);
v___x_307_ = lean_usize_sub(v_i_302_, v___x_306_);
v___x_308_ = lean_array_uget_borrowed(v_as_301_, v___x_307_);
v___x_309_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2(v_b_304_, v___x_308_);
lean_dec(v_b_304_);
v_i_302_ = v___x_307_;
v_b_304_ = v___x_309_;
goto _start;
}
else
{
return v_b_304_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__3___boxed(lean_object* v_as_311_, lean_object* v_i_312_, lean_object* v_stop_313_, lean_object* v_b_314_){
_start:
{
size_t v_i_boxed_315_; size_t v_stop_boxed_316_; lean_object* v_res_317_; 
v_i_boxed_315_ = lean_unbox_usize(v_i_312_);
lean_dec(v_i_312_);
v_stop_boxed_316_ = lean_unbox_usize(v_stop_313_);
lean_dec(v_stop_313_);
v_res_317_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__3(v_as_311_, v_i_boxed_315_, v_stop_boxed_316_, v_b_314_);
lean_dec_ref(v_as_311_);
return v_res_317_;
}
}
static lean_object* _init_l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_331_ = lean_unsigned_to_nat(11u);
v___x_332_ = lean_nat_to_int(v___x_331_);
return v___x_332_;
}
}
static lean_object* _init_l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__17(void){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__6));
v___x_347_ = lean_string_length(v___x_346_);
return v___x_347_;
}
}
static lean_object* _init_l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__18(void){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = lean_obj_once(&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__17, &l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__17_once, _init_l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__17);
v___x_349_ = lean_nat_to_int(v___x_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg(lean_object* v_x_354_){
_start:
{
lean_object* v_indexes_355_; lean_object* v_entries_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_415_; 
v_indexes_355_ = lean_ctor_get(v_x_354_, 1);
v_entries_356_ = lean_ctor_get(v_x_354_, 0);
v_isSharedCheck_415_ = !lean_is_exclusive(v_x_354_);
if (v_isSharedCheck_415_ == 0)
{
v___x_358_ = v_x_354_;
v_isShared_359_ = v_isSharedCheck_415_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_indexes_355_);
lean_inc(v_entries_356_);
lean_dec(v_x_354_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_415_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v_buckets_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_413_; 
v_buckets_360_ = lean_ctor_get(v_indexes_355_, 1);
v_isSharedCheck_413_ = !lean_is_exclusive(v_indexes_355_);
if (v_isSharedCheck_413_ == 0)
{
lean_object* v_unused_414_; 
v_unused_414_ = lean_ctor_get(v_indexes_355_, 0);
lean_dec(v_unused_414_);
v___x_362_ = v_indexes_355_;
v_isShared_363_ = v_isSharedCheck_413_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_buckets_360_);
lean_dec(v_indexes_355_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_413_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_369_; 
v___x_364_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__4));
v___x_365_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__5));
v___x_366_ = lean_obj_once(&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__7, &l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__7_once, _init_l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__7);
v___x_367_ = l_Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0(v_entries_356_);
if (v_isShared_363_ == 0)
{
lean_ctor_set_tag(v___x_362_, 4);
lean_ctor_set(v___x_362_, 1, v___x_367_);
lean_ctor_set(v___x_362_, 0, v___x_366_);
v___x_369_ = v___x_362_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_366_);
lean_ctor_set(v_reuseFailAlloc_412_, 1, v___x_367_);
v___x_369_ = v_reuseFailAlloc_412_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
uint8_t v___x_370_; lean_object* v___x_371_; lean_object* v___x_373_; 
v___x_370_ = 0;
v___x_371_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_371_, 0, v___x_369_);
lean_ctor_set_uint8(v___x_371_, sizeof(void*)*1, v___x_370_);
if (v_isShared_359_ == 0)
{
lean_ctor_set_tag(v___x_358_, 5);
lean_ctor_set(v___x_358_, 1, v___x_371_);
lean_ctor_set(v___x_358_, 0, v___x_365_);
v___x_373_ = v___x_358_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v___x_365_);
lean_ctor_set(v_reuseFailAlloc_411_, 1, v___x_371_);
v___x_373_ = v_reuseFailAlloc_411_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___y_384_; lean_object* v___x_405_; lean_object* v___x_406_; uint8_t v___x_407_; 
v___x_374_ = ((lean_object*)(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__2));
v___x_375_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_375_, 0, v___x_373_);
lean_ctor_set(v___x_375_, 1, v___x_374_);
v___x_376_ = lean_box(1);
v___x_377_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_377_, 0, v___x_375_);
lean_ctor_set(v___x_377_, 1, v___x_376_);
v___x_378_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__9));
v___x_379_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_379_, 0, v___x_377_);
lean_ctor_set(v___x_379_, 1, v___x_378_);
v___x_380_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
lean_ctor_set(v___x_380_, 1, v___x_364_);
v___x_381_ = lean_unsigned_to_nat(0u);
v___x_382_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__11));
v___x_405_ = lean_box(0);
v___x_406_ = lean_array_get_size(v_buckets_360_);
v___x_407_ = lean_nat_dec_lt(v___x_381_, v___x_406_);
if (v___x_407_ == 0)
{
lean_dec_ref(v_buckets_360_);
v___y_384_ = v___x_405_;
goto v___jp_383_;
}
else
{
size_t v___x_408_; size_t v___x_409_; lean_object* v___x_410_; 
v___x_408_ = lean_usize_of_nat(v___x_406_);
v___x_409_ = ((size_t)0ULL);
v___x_410_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__3(v_buckets_360_, v___x_408_, v___x_409_, v___x_405_);
lean_dec_ref(v_buckets_360_);
v___y_384_ = v___x_410_;
goto v___jp_383_;
}
v___jp_383_:
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_385_ = l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg(v___y_384_);
v___x_386_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_386_, 0, v___x_382_);
lean_ctor_set(v___x_386_, 1, v___x_385_);
v___x_387_ = l_Repr_addAppParen(v___x_386_, v___x_381_);
v___x_388_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_388_, 0, v___x_366_);
lean_ctor_set(v___x_388_, 1, v___x_387_);
v___x_389_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_389_, 0, v___x_388_);
lean_ctor_set_uint8(v___x_389_, sizeof(void*)*1, v___x_370_);
v___x_390_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_390_, 0, v___x_380_);
lean_ctor_set(v___x_390_, 1, v___x_389_);
v___x_391_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
lean_ctor_set(v___x_391_, 1, v___x_374_);
v___x_392_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
lean_ctor_set(v___x_392_, 1, v___x_376_);
v___x_393_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__13));
v___x_394_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_394_, 0, v___x_392_);
lean_ctor_set(v___x_394_, 1, v___x_393_);
v___x_395_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_395_, 0, v___x_394_);
lean_ctor_set(v___x_395_, 1, v___x_364_);
v___x_396_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__15));
v___x_397_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_397_, 0, v___x_395_);
lean_ctor_set(v___x_397_, 1, v___x_396_);
v___x_398_ = lean_obj_once(&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__18, &l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__18_once, _init_l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__18);
v___x_399_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__19));
v___x_400_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_400_, 0, v___x_399_);
lean_ctor_set(v___x_400_, 1, v___x_397_);
v___x_401_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__20));
v___x_402_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_402_, 0, v___x_400_);
lean_ctor_set(v___x_402_, 1, v___x_401_);
v___x_403_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_403_, 0, v___x_398_);
lean_ctor_set(v___x_403_, 1, v___x_402_);
v___x_404_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_404_, 0, v___x_403_);
lean_ctor_set_uint8(v___x_404_, sizeof(void*)*1, v___x_370_);
return v___x_404_;
}
}
}
}
}
}
}
static lean_object* _init_l_Std_Http_instReprHeaders_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_425_ = lean_unsigned_to_nat(7u);
v___x_426_ = lean_nat_to_int(v___x_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprHeaders_repr___redArg(lean_object* v_x_427_){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; uint8_t v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_428_ = ((lean_object*)(l_Std_Http_instReprHeaders_repr___redArg___closed__3));
v___x_429_ = lean_obj_once(&l_Std_Http_instReprHeaders_repr___redArg___closed__4, &l_Std_Http_instReprHeaders_repr___redArg___closed__4_once, _init_l_Std_Http_instReprHeaders_repr___redArg___closed__4);
v___x_430_ = l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg(v_x_427_);
v___x_431_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_431_, 0, v___x_429_);
lean_ctor_set(v___x_431_, 1, v___x_430_);
v___x_432_ = 0;
v___x_433_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_433_, 0, v___x_431_);
lean_ctor_set_uint8(v___x_433_, sizeof(void*)*1, v___x_432_);
v___x_434_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_434_, 0, v___x_428_);
lean_ctor_set(v___x_434_, 1, v___x_433_);
v___x_435_ = lean_obj_once(&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__18, &l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__18_once, _init_l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__18);
v___x_436_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__19));
v___x_437_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_437_, 0, v___x_436_);
lean_ctor_set(v___x_437_, 1, v___x_434_);
v___x_438_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__20));
v___x_439_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_439_, 0, v___x_437_);
lean_ctor_set(v___x_439_, 1, v___x_438_);
v___x_440_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_440_, 0, v___x_435_);
lean_ctor_set(v___x_440_, 1, v___x_439_);
v___x_441_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_441_, 0, v___x_440_);
lean_ctor_set_uint8(v___x_441_, sizeof(void*)*1, v___x_432_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprHeaders_repr(lean_object* v_x_442_, lean_object* v_prec_443_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_Std_Http_instReprHeaders_repr___redArg(v_x_442_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprHeaders_repr___boxed(lean_object* v_x_445_, lean_object* v_prec_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Std_Http_instReprHeaders_repr(v_x_445_, v_prec_446_);
lean_dec(v_prec_446_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0(lean_object* v_x_448_, lean_object* v_prec_449_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg(v_x_448_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___boxed(lean_object* v_x_451_, lean_object* v_prec_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0(v_x_451_, v_prec_452_);
lean_dec(v_prec_452_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1(lean_object* v_a_454_, lean_object* v_n_455_){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg(v_a_454_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___boxed(lean_object* v_a_457_, lean_object* v_n_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1(v_a_457_, v_n_458_);
lean_dec(v_n_458_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2(lean_object* v_x_460_, lean_object* v_x_461_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg(v_x_460_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___boxed(lean_object* v_x_463_, lean_object* v_x_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2(v_x_463_, v_x_464_);
lean_dec(v_x_464_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5(lean_object* v_x_466_, lean_object* v_x_467_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg(v_x_466_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___boxed(lean_object* v_x_469_, lean_object* v_x_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5(v_x_469_, v_x_470_);
lean_dec(v_x_470_);
return v_res_471_;
}
}
static lean_object* _init_l_Std_Http_instMembershipNameHeaders(void){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = lean_box(0);
return v___x_474_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_instDecidableMemNameHeaders(lean_object* v_name_477_, lean_object* v_h_478_){
_start:
{
lean_object* v___f_479_; lean_object* v___f_480_; uint8_t v___x_481_; 
v___f_479_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_480_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v___x_481_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_479_, v___f_480_, v_name_477_, v_h_478_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instDecidableMemNameHeaders___boxed(lean_object* v_name_482_, lean_object* v_h_483_){
_start:
{
uint8_t v_res_484_; lean_object* v_r_485_; 
v_res_484_ = l_Std_Http_instDecidableMemNameHeaders(v_name_482_, v_h_483_);
lean_dec_ref(v_h_483_);
v_r_485_ = lean_box(v_res_484_);
return v_r_485_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_get___redArg(lean_object* v_headers_486_, lean_object* v_name_487_){
_start:
{
lean_object* v_entries_488_; lean_object* v_indexes_489_; lean_object* v___f_490_; lean_object* v___f_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v_entry_494_; lean_object* v___x_495_; lean_object* v_snd_496_; 
v_entries_488_ = lean_ctor_get(v_headers_486_, 0);
v_indexes_489_ = lean_ctor_get(v_headers_486_, 1);
v___f_490_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_491_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v___x_492_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v___f_490_, v___f_491_, v_indexes_489_, v_name_487_);
v___x_493_ = lean_unsigned_to_nat(0u);
v_entry_494_ = lean_array_fget(v___x_492_, v___x_493_);
lean_dec(v___x_492_);
v___x_495_ = lean_array_fget_borrowed(v_entries_488_, v_entry_494_);
lean_dec(v_entry_494_);
v_snd_496_ = lean_ctor_get(v___x_495_, 1);
lean_inc(v_snd_496_);
return v_snd_496_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_get___redArg___boxed(lean_object* v_headers_497_, lean_object* v_name_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l_Std_Http_Headers_get___redArg(v_headers_497_, v_name_498_);
lean_dec_ref(v_headers_497_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_get(lean_object* v_headers_500_, lean_object* v_name_501_, lean_object* v_h_502_){
_start:
{
lean_object* v_entries_503_; lean_object* v_indexes_504_; lean_object* v___f_505_; lean_object* v___f_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v_entry_509_; lean_object* v___x_510_; lean_object* v_snd_511_; 
v_entries_503_ = lean_ctor_get(v_headers_500_, 0);
v_indexes_504_ = lean_ctor_get(v_headers_500_, 1);
v___f_505_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_506_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v___x_507_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v___f_505_, v___f_506_, v_indexes_504_, v_name_501_);
v___x_508_ = lean_unsigned_to_nat(0u);
v_entry_509_ = lean_array_fget(v___x_507_, v___x_508_);
lean_dec(v___x_507_);
v___x_510_ = lean_array_fget_borrowed(v_entries_503_, v_entry_509_);
lean_dec(v_entry_509_);
v_snd_511_ = lean_ctor_get(v___x_510_, 1);
lean_inc(v_snd_511_);
return v_snd_511_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_get___boxed(lean_object* v_headers_512_, lean_object* v_name_513_, lean_object* v_h_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l_Std_Http_Headers_get(v_headers_512_, v_name_513_, v_h_514_);
lean_dec_ref(v_headers_512_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_getAll___redArg___lam__0(lean_object* v___x_516_, lean_object* v_entries_517_, lean_object* v_x1_518_, lean_object* v_x2_519_, lean_object* v_x3_520_){
_start:
{
lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v_snd_523_; 
v___x_521_ = lean_array_fget_borrowed(v___x_516_, v_x1_518_);
v___x_522_ = lean_array_fget_borrowed(v_entries_517_, v___x_521_);
v_snd_523_ = lean_ctor_get(v___x_522_, 1);
lean_inc(v_snd_523_);
return v_snd_523_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_getAll___redArg___lam__0___boxed(lean_object* v___x_524_, lean_object* v_entries_525_, lean_object* v_x1_526_, lean_object* v_x2_527_, lean_object* v_x3_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Std_Http_Headers_getAll___redArg___lam__0(v___x_524_, v_entries_525_, v_x1_526_, v_x2_527_, v_x3_528_);
lean_dec(v_x2_527_);
lean_dec(v_x1_526_);
lean_dec_ref(v_entries_525_);
lean_dec_ref(v___x_524_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_getAll___redArg(lean_object* v_headers_549_, lean_object* v_name_550_){
_start:
{
lean_object* v_entries_551_; lean_object* v_indexes_552_; lean_object* v___f_553_; lean_object* v___f_554_; lean_object* v___x_555_; lean_object* v___f_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v_entries_561_; 
v_entries_551_ = lean_ctor_get(v_headers_549_, 0);
lean_inc_ref(v_entries_551_);
v_indexes_552_ = lean_ctor_get(v_headers_549_, 1);
lean_inc_ref(v_indexes_552_);
lean_dec_ref(v_headers_549_);
v___f_553_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_554_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v___x_555_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v___f_553_, v___f_554_, v_indexes_552_, v_name_550_);
lean_dec_ref(v_indexes_552_);
lean_inc(v___x_555_);
v___f_556_ = lean_alloc_closure((void*)(l_Std_Http_Headers_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_556_, 0, v___x_555_);
lean_closure_set(v___f_556_, 1, v_entries_551_);
v___x_557_ = ((lean_object*)(l_Std_Http_Headers_getAll___redArg___closed__9));
v___x_558_ = lean_array_get_size(v___x_555_);
v___x_559_ = lean_unsigned_to_nat(0u);
v___x_560_ = lean_mk_empty_array_with_capacity(v___x_558_);
v_entries_561_ = l_Array_mapFinIdxM_map___redArg(v___x_557_, v___x_555_, v___f_556_, v___x_558_, v___x_559_, v___x_560_);
return v_entries_561_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_getAll(lean_object* v_headers_562_, lean_object* v_name_563_, lean_object* v_h_564_){
_start:
{
lean_object* v_entries_565_; lean_object* v_indexes_566_; lean_object* v___f_567_; lean_object* v___f_568_; lean_object* v___x_569_; lean_object* v___f_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v_entries_575_; 
v_entries_565_ = lean_ctor_get(v_headers_562_, 0);
lean_inc_ref(v_entries_565_);
v_indexes_566_ = lean_ctor_get(v_headers_562_, 1);
lean_inc_ref(v_indexes_566_);
lean_dec_ref(v_headers_562_);
v___f_567_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_568_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v___x_569_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v___f_567_, v___f_568_, v_indexes_566_, v_name_563_);
lean_dec_ref(v_indexes_566_);
lean_inc(v___x_569_);
v___f_570_ = lean_alloc_closure((void*)(l_Std_Http_Headers_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_570_, 0, v___x_569_);
lean_closure_set(v___f_570_, 1, v_entries_565_);
v___x_571_ = ((lean_object*)(l_Std_Http_Headers_getAll___redArg___closed__9));
v___x_572_ = lean_array_get_size(v___x_569_);
v___x_573_ = lean_unsigned_to_nat(0u);
v___x_574_ = lean_mk_empty_array_with_capacity(v___x_572_);
v_entries_575_ = l_Array_mapFinIdxM_map___redArg(v___x_571_, v___x_569_, v___f_570_, v___x_572_, v___x_573_, v___x_574_);
return v_entries_575_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_getAll_x3f(lean_object* v_headers_576_, lean_object* v_name_577_){
_start:
{
lean_object* v___f_578_; lean_object* v___f_579_; uint8_t v___x_580_; 
v___f_578_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_579_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
lean_inc_ref(v_name_577_);
v___x_580_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_578_, v___f_579_, v_name_577_, v_headers_576_);
if (v___x_580_ == 0)
{
lean_object* v___x_581_; 
lean_dec_ref(v_name_577_);
lean_dec_ref(v_headers_576_);
v___x_581_ = lean_box(0);
return v___x_581_;
}
else
{
lean_object* v_entries_582_; lean_object* v_indexes_583_; lean_object* v___x_584_; lean_object* v___f_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v_entries_590_; lean_object* v___x_591_; 
v_entries_582_ = lean_ctor_get(v_headers_576_, 0);
lean_inc_ref(v_entries_582_);
v_indexes_583_ = lean_ctor_get(v_headers_576_, 1);
lean_inc_ref(v_indexes_583_);
lean_dec_ref(v_headers_576_);
v___x_584_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v___f_578_, v___f_579_, v_indexes_583_, v_name_577_);
lean_dec_ref(v_indexes_583_);
lean_inc(v___x_584_);
v___f_585_ = lean_alloc_closure((void*)(l_Std_Http_Headers_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_585_, 0, v___x_584_);
lean_closure_set(v___f_585_, 1, v_entries_582_);
v___x_586_ = ((lean_object*)(l_Std_Http_Headers_getAll___redArg___closed__9));
v___x_587_ = lean_array_get_size(v___x_584_);
v___x_588_ = lean_unsigned_to_nat(0u);
v___x_589_ = lean_mk_empty_array_with_capacity(v___x_587_);
v_entries_590_ = l_Array_mapFinIdxM_map___redArg(v___x_586_, v___x_584_, v___f_585_, v___x_587_, v___x_588_, v___x_589_);
v___x_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_591_, 0, v_entries_590_);
return v___x_591_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_get_x3f(lean_object* v_headers_592_, lean_object* v_name_593_){
_start:
{
lean_object* v___f_594_; lean_object* v___f_595_; uint8_t v___x_596_; 
v___f_594_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_595_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
lean_inc_ref(v_name_593_);
v___x_596_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_594_, v___f_595_, v_name_593_, v_headers_592_);
if (v___x_596_ == 0)
{
lean_object* v___x_597_; 
lean_dec_ref(v_name_593_);
v___x_597_ = lean_box(0);
return v___x_597_;
}
else
{
lean_object* v_entries_598_; lean_object* v_indexes_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v_entry_602_; lean_object* v___x_603_; lean_object* v_snd_604_; lean_object* v___x_605_; 
v_entries_598_ = lean_ctor_get(v_headers_592_, 0);
v_indexes_599_ = lean_ctor_get(v_headers_592_, 1);
v___x_600_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v___f_594_, v___f_595_, v_indexes_599_, v_name_593_);
v___x_601_ = lean_unsigned_to_nat(0u);
v_entry_602_ = lean_array_fget(v___x_600_, v___x_601_);
lean_dec(v___x_600_);
v___x_603_ = lean_array_fget_borrowed(v_entries_598_, v_entry_602_);
lean_dec(v_entry_602_);
v_snd_604_ = lean_ctor_get(v___x_603_, 1);
lean_inc(v_snd_604_);
v___x_605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_605_, 0, v_snd_604_);
return v___x_605_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_get_x3f___boxed(lean_object* v_headers_606_, lean_object* v_name_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_Std_Http_Headers_get_x3f(v_headers_606_, v_name_607_);
lean_dec_ref(v_headers_606_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_hasEntry___lam__1(lean_object* v_value_609_, lean_object* v___x_610_, lean_object* v___x_611_, lean_object* v_a_612_, lean_object* v_x_613_, lean_object* v___y_614_){
_start:
{
uint8_t v___x_615_; 
v___x_615_ = l_Std_Http_Header_instBEqValue_beq(v_a_612_, v_value_609_);
if (v___x_615_ == 0)
{
lean_object* v___x_616_; 
lean_dec_ref(v_a_612_);
v___x_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_616_, 0, v___x_610_);
return v___x_616_;
}
else
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
lean_dec_ref(v___x_610_);
v___x_617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_617_, 0, v_a_612_);
v___x_618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_618_, 0, v___x_617_);
v___x_619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_619_, 0, v___x_618_);
lean_ctor_set(v___x_619_, 1, v___x_611_);
v___x_620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_620_, 0, v___x_619_);
return v___x_620_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_hasEntry___lam__1___boxed(lean_object* v_value_621_, lean_object* v___x_622_, lean_object* v___x_623_, lean_object* v_a_624_, lean_object* v_x_625_, lean_object* v___y_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_Std_Http_Headers_hasEntry___lam__1(v_value_621_, v___x_622_, v___x_623_, v_a_624_, v_x_625_, v___y_626_);
lean_dec_ref(v___y_626_);
lean_dec_ref(v_value_621_);
return v_res_627_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Headers_hasEntry(lean_object* v_headers_631_, lean_object* v_name_632_, lean_object* v_value_633_){
_start:
{
lean_object* v___f_634_; lean_object* v___f_635_; uint8_t v___x_636_; 
v___f_634_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_635_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
lean_inc_ref(v_name_632_);
v___x_636_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_634_, v___f_635_, v_name_632_, v_headers_631_);
if (v___x_636_ == 0)
{
lean_dec_ref(v_value_633_);
lean_dec_ref(v_name_632_);
lean_dec_ref(v_headers_631_);
return v___x_636_;
}
else
{
lean_object* v_entries_637_; lean_object* v_indexes_638_; lean_object* v___x_639_; lean_object* v___f_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v_entries_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___f_648_; size_t v_sz_649_; size_t v___x_650_; lean_object* v___x_651_; lean_object* v_fst_652_; 
v_entries_637_ = lean_ctor_get(v_headers_631_, 0);
lean_inc_ref(v_entries_637_);
v_indexes_638_ = lean_ctor_get(v_headers_631_, 1);
lean_inc_ref(v_indexes_638_);
lean_dec_ref(v_headers_631_);
v___x_639_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v___f_634_, v___f_635_, v_indexes_638_, v_name_632_);
lean_dec_ref(v_indexes_638_);
lean_inc(v___x_639_);
v___f_640_ = lean_alloc_closure((void*)(l_Std_Http_Headers_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_640_, 0, v___x_639_);
lean_closure_set(v___f_640_, 1, v_entries_637_);
v___x_641_ = ((lean_object*)(l_Std_Http_Headers_getAll___redArg___closed__9));
v___x_642_ = lean_array_get_size(v___x_639_);
v___x_643_ = lean_unsigned_to_nat(0u);
v___x_644_ = lean_mk_empty_array_with_capacity(v___x_642_);
v_entries_645_ = l_Array_mapFinIdxM_map___redArg(v___x_641_, v___x_639_, v___f_640_, v___x_642_, v___x_643_, v___x_644_);
v___x_646_ = lean_box(0);
v___x_647_ = ((lean_object*)(l_Std_Http_Headers_hasEntry___closed__0));
v___f_648_ = lean_alloc_closure((void*)(l_Std_Http_Headers_hasEntry___lam__1___boxed), 6, 3);
lean_closure_set(v___f_648_, 0, v_value_633_);
lean_closure_set(v___f_648_, 1, v___x_647_);
lean_closure_set(v___f_648_, 2, v___x_646_);
v_sz_649_ = lean_array_size(v_entries_645_);
v___x_650_ = ((size_t)0ULL);
v___x_651_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_641_, v_entries_645_, v___f_648_, v_sz_649_, v___x_650_, v___x_647_);
v_fst_652_ = lean_ctor_get(v___x_651_, 0);
lean_inc(v_fst_652_);
lean_dec(v___x_651_);
if (lean_obj_tag(v_fst_652_) == 0)
{
uint8_t v___x_653_; 
v___x_653_ = 0;
return v___x_653_;
}
else
{
lean_object* v_val_654_; 
v_val_654_ = lean_ctor_get(v_fst_652_, 0);
lean_inc(v_val_654_);
lean_dec_ref(v_fst_652_);
if (lean_obj_tag(v_val_654_) == 0)
{
uint8_t v___x_655_; 
v___x_655_ = 0;
return v___x_655_;
}
else
{
lean_dec_ref(v_val_654_);
return v___x_636_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_hasEntry___boxed(lean_object* v_headers_656_, lean_object* v_name_657_, lean_object* v_value_658_){
_start:
{
uint8_t v_res_659_; lean_object* v_r_660_; 
v_res_659_ = l_Std_Http_Headers_hasEntry(v_headers_656_, v_name_657_, v_value_658_);
v_r_660_ = lean_box(v_res_659_);
return v_r_660_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_getLast_x3f(lean_object* v_headers_661_, lean_object* v_name_662_){
_start:
{
lean_object* v___f_663_; lean_object* v___f_664_; uint8_t v___x_665_; 
v___f_663_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_664_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
lean_inc_ref(v_name_662_);
v___x_665_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_663_, v___f_664_, v_name_662_, v_headers_661_);
if (v___x_665_ == 0)
{
lean_object* v___x_666_; 
lean_dec_ref(v_name_662_);
lean_dec_ref(v_headers_661_);
v___x_666_ = lean_box(0);
return v___x_666_;
}
else
{
lean_object* v_entries_667_; lean_object* v_indexes_668_; lean_object* v___x_669_; lean_object* v___f_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v_entries_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; uint8_t v___x_679_; 
v_entries_667_ = lean_ctor_get(v_headers_661_, 0);
lean_inc_ref(v_entries_667_);
v_indexes_668_ = lean_ctor_get(v_headers_661_, 1);
lean_inc_ref(v_indexes_668_);
lean_dec_ref(v_headers_661_);
v___x_669_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v___f_663_, v___f_664_, v_indexes_668_, v_name_662_);
lean_dec_ref(v_indexes_668_);
lean_inc(v___x_669_);
v___f_670_ = lean_alloc_closure((void*)(l_Std_Http_Headers_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_670_, 0, v___x_669_);
lean_closure_set(v___f_670_, 1, v_entries_667_);
v___x_671_ = ((lean_object*)(l_Std_Http_Headers_getAll___redArg___closed__9));
v___x_672_ = lean_array_get_size(v___x_669_);
v___x_673_ = lean_unsigned_to_nat(0u);
v___x_674_ = lean_mk_empty_array_with_capacity(v___x_672_);
v_entries_675_ = l_Array_mapFinIdxM_map___redArg(v___x_671_, v___x_669_, v___f_670_, v___x_672_, v___x_673_, v___x_674_);
v___x_676_ = lean_array_get_size(v_entries_675_);
v___x_677_ = lean_unsigned_to_nat(1u);
v___x_678_ = lean_nat_sub(v___x_676_, v___x_677_);
v___x_679_ = lean_nat_dec_lt(v___x_678_, v___x_676_);
if (v___x_679_ == 0)
{
lean_object* v___x_680_; 
lean_dec(v___x_678_);
lean_dec(v_entries_675_);
v___x_680_ = lean_box(0);
return v___x_680_;
}
else
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = lean_array_fget(v_entries_675_, v___x_678_);
lean_dec(v___x_678_);
lean_dec(v_entries_675_);
v___x_682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_682_, 0, v___x_681_);
return v___x_682_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_getD(lean_object* v_headers_683_, lean_object* v_name_684_, lean_object* v_d_685_){
_start:
{
lean_object* v___f_686_; lean_object* v___f_687_; uint8_t v___x_688_; 
v___f_686_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_687_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
lean_inc_ref(v_name_684_);
v___x_688_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_686_, v___f_687_, v_name_684_, v_headers_683_);
if (v___x_688_ == 0)
{
lean_dec_ref(v_name_684_);
lean_inc_ref(v_d_685_);
return v_d_685_;
}
else
{
lean_object* v_entries_689_; lean_object* v_indexes_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v_entry_693_; lean_object* v___x_694_; lean_object* v_snd_695_; 
v_entries_689_ = lean_ctor_get(v_headers_683_, 0);
v_indexes_690_ = lean_ctor_get(v_headers_683_, 1);
v___x_691_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v___f_686_, v___f_687_, v_indexes_690_, v_name_684_);
v___x_692_ = lean_unsigned_to_nat(0u);
v_entry_693_ = lean_array_fget(v___x_691_, v___x_692_);
lean_dec(v___x_691_);
v___x_694_ = lean_array_fget_borrowed(v_entries_689_, v_entry_693_);
lean_dec(v_entry_693_);
v_snd_695_ = lean_ctor_get(v___x_694_, 1);
lean_inc(v_snd_695_);
return v_snd_695_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_getD___boxed(lean_object* v_headers_696_, lean_object* v_name_697_, lean_object* v_d_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_Std_Http_Headers_getD(v_headers_696_, v_name_697_, v_d_698_);
lean_dec_ref(v_d_698_);
lean_dec_ref(v_headers_696_);
return v_res_699_;
}
}
static lean_object* _init_l_Std_Http_Headers_get_x21___closed__4(void){
_start:
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_704_ = ((lean_object*)(l_Std_Http_Headers_get_x21___closed__3));
v___x_705_ = lean_unsigned_to_nat(14u);
v___x_706_ = lean_unsigned_to_nat(22u);
v___x_707_ = ((lean_object*)(l_Std_Http_Headers_get_x21___closed__2));
v___x_708_ = ((lean_object*)(l_Std_Http_Headers_get_x21___closed__1));
v___x_709_ = l_mkPanicMessageWithDecl(v___x_708_, v___x_707_, v___x_706_, v___x_705_, v___x_704_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_get_x21(lean_object* v_headers_710_, lean_object* v_name_711_){
_start:
{
lean_object* v___f_712_; lean_object* v___f_713_; uint8_t v___x_714_; 
v___f_712_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_713_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
lean_inc_ref(v_name_711_);
v___x_714_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_712_, v___f_713_, v_name_711_, v_headers_710_);
if (v___x_714_ == 0)
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
lean_dec_ref(v_name_711_);
v___x_715_ = ((lean_object*)(l_Std_Http_Headers_get_x21___closed__0));
v___x_716_ = lean_obj_once(&l_Std_Http_Headers_get_x21___closed__4, &l_Std_Http_Headers_get_x21___closed__4_once, _init_l_Std_Http_Headers_get_x21___closed__4);
v___x_717_ = l_panic___redArg(v___x_715_, v___x_716_);
return v___x_717_;
}
else
{
lean_object* v_entries_718_; lean_object* v_indexes_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v_entry_722_; lean_object* v___x_723_; lean_object* v_snd_724_; 
v_entries_718_ = lean_ctor_get(v_headers_710_, 0);
v_indexes_719_ = lean_ctor_get(v_headers_710_, 1);
v___x_720_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v___f_712_, v___f_713_, v_indexes_719_, v_name_711_);
v___x_721_ = lean_unsigned_to_nat(0u);
v_entry_722_ = lean_array_fget(v___x_720_, v___x_721_);
lean_dec(v___x_720_);
v___x_723_ = lean_array_fget_borrowed(v_entries_718_, v_entry_722_);
lean_dec(v_entry_722_);
v_snd_724_ = lean_ctor_get(v___x_723_, 1);
lean_inc(v_snd_724_);
return v_snd_724_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_get_x21___boxed(lean_object* v_headers_725_, lean_object* v_name_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Std_Http_Headers_get_x21(v_headers_725_, v_name_726_);
lean_dec_ref(v_headers_725_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_insert___lam__0(lean_object* v_i_728_, lean_object* v_x_729_){
_start:
{
if (lean_obj_tag(v_x_729_) == 0)
{
lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_730_ = lean_unsigned_to_nat(1u);
v___x_731_ = lean_mk_empty_array_with_capacity(v___x_730_);
v___x_732_ = lean_array_push(v___x_731_, v_i_728_);
v___x_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_733_, 0, v___x_732_);
return v___x_733_;
}
else
{
lean_object* v_val_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_742_; 
v_val_734_ = lean_ctor_get(v_x_729_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v_x_729_);
if (v_isSharedCheck_742_ == 0)
{
v___x_736_ = v_x_729_;
v_isShared_737_ = v_isSharedCheck_742_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_val_734_);
lean_dec(v_x_729_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_742_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_738_; lean_object* v___x_740_; 
v___x_738_ = lean_array_push(v_val_734_, v_i_728_);
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 0, v___x_738_);
v___x_740_ = v___x_736_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v___x_738_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_insert(lean_object* v_headers_743_, lean_object* v_key_744_, lean_object* v_value_745_){
_start:
{
lean_object* v_entries_746_; lean_object* v_indexes_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_761_; 
v_entries_746_ = lean_ctor_get(v_headers_743_, 0);
v_indexes_747_ = lean_ctor_get(v_headers_743_, 1);
v_isSharedCheck_761_ = !lean_is_exclusive(v_headers_743_);
if (v_isSharedCheck_761_ == 0)
{
v___x_749_ = v_headers_743_;
v_isShared_750_ = v_isSharedCheck_761_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_indexes_747_);
lean_inc(v_entries_746_);
lean_dec(v_headers_743_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_761_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___f_751_; lean_object* v___f_752_; lean_object* v_i_753_; lean_object* v_f_754_; lean_object* v___x_755_; lean_object* v_entries_756_; lean_object* v_indexes_757_; lean_object* v___x_759_; 
v___f_751_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_752_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v_i_753_ = lean_array_get_size(v_entries_746_);
v_f_754_ = lean_alloc_closure((void*)(l_Std_Http_Headers_insert___lam__0), 2, 1);
lean_closure_set(v_f_754_, 0, v_i_753_);
lean_inc_ref(v_key_744_);
v___x_755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_755_, 0, v_key_744_);
lean_ctor_set(v___x_755_, 1, v_value_745_);
v_entries_756_ = lean_array_push(v_entries_746_, v___x_755_);
v_indexes_757_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_751_, v___f_752_, v_indexes_747_, v_key_744_, v_f_754_);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 1, v_indexes_757_);
lean_ctor_set(v___x_749_, 0, v_entries_756_);
v___x_759_ = v___x_749_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_entries_756_);
lean_ctor_set(v_reuseFailAlloc_760_, 1, v_indexes_757_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_insert_x21(lean_object* v_headers_762_, lean_object* v_name_763_, lean_object* v_value_764_){
_start:
{
lean_object* v_entries_765_; lean_object* v_indexes_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_782_; 
v_entries_765_ = lean_ctor_get(v_headers_762_, 0);
v_indexes_766_ = lean_ctor_get(v_headers_762_, 1);
v_isSharedCheck_782_ = !lean_is_exclusive(v_headers_762_);
if (v_isSharedCheck_782_ == 0)
{
v___x_768_ = v_headers_762_;
v_isShared_769_ = v_isSharedCheck_782_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_indexes_766_);
lean_inc(v_entries_765_);
lean_dec(v_headers_762_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_782_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___f_772_; lean_object* v___f_773_; lean_object* v_i_774_; lean_object* v_f_775_; lean_object* v___x_776_; lean_object* v_entries_777_; lean_object* v_indexes_778_; lean_object* v___x_780_; 
v___x_770_ = l_Std_Http_Header_Name_ofString_x21(v_name_763_);
v___x_771_ = l_Std_Http_Header_Value_ofString_x21(v_value_764_);
v___f_772_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_773_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v_i_774_ = lean_array_get_size(v_entries_765_);
v_f_775_ = lean_alloc_closure((void*)(l_Std_Http_Headers_insert___lam__0), 2, 1);
lean_closure_set(v_f_775_, 0, v_i_774_);
lean_inc_ref(v___x_770_);
v___x_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_776_, 0, v___x_770_);
lean_ctor_set(v___x_776_, 1, v___x_771_);
v_entries_777_ = lean_array_push(v_entries_765_, v___x_776_);
v_indexes_778_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_772_, v___f_773_, v_indexes_766_, v___x_770_, v_f_775_);
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 1, v_indexes_778_);
lean_ctor_set(v___x_768_, 0, v_entries_777_);
v___x_780_ = v___x_768_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_entries_777_);
lean_ctor_set(v_reuseFailAlloc_781_, 1, v_indexes_778_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_insert_x3f(lean_object* v_headers_783_, lean_object* v_name_784_, lean_object* v_value_785_){
_start:
{
lean_object* v___x_786_; 
v___x_786_ = l_Std_Http_Header_Name_ofString_x3f(v_name_784_);
if (lean_obj_tag(v___x_786_) == 0)
{
lean_object* v___x_787_; 
lean_dec_ref(v_value_785_);
lean_dec_ref(v_headers_783_);
v___x_787_ = lean_box(0);
return v___x_787_;
}
else
{
lean_object* v_val_788_; lean_object* v___x_789_; 
v_val_788_ = lean_ctor_get(v___x_786_, 0);
lean_inc(v_val_788_);
lean_dec_ref(v___x_786_);
v___x_789_ = l_Std_Http_Header_Value_ofString_x3f(v_value_785_);
if (lean_obj_tag(v___x_789_) == 0)
{
lean_object* v___x_790_; 
lean_dec(v_val_788_);
lean_dec_ref(v_headers_783_);
v___x_790_ = lean_box(0);
return v___x_790_;
}
else
{
lean_object* v_val_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_814_; 
v_val_791_ = lean_ctor_get(v___x_789_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_814_ == 0)
{
v___x_793_ = v___x_789_;
v_isShared_794_ = v_isSharedCheck_814_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_val_791_);
lean_dec(v___x_789_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_814_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v_entries_795_; lean_object* v_indexes_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_813_; 
v_entries_795_ = lean_ctor_get(v_headers_783_, 0);
v_indexes_796_ = lean_ctor_get(v_headers_783_, 1);
v_isSharedCheck_813_ = !lean_is_exclusive(v_headers_783_);
if (v_isSharedCheck_813_ == 0)
{
v___x_798_ = v_headers_783_;
v_isShared_799_ = v_isSharedCheck_813_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_indexes_796_);
lean_inc(v_entries_795_);
lean_dec(v_headers_783_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_813_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___f_800_; lean_object* v___f_801_; lean_object* v_i_802_; lean_object* v_f_803_; lean_object* v___x_804_; lean_object* v_entries_805_; lean_object* v_indexes_806_; lean_object* v___x_808_; 
v___f_800_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_801_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v_i_802_ = lean_array_get_size(v_entries_795_);
v_f_803_ = lean_alloc_closure((void*)(l_Std_Http_Headers_insert___lam__0), 2, 1);
lean_closure_set(v_f_803_, 0, v_i_802_);
lean_inc(v_val_788_);
v___x_804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_804_, 0, v_val_788_);
lean_ctor_set(v___x_804_, 1, v_val_791_);
v_entries_805_ = lean_array_push(v_entries_795_, v___x_804_);
v_indexes_806_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_800_, v___f_801_, v_indexes_796_, v_val_788_, v_f_803_);
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 1, v_indexes_806_);
lean_ctor_set(v___x_798_, 0, v_entries_805_);
v___x_808_ = v___x_798_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_entries_805_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v_indexes_806_);
v___x_808_ = v_reuseFailAlloc_812_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
lean_object* v___x_810_; 
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 0, v___x_808_);
v___x_810_ = v___x_793_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v___x_808_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_insertMany___lam__1(lean_object* v_key_815_, lean_object* v___f_816_, lean_object* v___f_817_, lean_object* v_x1_818_, lean_object* v_x2_819_){
_start:
{
lean_object* v_entries_820_; lean_object* v_indexes_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_833_; 
v_entries_820_ = lean_ctor_get(v_x1_818_, 0);
v_indexes_821_ = lean_ctor_get(v_x1_818_, 1);
v_isSharedCheck_833_ = !lean_is_exclusive(v_x1_818_);
if (v_isSharedCheck_833_ == 0)
{
v___x_823_ = v_x1_818_;
v_isShared_824_ = v_isSharedCheck_833_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_indexes_821_);
lean_inc(v_entries_820_);
lean_dec(v_x1_818_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_833_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v_i_825_; lean_object* v_f_826_; lean_object* v___x_827_; lean_object* v_entries_828_; lean_object* v_indexes_829_; lean_object* v___x_831_; 
v_i_825_ = lean_array_get_size(v_entries_820_);
v_f_826_ = lean_alloc_closure((void*)(l_Std_Http_Headers_insert___lam__0), 2, 1);
lean_closure_set(v_f_826_, 0, v_i_825_);
lean_inc_ref(v_key_815_);
v___x_827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_827_, 0, v_key_815_);
lean_ctor_set(v___x_827_, 1, v_x2_819_);
v_entries_828_ = lean_array_push(v_entries_820_, v___x_827_);
v_indexes_829_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_816_, v___f_817_, v_indexes_821_, v_key_815_, v_f_826_);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 1, v_indexes_829_);
lean_ctor_set(v___x_823_, 0, v_entries_828_);
v___x_831_ = v___x_823_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_entries_828_);
lean_ctor_set(v_reuseFailAlloc_832_, 1, v_indexes_829_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_insertMany(lean_object* v_headers_834_, lean_object* v_key_835_, lean_object* v_values_836_){
_start:
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; uint8_t v___x_840_; 
v___x_837_ = lean_unsigned_to_nat(0u);
v___x_838_ = lean_array_get_size(v_values_836_);
v___x_839_ = ((lean_object*)(l_Std_Http_Headers_getAll___redArg___closed__9));
v___x_840_ = lean_nat_dec_lt(v___x_837_, v___x_838_);
if (v___x_840_ == 0)
{
lean_dec_ref(v_values_836_);
lean_dec_ref(v_key_835_);
return v_headers_834_;
}
else
{
lean_object* v___f_841_; lean_object* v___f_842_; lean_object* v___f_843_; uint8_t v___x_844_; 
v___f_841_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_842_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v___f_843_ = lean_alloc_closure((void*)(l_Std_Http_Headers_insertMany___lam__1), 5, 3);
lean_closure_set(v___f_843_, 0, v_key_835_);
lean_closure_set(v___f_843_, 1, v___f_841_);
lean_closure_set(v___f_843_, 2, v___f_842_);
v___x_844_ = lean_nat_dec_le(v___x_838_, v___x_838_);
if (v___x_844_ == 0)
{
if (v___x_840_ == 0)
{
lean_dec_ref(v___f_843_);
lean_dec_ref(v_values_836_);
return v_headers_834_;
}
else
{
size_t v___x_845_; size_t v___x_846_; lean_object* v___x_847_; 
v___x_845_ = ((size_t)0ULL);
v___x_846_ = lean_usize_of_nat(v___x_838_);
v___x_847_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_839_, v___f_843_, v_values_836_, v___x_845_, v___x_846_, v_headers_834_);
return v___x_847_;
}
}
else
{
size_t v___x_848_; size_t v___x_849_; lean_object* v___x_850_; 
v___x_848_ = ((size_t)0ULL);
v___x_849_ = lean_usize_of_nat(v___x_838_);
v___x_850_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_839_, v___f_843_, v_values_836_, v___x_848_, v___x_849_, v_headers_834_);
return v___x_850_;
}
}
}
}
static lean_object* _init_l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__1(void){
_start:
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_853_ = lean_obj_once(&l_Std_Http_instInhabitedHeaders_default___closed__2, &l_Std_Http_instInhabitedHeaders_default___closed__2_once, _init_l_Std_Http_instInhabitedHeaders_default___closed__2);
v___x_854_ = ((lean_object*)(l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__0));
v___x_855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_855_, 0, v___x_854_);
lean_ctor_set(v___x_855_, 1, v___x_853_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0(lean_object* v_00_u03b2_856_){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__1, &l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__1_once, _init_l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__1);
return v___x_857_;
}
}
static lean_object* _init_l_Std_Http_Headers_empty___closed__0(void){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0(lean_box(0));
return v___x_858_;
}
}
static lean_object* _init_l_Std_Http_Headers_empty(void){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = lean_obj_once(&l_Std_Http_Headers_empty___closed__0, &l_Std_Http_Headers_empty___closed__0_once, _init_l_Std_Http_Headers_empty___closed__0);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__3(lean_object* v_i_860_, lean_object* v_a_861_, lean_object* v_x_862_){
_start:
{
if (lean_obj_tag(v_x_862_) == 0)
{
lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v_val_865_; lean_object* v___x_866_; 
v___x_863_ = lean_box(0);
v___x_864_ = l_Std_Http_Headers_insert___lam__0(v_i_860_, v___x_863_);
v_val_865_ = lean_ctor_get(v___x_864_, 0);
lean_inc(v_val_865_);
lean_dec(v___x_864_);
v___x_866_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_866_, 0, v_a_861_);
lean_ctor_set(v___x_866_, 1, v_val_865_);
lean_ctor_set(v___x_866_, 2, v_x_862_);
return v___x_866_;
}
else
{
lean_object* v_key_867_; lean_object* v_value_868_; lean_object* v_tail_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_884_; 
v_key_867_ = lean_ctor_get(v_x_862_, 0);
v_value_868_ = lean_ctor_get(v_x_862_, 1);
v_tail_869_ = lean_ctor_get(v_x_862_, 2);
v_isSharedCheck_884_ = !lean_is_exclusive(v_x_862_);
if (v_isSharedCheck_884_ == 0)
{
v___x_871_ = v_x_862_;
v_isShared_872_ = v_isSharedCheck_884_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_tail_869_);
lean_inc(v_value_868_);
lean_inc(v_key_867_);
lean_dec(v_x_862_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_884_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
uint8_t v___x_873_; 
v___x_873_ = lean_string_dec_eq(v_key_867_, v_a_861_);
if (v___x_873_ == 0)
{
lean_object* v_tail_874_; lean_object* v___x_876_; 
v_tail_874_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__3(v_i_860_, v_a_861_, v_tail_869_);
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 2, v_tail_874_);
v___x_876_ = v___x_871_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_key_867_);
lean_ctor_set(v_reuseFailAlloc_877_, 1, v_value_868_);
lean_ctor_set(v_reuseFailAlloc_877_, 2, v_tail_874_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
else
{
lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v_val_880_; lean_object* v___x_882_; 
lean_dec(v_key_867_);
v___x_878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_878_, 0, v_value_868_);
v___x_879_ = l_Std_Http_Headers_insert___lam__0(v_i_860_, v___x_878_);
v_val_880_ = lean_ctor_get(v___x_879_, 0);
lean_inc(v_val_880_);
lean_dec(v___x_879_);
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 1, v_val_880_);
lean_ctor_set(v___x_871_, 0, v_a_861_);
v___x_882_ = v___x_871_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_a_861_);
lean_ctor_set(v_reuseFailAlloc_883_, 1, v_val_880_);
lean_ctor_set(v_reuseFailAlloc_883_, 2, v_tail_869_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_x_885_, lean_object* v_x_886_){
_start:
{
if (lean_obj_tag(v_x_886_) == 0)
{
return v_x_885_;
}
else
{
lean_object* v_key_887_; lean_object* v_value_888_; lean_object* v_tail_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_912_; 
v_key_887_ = lean_ctor_get(v_x_886_, 0);
v_value_888_ = lean_ctor_get(v_x_886_, 1);
v_tail_889_ = lean_ctor_get(v_x_886_, 2);
v_isSharedCheck_912_ = !lean_is_exclusive(v_x_886_);
if (v_isSharedCheck_912_ == 0)
{
v___x_891_ = v_x_886_;
v_isShared_892_ = v_isSharedCheck_912_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_tail_889_);
lean_inc(v_value_888_);
lean_inc(v_key_887_);
lean_dec(v_x_886_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_912_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_893_; uint64_t v___x_894_; uint64_t v___x_895_; uint64_t v___x_896_; uint64_t v_fold_897_; uint64_t v___x_898_; uint64_t v___x_899_; uint64_t v___x_900_; size_t v___x_901_; size_t v___x_902_; size_t v___x_903_; size_t v___x_904_; size_t v___x_905_; lean_object* v___x_906_; lean_object* v___x_908_; 
v___x_893_ = lean_array_get_size(v_x_885_);
v___x_894_ = lean_string_hash(v_key_887_);
v___x_895_ = 32ULL;
v___x_896_ = lean_uint64_shift_right(v___x_894_, v___x_895_);
v_fold_897_ = lean_uint64_xor(v___x_894_, v___x_896_);
v___x_898_ = 16ULL;
v___x_899_ = lean_uint64_shift_right(v_fold_897_, v___x_898_);
v___x_900_ = lean_uint64_xor(v_fold_897_, v___x_899_);
v___x_901_ = lean_uint64_to_usize(v___x_900_);
v___x_902_ = lean_usize_of_nat(v___x_893_);
v___x_903_ = ((size_t)1ULL);
v___x_904_ = lean_usize_sub(v___x_902_, v___x_903_);
v___x_905_ = lean_usize_land(v___x_901_, v___x_904_);
v___x_906_ = lean_array_uget_borrowed(v_x_885_, v___x_905_);
lean_inc(v___x_906_);
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 2, v___x_906_);
v___x_908_ = v___x_891_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_key_887_);
lean_ctor_set(v_reuseFailAlloc_911_, 1, v_value_888_);
lean_ctor_set(v_reuseFailAlloc_911_, 2, v___x_906_);
v___x_908_ = v_reuseFailAlloc_911_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
lean_object* v___x_909_; 
v___x_909_ = lean_array_uset(v_x_885_, v___x_905_, v___x_908_);
v_x_885_ = v___x_909_;
v_x_886_ = v_tail_889_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_i_913_, lean_object* v_source_914_, lean_object* v_target_915_){
_start:
{
lean_object* v___x_916_; uint8_t v___x_917_; 
v___x_916_ = lean_array_get_size(v_source_914_);
v___x_917_ = lean_nat_dec_lt(v_i_913_, v___x_916_);
if (v___x_917_ == 0)
{
lean_dec_ref(v_source_914_);
lean_dec(v_i_913_);
return v_target_915_;
}
else
{
lean_object* v_es_918_; lean_object* v___x_919_; lean_object* v_source_920_; lean_object* v_target_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v_es_918_ = lean_array_fget(v_source_914_, v_i_913_);
v___x_919_ = lean_box(0);
v_source_920_ = lean_array_fset(v_source_914_, v_i_913_, v___x_919_);
v_target_921_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_target_915_, v_es_918_);
v___x_922_ = lean_unsigned_to_nat(1u);
v___x_923_ = lean_nat_add(v_i_913_, v___x_922_);
lean_dec(v_i_913_);
v_i_913_ = v___x_923_;
v_source_914_ = v_source_920_;
v_target_915_ = v_target_921_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2___redArg(lean_object* v_data_925_){
_start:
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v_nbuckets_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_926_ = lean_array_get_size(v_data_925_);
v___x_927_ = lean_unsigned_to_nat(2u);
v_nbuckets_928_ = lean_nat_mul(v___x_926_, v___x_927_);
v___x_929_ = lean_unsigned_to_nat(0u);
v___x_930_ = lean_box(0);
v___x_931_ = lean_mk_array(v_nbuckets_928_, v___x_930_);
v___x_932_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2_spec__3___redArg(v___x_929_, v_data_925_, v___x_931_);
return v___x_932_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1___redArg(lean_object* v_a_933_, lean_object* v_x_934_){
_start:
{
if (lean_obj_tag(v_x_934_) == 0)
{
uint8_t v___x_935_; 
v___x_935_ = 0;
return v___x_935_;
}
else
{
lean_object* v_key_936_; lean_object* v_tail_937_; uint8_t v___x_938_; 
v_key_936_ = lean_ctor_get(v_x_934_, 0);
v_tail_937_ = lean_ctor_get(v_x_934_, 2);
v___x_938_ = lean_string_dec_eq(v_key_936_, v_a_933_);
if (v___x_938_ == 0)
{
v_x_934_ = v_tail_937_;
goto _start;
}
else
{
return v___x_938_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_a_940_, lean_object* v_x_941_){
_start:
{
uint8_t v_res_942_; lean_object* v_r_943_; 
v_res_942_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1___redArg(v_a_940_, v_x_941_);
lean_dec(v_x_941_);
lean_dec_ref(v_a_940_);
v_r_943_ = lean_box(v_res_942_);
return v_r_943_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0(lean_object* v_i_944_, lean_object* v_m_945_, lean_object* v_a_946_){
_start:
{
lean_object* v_size_947_; lean_object* v_buckets_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_998_; 
v_size_947_ = lean_ctor_get(v_m_945_, 0);
v_buckets_948_ = lean_ctor_get(v_m_945_, 1);
v_isSharedCheck_998_ = !lean_is_exclusive(v_m_945_);
if (v_isSharedCheck_998_ == 0)
{
v___x_950_ = v_m_945_;
v_isShared_951_ = v_isSharedCheck_998_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_buckets_948_);
lean_inc(v_size_947_);
lean_dec(v_m_945_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_998_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_952_; uint64_t v___x_953_; uint64_t v___x_954_; uint64_t v___x_955_; uint64_t v_fold_956_; uint64_t v___x_957_; uint64_t v___x_958_; uint64_t v___x_959_; size_t v___x_960_; size_t v___x_961_; size_t v___x_962_; size_t v___x_963_; size_t v___x_964_; lean_object* v_bkt_965_; uint8_t v___x_966_; 
v___x_952_ = lean_array_get_size(v_buckets_948_);
v___x_953_ = lean_string_hash(v_a_946_);
v___x_954_ = 32ULL;
v___x_955_ = lean_uint64_shift_right(v___x_953_, v___x_954_);
v_fold_956_ = lean_uint64_xor(v___x_953_, v___x_955_);
v___x_957_ = 16ULL;
v___x_958_ = lean_uint64_shift_right(v_fold_956_, v___x_957_);
v___x_959_ = lean_uint64_xor(v_fold_956_, v___x_958_);
v___x_960_ = lean_uint64_to_usize(v___x_959_);
v___x_961_ = lean_usize_of_nat(v___x_952_);
v___x_962_ = ((size_t)1ULL);
v___x_963_ = lean_usize_sub(v___x_961_, v___x_962_);
v___x_964_ = lean_usize_land(v___x_960_, v___x_963_);
v_bkt_965_ = lean_array_uget_borrowed(v_buckets_948_, v___x_964_);
v___x_966_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1___redArg(v_a_946_, v_bkt_965_);
if (v___x_966_ == 0)
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v_size_x27_970_; lean_object* v___x_971_; lean_object* v_buckets_x27_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; uint8_t v___x_978_; 
v___x_967_ = lean_unsigned_to_nat(1u);
v___x_968_ = lean_mk_empty_array_with_capacity(v___x_967_);
v___x_969_ = lean_array_push(v___x_968_, v_i_944_);
v_size_x27_970_ = lean_nat_add(v_size_947_, v___x_967_);
lean_dec(v_size_947_);
lean_inc(v_bkt_965_);
v___x_971_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_971_, 0, v_a_946_);
lean_ctor_set(v___x_971_, 1, v___x_969_);
lean_ctor_set(v___x_971_, 2, v_bkt_965_);
v_buckets_x27_972_ = lean_array_uset(v_buckets_948_, v___x_964_, v___x_971_);
v___x_973_ = lean_unsigned_to_nat(4u);
v___x_974_ = lean_nat_mul(v_size_x27_970_, v___x_973_);
v___x_975_ = lean_unsigned_to_nat(3u);
v___x_976_ = lean_nat_div(v___x_974_, v___x_975_);
lean_dec(v___x_974_);
v___x_977_ = lean_array_get_size(v_buckets_x27_972_);
v___x_978_ = lean_nat_dec_le(v___x_976_, v___x_977_);
lean_dec(v___x_976_);
if (v___x_978_ == 0)
{
lean_object* v_val_979_; lean_object* v___x_981_; 
v_val_979_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2___redArg(v_buckets_x27_972_);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 1, v_val_979_);
lean_ctor_set(v___x_950_, 0, v_size_x27_970_);
v___x_981_ = v___x_950_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_size_x27_970_);
lean_ctor_set(v_reuseFailAlloc_982_, 1, v_val_979_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
else
{
lean_object* v___x_984_; 
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 1, v_buckets_x27_972_);
lean_ctor_set(v___x_950_, 0, v_size_x27_970_);
v___x_984_ = v___x_950_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_size_x27_970_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v_buckets_x27_972_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
}
else
{
lean_object* v___x_986_; lean_object* v_buckets_x27_987_; lean_object* v_bkt_x27_988_; lean_object* v___y_990_; uint8_t v___x_995_; 
lean_inc(v_bkt_965_);
v___x_986_ = lean_box(0);
v_buckets_x27_987_ = lean_array_uset(v_buckets_948_, v___x_964_, v___x_986_);
lean_inc_ref(v_a_946_);
v_bkt_x27_988_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__3(v_i_944_, v_a_946_, v_bkt_965_);
v___x_995_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1___redArg(v_a_946_, v_bkt_x27_988_);
lean_dec_ref(v_a_946_);
if (v___x_995_ == 0)
{
lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_996_ = lean_unsigned_to_nat(1u);
v___x_997_ = lean_nat_sub(v_size_947_, v___x_996_);
lean_dec(v_size_947_);
v___y_990_ = v___x_997_;
goto v___jp_989_;
}
else
{
v___y_990_ = v_size_947_;
goto v___jp_989_;
}
v___jp_989_:
{
lean_object* v___x_991_; lean_object* v___x_993_; 
v___x_991_ = lean_array_uset(v_buckets_x27_987_, v___x_964_, v_bkt_x27_988_);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 1, v___x_991_);
lean_ctor_set(v___x_950_, 0, v___y_990_);
v___x_993_ = v___x_950_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v___y_990_);
lean_ctor_set(v_reuseFailAlloc_994_, 1, v___x_991_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1___redArg(lean_object* v_x_999_, lean_object* v_x_1000_){
_start:
{
if (lean_obj_tag(v_x_1000_) == 0)
{
return v_x_999_;
}
else
{
lean_object* v_head_1001_; lean_object* v_tail_1002_; lean_object* v_fst_1003_; lean_object* v_entries_1004_; lean_object* v_indexes_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1016_; 
v_head_1001_ = lean_ctor_get(v_x_1000_, 0);
lean_inc(v_head_1001_);
v_tail_1002_ = lean_ctor_get(v_x_1000_, 1);
lean_inc(v_tail_1002_);
lean_dec_ref(v_x_1000_);
v_fst_1003_ = lean_ctor_get(v_head_1001_, 0);
lean_inc(v_fst_1003_);
v_entries_1004_ = lean_ctor_get(v_x_999_, 0);
v_indexes_1005_ = lean_ctor_get(v_x_999_, 1);
v_isSharedCheck_1016_ = !lean_is_exclusive(v_x_999_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_1007_ = v_x_999_;
v_isShared_1008_ = v_isSharedCheck_1016_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_indexes_1005_);
lean_inc(v_entries_1004_);
lean_dec(v_x_999_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1016_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v_i_1009_; lean_object* v_entries_1010_; lean_object* v_indexes_1011_; lean_object* v___x_1013_; 
v_i_1009_ = lean_array_get_size(v_entries_1004_);
v_entries_1010_ = lean_array_push(v_entries_1004_, v_head_1001_);
v_indexes_1011_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0(v_i_1009_, v_indexes_1005_, v_fst_1003_);
if (v_isShared_1008_ == 0)
{
lean_ctor_set(v___x_1007_, 1, v_indexes_1011_);
lean_ctor_set(v___x_1007_, 0, v_entries_1010_);
v___x_1013_ = v___x_1007_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_entries_1010_);
lean_ctor_set(v_reuseFailAlloc_1015_, 1, v_indexes_1011_);
v___x_1013_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
v_x_999_ = v___x_1013_;
v_x_1000_ = v_tail_1002_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1017_; 
v___x_1017_ = l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0(lean_box(0));
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0___redArg(lean_object* v_pairs_1018_){
_start:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1019_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0___redArg___closed__0, &l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0___redArg___closed__0_once, _init_l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0___redArg___closed__0);
v___x_1020_ = l_List_foldl___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1___redArg(v___x_1019_, v_pairs_1018_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_ofList(lean_object* v_pairs_1021_){
_start:
{
lean_object* v___x_1022_; 
v___x_1022_ = l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0___redArg(v_pairs_1021_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0(lean_object* v_00_u03b2_1023_, lean_object* v_inst_1024_, lean_object* v_inst_1025_, lean_object* v_pairs_1026_){
_start:
{
lean_object* v___x_1027_; 
v___x_1027_ = l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0___redArg(v_pairs_1026_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1(lean_object* v_00_u03b2_1028_, lean_object* v_x_1029_, lean_object* v_x_1030_){
_start:
{
lean_object* v___x_1031_; 
v___x_1031_ = l_List_foldl___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1___redArg(v_x_1029_, v_x_1030_);
return v___x_1031_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1032_, lean_object* v_a_1033_, lean_object* v_x_1034_){
_start:
{
uint8_t v___x_1035_; 
v___x_1035_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1___redArg(v_a_1033_, v_x_1034_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1036_, lean_object* v_a_1037_, lean_object* v_x_1038_){
_start:
{
uint8_t v_res_1039_; lean_object* v_r_1040_; 
v_res_1039_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1(v_00_u03b2_1036_, v_a_1037_, v_x_1038_);
lean_dec(v_x_1038_);
lean_dec_ref(v_a_1037_);
v_r_1040_ = lean_box(v_res_1039_);
return v_r_1040_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1041_, lean_object* v_data_1042_){
_start:
{
lean_object* v___x_1043_; 
v___x_1043_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2___redArg(v_data_1042_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_1044_, lean_object* v_i_1045_, lean_object* v_source_1046_, lean_object* v_target_1047_){
_start:
{
lean_object* v___x_1048_; 
v___x_1048_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2_spec__3___redArg(v_i_1045_, v_source_1046_, v_target_1047_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_1049_, lean_object* v_x_1050_, lean_object* v_x_1051_){
_start:
{
lean_object* v___x_1052_; 
v___x_1052_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_x_1050_, v_x_1051_);
return v___x_1052_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Headers_contains(lean_object* v_headers_1053_, lean_object* v_name_1054_){
_start:
{
lean_object* v_indexes_1055_; lean_object* v___f_1056_; lean_object* v___f_1057_; uint8_t v___x_1058_; 
v_indexes_1055_ = lean_ctor_get(v_headers_1053_, 1);
v___f_1056_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_1057_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v___x_1058_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_1056_, v___f_1057_, v_indexes_1055_, v_name_1054_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_contains___boxed(lean_object* v_headers_1059_, lean_object* v_name_1060_){
_start:
{
uint8_t v_res_1061_; lean_object* v_r_1062_; 
v_res_1061_ = l_Std_Http_Headers_contains(v_headers_1059_, v_name_1060_);
lean_dec_ref(v_headers_1059_);
v_r_1062_ = lean_box(v_res_1061_);
return v_r_1062_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_erase___lam__1(lean_object* v___f_1063_, lean_object* v___f_1064_, lean_object* v_x1_1065_, lean_object* v_x2_1066_){
_start:
{
lean_object* v_fst_1067_; lean_object* v_entries_1068_; lean_object* v_indexes_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1080_; 
v_fst_1067_ = lean_ctor_get(v_x2_1066_, 0);
lean_inc(v_fst_1067_);
v_entries_1068_ = lean_ctor_get(v_x1_1065_, 0);
v_indexes_1069_ = lean_ctor_get(v_x1_1065_, 1);
v_isSharedCheck_1080_ = !lean_is_exclusive(v_x1_1065_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1071_ = v_x1_1065_;
v_isShared_1072_ = v_isSharedCheck_1080_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_indexes_1069_);
lean_inc(v_entries_1068_);
lean_dec(v_x1_1065_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1080_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v_i_1073_; lean_object* v_f_1074_; lean_object* v_entries_1075_; lean_object* v_indexes_1076_; lean_object* v___x_1078_; 
v_i_1073_ = lean_array_get_size(v_entries_1068_);
v_f_1074_ = lean_alloc_closure((void*)(l_Std_Http_Headers_insert___lam__0), 2, 1);
lean_closure_set(v_f_1074_, 0, v_i_1073_);
v_entries_1075_ = lean_array_push(v_entries_1068_, v_x2_1066_);
v_indexes_1076_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_1063_, v___f_1064_, v_indexes_1069_, v_fst_1067_, v_f_1074_);
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 1, v_indexes_1076_);
lean_ctor_set(v___x_1071_, 0, v_entries_1075_);
v___x_1078_ = v___x_1071_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_entries_1075_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v_indexes_1076_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_erase___lam__0(lean_object* v_name_1081_, lean_object* v_x1_1082_, lean_object* v_x2_1083_){
_start:
{
lean_object* v_fst_1084_; uint8_t v___x_1085_; 
v_fst_1084_ = lean_ctor_get(v_x2_1083_, 0);
v___x_1085_ = lean_string_dec_eq(v_fst_1084_, v_name_1081_);
if (v___x_1085_ == 0)
{
lean_object* v___x_1086_; 
v___x_1086_ = lean_array_push(v_x1_1082_, v_x2_1083_);
return v___x_1086_;
}
else
{
lean_dec_ref(v_x2_1083_);
return v_x1_1082_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_erase___lam__0___boxed(lean_object* v_name_1087_, lean_object* v_x1_1088_, lean_object* v_x2_1089_){
_start:
{
lean_object* v_res_1090_; 
v_res_1090_ = l_Std_Http_Headers_erase___lam__0(v_name_1087_, v_x1_1088_, v_x2_1089_);
lean_dec_ref(v_name_1087_);
return v_res_1090_;
}
}
static lean_object* _init_l_Std_Http_Headers_erase___closed__1(void){
_start:
{
lean_object* v___f_1094_; lean_object* v___f_1095_; lean_object* v___x_1096_; 
v___f_1094_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v___f_1095_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___x_1096_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v___f_1095_, v___f_1094_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_erase(lean_object* v_headers_1097_, lean_object* v_name_1098_){
_start:
{
lean_object* v___f_1099_; lean_object* v___f_1100_; uint8_t v___x_1101_; 
v___f_1099_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_1100_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
lean_inc_ref(v_name_1098_);
v___x_1101_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_1099_, v___f_1100_, v_name_1098_, v_headers_1097_);
if (v___x_1101_ == 0)
{
lean_dec_ref(v_name_1098_);
return v_headers_1097_;
}
else
{
lean_object* v_entries_1102_; lean_object* v___f_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___y_1107_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; uint8_t v___x_1121_; 
v_entries_1102_ = lean_ctor_get(v_headers_1097_, 0);
lean_inc_ref(v_entries_1102_);
lean_dec_ref(v_headers_1097_);
v___f_1103_ = ((lean_object*)(l_Std_Http_Headers_erase___closed__0));
v___x_1104_ = lean_obj_once(&l_Std_Http_Headers_erase___closed__1, &l_Std_Http_Headers_erase___closed__1_once, _init_l_Std_Http_Headers_erase___closed__1);
v___x_1105_ = lean_unsigned_to_nat(0u);
v___x_1118_ = lean_array_get_size(v_entries_1102_);
v___x_1119_ = ((lean_object*)(l_Std_Http_instInhabitedHeaders_default___closed__0));
v___x_1120_ = ((lean_object*)(l_Std_Http_Headers_getAll___redArg___closed__9));
v___x_1121_ = lean_nat_dec_lt(v___x_1105_, v___x_1118_);
if (v___x_1121_ == 0)
{
lean_dec_ref(v_entries_1102_);
lean_dec_ref(v_name_1098_);
v___y_1107_ = v___x_1119_;
goto v___jp_1106_;
}
else
{
lean_object* v___f_1122_; uint8_t v___x_1123_; 
v___f_1122_ = lean_alloc_closure((void*)(l_Std_Http_Headers_erase___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1122_, 0, v_name_1098_);
v___x_1123_ = lean_nat_dec_le(v___x_1118_, v___x_1118_);
if (v___x_1123_ == 0)
{
if (v___x_1121_ == 0)
{
lean_dec_ref(v___f_1122_);
lean_dec_ref(v_entries_1102_);
v___y_1107_ = v___x_1119_;
goto v___jp_1106_;
}
else
{
size_t v___x_1124_; size_t v___x_1125_; lean_object* v___x_1126_; 
v___x_1124_ = ((size_t)0ULL);
v___x_1125_ = lean_usize_of_nat(v___x_1118_);
v___x_1126_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1120_, v___f_1122_, v_entries_1102_, v___x_1124_, v___x_1125_, v___x_1119_);
v___y_1107_ = v___x_1126_;
goto v___jp_1106_;
}
}
else
{
size_t v___x_1127_; size_t v___x_1128_; lean_object* v___x_1129_; 
v___x_1127_ = ((size_t)0ULL);
v___x_1128_ = lean_usize_of_nat(v___x_1118_);
v___x_1129_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1120_, v___f_1122_, v_entries_1102_, v___x_1127_, v___x_1128_, v___x_1119_);
v___y_1107_ = v___x_1129_;
goto v___jp_1106_;
}
}
v___jp_1106_:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; uint8_t v___x_1110_; 
v___x_1108_ = lean_array_get_size(v___y_1107_);
v___x_1109_ = ((lean_object*)(l_Std_Http_Headers_getAll___redArg___closed__9));
v___x_1110_ = lean_nat_dec_lt(v___x_1105_, v___x_1108_);
if (v___x_1110_ == 0)
{
lean_dec_ref(v___y_1107_);
return v___x_1104_;
}
else
{
uint8_t v___x_1111_; 
v___x_1111_ = lean_nat_dec_le(v___x_1108_, v___x_1108_);
if (v___x_1111_ == 0)
{
if (v___x_1110_ == 0)
{
lean_dec_ref(v___y_1107_);
return v___x_1104_;
}
else
{
size_t v___x_1112_; size_t v___x_1113_; lean_object* v___x_1114_; 
v___x_1112_ = ((size_t)0ULL);
v___x_1113_ = lean_usize_of_nat(v___x_1108_);
v___x_1114_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1109_, v___f_1103_, v___y_1107_, v___x_1112_, v___x_1113_, v___x_1104_);
return v___x_1114_;
}
}
else
{
size_t v___x_1115_; size_t v___x_1116_; lean_object* v___x_1117_; 
v___x_1115_ = ((size_t)0ULL);
v___x_1116_ = lean_usize_of_nat(v___x_1108_);
v___x_1117_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1109_, v___f_1103_, v___y_1107_, v___x_1115_, v___x_1116_, v___x_1104_);
return v___x_1117_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_size(lean_object* v_headers_1130_){
_start:
{
lean_object* v_entries_1131_; lean_object* v___x_1132_; 
v_entries_1131_ = lean_ctor_get(v_headers_1130_, 0);
v___x_1132_ = lean_array_get_size(v_entries_1131_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_size___boxed(lean_object* v_headers_1133_){
_start:
{
lean_object* v_res_1134_; 
v_res_1134_ = l_Std_Http_Headers_size(v_headers_1133_);
lean_dec_ref(v_headers_1133_);
return v_res_1134_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Headers_isEmpty(lean_object* v_headers_1135_){
_start:
{
lean_object* v_entries_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; uint8_t v___x_1139_; 
v_entries_1136_ = lean_ctor_get(v_headers_1135_, 0);
v___x_1137_ = lean_array_get_size(v_entries_1136_);
v___x_1138_ = lean_unsigned_to_nat(0u);
v___x_1139_ = lean_nat_dec_eq(v___x_1137_, v___x_1138_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_isEmpty___boxed(lean_object* v_headers_1140_){
_start:
{
uint8_t v_res_1141_; lean_object* v_r_1142_; 
v_res_1141_ = l_Std_Http_Headers_isEmpty(v_headers_1140_);
lean_dec_ref(v_headers_1140_);
v_r_1142_ = lean_box(v_res_1141_);
return v_r_1142_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___redArg(lean_object* v_as_1143_, size_t v_i_1144_, size_t v_stop_1145_, lean_object* v_b_1146_){
_start:
{
uint8_t v___x_1147_; 
v___x_1147_ = lean_usize_dec_eq(v_i_1144_, v_stop_1145_);
if (v___x_1147_ == 0)
{
lean_object* v___x_1148_; lean_object* v_fst_1149_; lean_object* v_entries_1150_; lean_object* v_indexes_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1164_; 
v___x_1148_ = lean_array_uget_borrowed(v_as_1143_, v_i_1144_);
v_fst_1149_ = lean_ctor_get(v___x_1148_, 0);
v_entries_1150_ = lean_ctor_get(v_b_1146_, 0);
v_indexes_1151_ = lean_ctor_get(v_b_1146_, 1);
v_isSharedCheck_1164_ = !lean_is_exclusive(v_b_1146_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1153_ = v_b_1146_;
v_isShared_1154_ = v_isSharedCheck_1164_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_indexes_1151_);
lean_inc(v_entries_1150_);
lean_dec(v_b_1146_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1164_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v_i_1155_; lean_object* v_entries_1156_; lean_object* v_indexes_1157_; lean_object* v___x_1159_; 
v_i_1155_ = lean_array_get_size(v_entries_1150_);
lean_inc(v___x_1148_);
v_entries_1156_ = lean_array_push(v_entries_1150_, v___x_1148_);
lean_inc(v_fst_1149_);
v_indexes_1157_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0(v_i_1155_, v_indexes_1151_, v_fst_1149_);
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 1, v_indexes_1157_);
lean_ctor_set(v___x_1153_, 0, v_entries_1156_);
v___x_1159_ = v___x_1153_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_entries_1156_);
lean_ctor_set(v_reuseFailAlloc_1163_, 1, v_indexes_1157_);
v___x_1159_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
size_t v___x_1160_; size_t v___x_1161_; 
v___x_1160_ = ((size_t)1ULL);
v___x_1161_ = lean_usize_add(v_i_1144_, v___x_1160_);
v_i_1144_ = v___x_1161_;
v_b_1146_ = v___x_1159_;
goto _start;
}
}
}
else
{
return v_b_1146_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___redArg___boxed(lean_object* v_as_1165_, lean_object* v_i_1166_, lean_object* v_stop_1167_, lean_object* v_b_1168_){
_start:
{
size_t v_i_boxed_1169_; size_t v_stop_boxed_1170_; lean_object* v_res_1171_; 
v_i_boxed_1169_ = lean_unbox_usize(v_i_1166_);
lean_dec(v_i_1166_);
v_stop_boxed_1170_ = lean_unbox_usize(v_stop_1167_);
lean_dec(v_stop_1167_);
v_res_1171_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___redArg(v_as_1165_, v_i_boxed_1169_, v_stop_boxed_1170_, v_b_1168_);
lean_dec_ref(v_as_1165_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0___redArg(lean_object* v_m1_1172_, lean_object* v_m2_1173_){
_start:
{
lean_object* v_entries_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; uint8_t v___x_1177_; 
v_entries_1174_ = lean_ctor_get(v_m2_1173_, 0);
v___x_1175_ = lean_unsigned_to_nat(0u);
v___x_1176_ = lean_array_get_size(v_entries_1174_);
v___x_1177_ = lean_nat_dec_lt(v___x_1175_, v___x_1176_);
if (v___x_1177_ == 0)
{
return v_m1_1172_;
}
else
{
uint8_t v___x_1178_; 
v___x_1178_ = lean_nat_dec_le(v___x_1176_, v___x_1176_);
if (v___x_1178_ == 0)
{
if (v___x_1177_ == 0)
{
return v_m1_1172_;
}
else
{
size_t v___x_1179_; size_t v___x_1180_; lean_object* v___x_1181_; 
v___x_1179_ = ((size_t)0ULL);
v___x_1180_ = lean_usize_of_nat(v___x_1176_);
v___x_1181_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___redArg(v_entries_1174_, v___x_1179_, v___x_1180_, v_m1_1172_);
return v___x_1181_;
}
}
else
{
size_t v___x_1182_; size_t v___x_1183_; lean_object* v___x_1184_; 
v___x_1182_ = ((size_t)0ULL);
v___x_1183_ = lean_usize_of_nat(v___x_1176_);
v___x_1184_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___redArg(v_entries_1174_, v___x_1182_, v___x_1183_, v_m1_1172_);
return v___x_1184_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0___redArg___boxed(lean_object* v_m1_1185_, lean_object* v_m2_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0___redArg(v_m1_1185_, v_m2_1186_);
lean_dec_ref(v_m2_1186_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_merge(lean_object* v_headers1_1188_, lean_object* v_headers2_1189_){
_start:
{
lean_object* v___x_1190_; 
v___x_1190_ = l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0___redArg(v_headers1_1188_, v_headers2_1189_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_merge___boxed(lean_object* v_headers1_1191_, lean_object* v_headers2_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l_Std_Http_Headers_merge(v_headers1_1191_, v_headers2_1192_);
lean_dec_ref(v_headers2_1192_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0(lean_object* v_00_u03b2_1194_, lean_object* v_inst_1195_, lean_object* v_inst_1196_, lean_object* v_m1_1197_, lean_object* v_m2_1198_){
_start:
{
lean_object* v___x_1199_; 
v___x_1199_ = l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0___redArg(v_m1_1197_, v_m2_1198_);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0___boxed(lean_object* v_00_u03b2_1200_, lean_object* v_inst_1201_, lean_object* v_inst_1202_, lean_object* v_m1_1203_, lean_object* v_m2_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0(v_00_u03b2_1200_, v_inst_1201_, v_inst_1202_, v_m1_1203_, v_m2_1204_);
lean_dec_ref(v_m2_1204_);
return v_res_1205_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0(lean_object* v_00_u03b2_1206_, lean_object* v_as_1207_, size_t v_i_1208_, size_t v_stop_1209_, lean_object* v_b_1210_){
_start:
{
lean_object* v___x_1211_; 
v___x_1211_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___redArg(v_as_1207_, v_i_1208_, v_stop_1209_, v_b_1210_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1212_, lean_object* v_as_1213_, lean_object* v_i_1214_, lean_object* v_stop_1215_, lean_object* v_b_1216_){
_start:
{
size_t v_i_boxed_1217_; size_t v_stop_boxed_1218_; lean_object* v_res_1219_; 
v_i_boxed_1217_ = lean_unbox_usize(v_i_1214_);
lean_dec(v_i_1214_);
v_stop_boxed_1218_ = lean_unbox_usize(v_stop_1215_);
lean_dec(v_stop_1215_);
v_res_1219_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0(v_00_u03b2_1212_, v_as_1213_, v_i_boxed_1217_, v_stop_boxed_1218_, v_b_1216_);
lean_dec_ref(v_as_1213_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toList___at___00Std_Http_Headers_toList_spec__0___redArg(lean_object* v_map_1220_){
_start:
{
lean_object* v_entries_1221_; lean_object* v___x_1222_; 
v_entries_1221_ = lean_ctor_get(v_map_1220_, 0);
lean_inc_ref(v_entries_1221_);
lean_dec_ref(v_map_1220_);
v___x_1222_ = lean_array_to_list(v_entries_1221_);
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toList___at___00Std_Http_Headers_toList_spec__0(lean_object* v_00_u03b2_1223_, lean_object* v_map_1224_){
_start:
{
lean_object* v___x_1225_; 
v___x_1225_ = l_Std_Internal_IndexMultiMap_toList___at___00Std_Http_Headers_toList_spec__0___redArg(v_map_1224_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_toList(lean_object* v_headers_1226_){
_start:
{
lean_object* v___x_1227_; 
v___x_1227_ = l_Std_Internal_IndexMultiMap_toList___at___00Std_Http_Headers_toList_spec__0___redArg(v_headers_1226_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_toArray(lean_object* v_headers_1228_){
_start:
{
lean_object* v_entries_1229_; 
v_entries_1229_ = lean_ctor_get(v_headers_1228_, 0);
lean_inc_ref(v_entries_1229_);
return v_entries_1229_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_toArray___boxed(lean_object* v_headers_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l_Std_Http_Headers_toArray(v_headers_1230_);
lean_dec_ref(v_headers_1230_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___redArg(lean_object* v_f_1232_, lean_object* v_as_1233_, size_t v_i_1234_, size_t v_stop_1235_, lean_object* v_b_1236_){
_start:
{
uint8_t v___x_1237_; 
v___x_1237_ = lean_usize_dec_eq(v_i_1234_, v_stop_1235_);
if (v___x_1237_ == 0)
{
lean_object* v___x_1238_; lean_object* v_fst_1239_; lean_object* v_snd_1240_; lean_object* v___x_1241_; size_t v___x_1242_; size_t v___x_1243_; 
v___x_1238_ = lean_array_uget_borrowed(v_as_1233_, v_i_1234_);
v_fst_1239_ = lean_ctor_get(v___x_1238_, 0);
v_snd_1240_ = lean_ctor_get(v___x_1238_, 1);
lean_inc(v_f_1232_);
lean_inc(v_snd_1240_);
lean_inc(v_fst_1239_);
v___x_1241_ = lean_apply_3(v_f_1232_, v_b_1236_, v_fst_1239_, v_snd_1240_);
v___x_1242_ = ((size_t)1ULL);
v___x_1243_ = lean_usize_add(v_i_1234_, v___x_1242_);
v_i_1234_ = v___x_1243_;
v_b_1236_ = v___x_1241_;
goto _start;
}
else
{
lean_dec(v_f_1232_);
return v_b_1236_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___redArg___boxed(lean_object* v_f_1245_, lean_object* v_as_1246_, lean_object* v_i_1247_, lean_object* v_stop_1248_, lean_object* v_b_1249_){
_start:
{
size_t v_i_boxed_1250_; size_t v_stop_boxed_1251_; lean_object* v_res_1252_; 
v_i_boxed_1250_ = lean_unbox_usize(v_i_1247_);
lean_dec(v_i_1247_);
v_stop_boxed_1251_ = lean_unbox_usize(v_stop_1248_);
lean_dec(v_stop_1248_);
v_res_1252_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___redArg(v_f_1245_, v_as_1246_, v_i_boxed_1250_, v_stop_boxed_1251_, v_b_1249_);
lean_dec_ref(v_as_1246_);
return v_res_1252_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_fold___redArg(lean_object* v_headers_1253_, lean_object* v_init_1254_, lean_object* v_f_1255_){
_start:
{
lean_object* v_entries_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; uint8_t v___x_1259_; 
v_entries_1256_ = lean_ctor_get(v_headers_1253_, 0);
v___x_1257_ = lean_unsigned_to_nat(0u);
v___x_1258_ = lean_array_get_size(v_entries_1256_);
v___x_1259_ = lean_nat_dec_lt(v___x_1257_, v___x_1258_);
if (v___x_1259_ == 0)
{
lean_dec(v_f_1255_);
return v_init_1254_;
}
else
{
uint8_t v___x_1260_; 
v___x_1260_ = lean_nat_dec_le(v___x_1258_, v___x_1258_);
if (v___x_1260_ == 0)
{
if (v___x_1259_ == 0)
{
lean_dec(v_f_1255_);
return v_init_1254_;
}
else
{
size_t v___x_1261_; size_t v___x_1262_; lean_object* v___x_1263_; 
v___x_1261_ = ((size_t)0ULL);
v___x_1262_ = lean_usize_of_nat(v___x_1258_);
v___x_1263_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___redArg(v_f_1255_, v_entries_1256_, v___x_1261_, v___x_1262_, v_init_1254_);
return v___x_1263_;
}
}
else
{
size_t v___x_1264_; size_t v___x_1265_; lean_object* v___x_1266_; 
v___x_1264_ = ((size_t)0ULL);
v___x_1265_ = lean_usize_of_nat(v___x_1258_);
v___x_1266_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___redArg(v_f_1255_, v_entries_1256_, v___x_1264_, v___x_1265_, v_init_1254_);
return v___x_1266_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_fold___redArg___boxed(lean_object* v_headers_1267_, lean_object* v_init_1268_, lean_object* v_f_1269_){
_start:
{
lean_object* v_res_1270_; 
v_res_1270_ = l_Std_Http_Headers_fold___redArg(v_headers_1267_, v_init_1268_, v_f_1269_);
lean_dec_ref(v_headers_1267_);
return v_res_1270_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_fold(lean_object* v_00_u03b1_1271_, lean_object* v_headers_1272_, lean_object* v_init_1273_, lean_object* v_f_1274_){
_start:
{
lean_object* v___x_1275_; 
v___x_1275_ = l_Std_Http_Headers_fold___redArg(v_headers_1272_, v_init_1273_, v_f_1274_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_fold___boxed(lean_object* v_00_u03b1_1276_, lean_object* v_headers_1277_, lean_object* v_init_1278_, lean_object* v_f_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l_Std_Http_Headers_fold(v_00_u03b1_1276_, v_headers_1277_, v_init_1278_, v_f_1279_);
lean_dec_ref(v_headers_1277_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0(lean_object* v_00_u03b1_1281_, lean_object* v_f_1282_, lean_object* v_as_1283_, size_t v_i_1284_, size_t v_stop_1285_, lean_object* v_b_1286_){
_start:
{
lean_object* v___x_1287_; 
v___x_1287_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___redArg(v_f_1282_, v_as_1283_, v_i_1284_, v_stop_1285_, v_b_1286_);
return v___x_1287_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___boxed(lean_object* v_00_u03b1_1288_, lean_object* v_f_1289_, lean_object* v_as_1290_, lean_object* v_i_1291_, lean_object* v_stop_1292_, lean_object* v_b_1293_){
_start:
{
size_t v_i_boxed_1294_; size_t v_stop_boxed_1295_; lean_object* v_res_1296_; 
v_i_boxed_1294_ = lean_unbox_usize(v_i_1291_);
lean_dec(v_i_1291_);
v_stop_boxed_1295_ = lean_unbox_usize(v_stop_1292_);
lean_dec(v_stop_1292_);
v_res_1296_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0(v_00_u03b1_1288_, v_f_1289_, v_as_1290_, v_i_boxed_1294_, v_stop_boxed_1295_, v_b_1293_);
lean_dec_ref(v_as_1290_);
return v_res_1296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Headers_mapValues_spec__0(lean_object* v_f_1297_, size_t v_sz_1298_, size_t v_i_1299_, lean_object* v_bs_1300_){
_start:
{
uint8_t v___x_1301_; 
v___x_1301_ = lean_usize_dec_lt(v_i_1299_, v_sz_1298_);
if (v___x_1301_ == 0)
{
lean_dec_ref(v_f_1297_);
return v_bs_1300_;
}
else
{
lean_object* v_v_1302_; lean_object* v_fst_1303_; lean_object* v_snd_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1318_; 
v_v_1302_ = lean_array_uget(v_bs_1300_, v_i_1299_);
v_fst_1303_ = lean_ctor_get(v_v_1302_, 0);
v_snd_1304_ = lean_ctor_get(v_v_1302_, 1);
v_isSharedCheck_1318_ = !lean_is_exclusive(v_v_1302_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1306_ = v_v_1302_;
v_isShared_1307_ = v_isSharedCheck_1318_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_snd_1304_);
lean_inc(v_fst_1303_);
lean_dec(v_v_1302_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1318_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1308_; lean_object* v_bs_x27_1309_; lean_object* v___x_1310_; lean_object* v___x_1312_; 
v___x_1308_ = lean_unsigned_to_nat(0u);
v_bs_x27_1309_ = lean_array_uset(v_bs_1300_, v_i_1299_, v___x_1308_);
lean_inc_ref(v_f_1297_);
lean_inc(v_fst_1303_);
v___x_1310_ = lean_apply_2(v_f_1297_, v_fst_1303_, v_snd_1304_);
if (v_isShared_1307_ == 0)
{
lean_ctor_set(v___x_1306_, 1, v___x_1310_);
v___x_1312_ = v___x_1306_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_fst_1303_);
lean_ctor_set(v_reuseFailAlloc_1317_, 1, v___x_1310_);
v___x_1312_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
size_t v___x_1313_; size_t v___x_1314_; lean_object* v___x_1315_; 
v___x_1313_ = ((size_t)1ULL);
v___x_1314_ = lean_usize_add(v_i_1299_, v___x_1313_);
v___x_1315_ = lean_array_uset(v_bs_x27_1309_, v_i_1299_, v___x_1312_);
v_i_1299_ = v___x_1314_;
v_bs_1300_ = v___x_1315_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Headers_mapValues_spec__0___boxed(lean_object* v_f_1319_, lean_object* v_sz_1320_, lean_object* v_i_1321_, lean_object* v_bs_1322_){
_start:
{
size_t v_sz_boxed_1323_; size_t v_i_boxed_1324_; lean_object* v_res_1325_; 
v_sz_boxed_1323_ = lean_unbox_usize(v_sz_1320_);
lean_dec(v_sz_1320_);
v_i_boxed_1324_ = lean_unbox_usize(v_i_1321_);
lean_dec(v_i_1321_);
v_res_1325_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Headers_mapValues_spec__0(v_f_1319_, v_sz_boxed_1323_, v_i_boxed_1324_, v_bs_1322_);
return v_res_1325_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_mapValues_spec__1(lean_object* v_as_1326_, size_t v_i_1327_, size_t v_stop_1328_, lean_object* v_b_1329_){
_start:
{
uint8_t v___x_1330_; 
v___x_1330_ = lean_usize_dec_eq(v_i_1327_, v_stop_1328_);
if (v___x_1330_ == 0)
{
lean_object* v___x_1331_; lean_object* v_fst_1332_; lean_object* v_entries_1333_; lean_object* v_indexes_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1347_; 
v___x_1331_ = lean_array_uget_borrowed(v_as_1326_, v_i_1327_);
v_fst_1332_ = lean_ctor_get(v___x_1331_, 0);
v_entries_1333_ = lean_ctor_get(v_b_1329_, 0);
v_indexes_1334_ = lean_ctor_get(v_b_1329_, 1);
v_isSharedCheck_1347_ = !lean_is_exclusive(v_b_1329_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1336_ = v_b_1329_;
v_isShared_1337_ = v_isSharedCheck_1347_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_indexes_1334_);
lean_inc(v_entries_1333_);
lean_dec(v_b_1329_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1347_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v_i_1338_; lean_object* v_entries_1339_; lean_object* v_indexes_1340_; lean_object* v___x_1342_; 
v_i_1338_ = lean_array_get_size(v_entries_1333_);
lean_inc(v___x_1331_);
v_entries_1339_ = lean_array_push(v_entries_1333_, v___x_1331_);
lean_inc(v_fst_1332_);
v_indexes_1340_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0(v_i_1338_, v_indexes_1334_, v_fst_1332_);
if (v_isShared_1337_ == 0)
{
lean_ctor_set(v___x_1336_, 1, v_indexes_1340_);
lean_ctor_set(v___x_1336_, 0, v_entries_1339_);
v___x_1342_ = v___x_1336_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_entries_1339_);
lean_ctor_set(v_reuseFailAlloc_1346_, 1, v_indexes_1340_);
v___x_1342_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
size_t v___x_1343_; size_t v___x_1344_; 
v___x_1343_ = ((size_t)1ULL);
v___x_1344_ = lean_usize_add(v_i_1327_, v___x_1343_);
v_i_1327_ = v___x_1344_;
v_b_1329_ = v___x_1342_;
goto _start;
}
}
}
else
{
return v_b_1329_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_mapValues_spec__1___boxed(lean_object* v_as_1348_, lean_object* v_i_1349_, lean_object* v_stop_1350_, lean_object* v_b_1351_){
_start:
{
size_t v_i_boxed_1352_; size_t v_stop_boxed_1353_; lean_object* v_res_1354_; 
v_i_boxed_1352_ = lean_unbox_usize(v_i_1349_);
lean_dec(v_i_1349_);
v_stop_boxed_1353_ = lean_unbox_usize(v_stop_1350_);
lean_dec(v_stop_1350_);
v_res_1354_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_mapValues_spec__1(v_as_1348_, v_i_boxed_1352_, v_stop_boxed_1353_, v_b_1351_);
lean_dec_ref(v_as_1348_);
return v_res_1354_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_mapValues(lean_object* v_headers_1355_, lean_object* v_f_1356_){
_start:
{
lean_object* v_entries_1357_; size_t v_sz_1358_; size_t v___x_1359_; lean_object* v_pairs_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; uint8_t v___x_1364_; 
v_entries_1357_ = lean_ctor_get(v_headers_1355_, 0);
lean_inc_ref(v_entries_1357_);
lean_dec_ref(v_headers_1355_);
v_sz_1358_ = lean_array_size(v_entries_1357_);
v___x_1359_ = ((size_t)0ULL);
v_pairs_1360_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Headers_mapValues_spec__0(v_f_1356_, v_sz_1358_, v___x_1359_, v_entries_1357_);
v___x_1361_ = lean_obj_once(&l_Std_Http_Headers_empty___closed__0, &l_Std_Http_Headers_empty___closed__0_once, _init_l_Std_Http_Headers_empty___closed__0);
v___x_1362_ = lean_unsigned_to_nat(0u);
v___x_1363_ = lean_array_get_size(v_pairs_1360_);
v___x_1364_ = lean_nat_dec_lt(v___x_1362_, v___x_1363_);
if (v___x_1364_ == 0)
{
lean_dec_ref(v_pairs_1360_);
return v___x_1361_;
}
else
{
uint8_t v___x_1365_; 
v___x_1365_ = lean_nat_dec_le(v___x_1363_, v___x_1363_);
if (v___x_1365_ == 0)
{
if (v___x_1364_ == 0)
{
lean_dec_ref(v_pairs_1360_);
return v___x_1361_;
}
else
{
size_t v___x_1366_; lean_object* v___x_1367_; 
v___x_1366_ = lean_usize_of_nat(v___x_1363_);
v___x_1367_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_mapValues_spec__1(v_pairs_1360_, v___x_1359_, v___x_1366_, v___x_1361_);
lean_dec_ref(v_pairs_1360_);
return v___x_1367_;
}
}
else
{
size_t v___x_1368_; lean_object* v___x_1369_; 
v___x_1368_ = lean_usize_of_nat(v___x_1363_);
v___x_1369_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_mapValues_spec__1(v_pairs_1360_, v___x_1359_, v___x_1368_, v___x_1361_);
lean_dec_ref(v_pairs_1360_);
return v___x_1369_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0_spec__0(lean_object* v_f_1370_, lean_object* v_as_1371_, size_t v_i_1372_, size_t v_stop_1373_, lean_object* v_b_1374_){
_start:
{
lean_object* v___y_1376_; uint8_t v___x_1380_; 
v___x_1380_ = lean_usize_dec_eq(v_i_1372_, v_stop_1373_);
if (v___x_1380_ == 0)
{
lean_object* v___x_1381_; lean_object* v_fst_1382_; lean_object* v_snd_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1393_; 
v___x_1381_ = lean_array_uget(v_as_1371_, v_i_1372_);
v_fst_1382_ = lean_ctor_get(v___x_1381_, 0);
v_snd_1383_ = lean_ctor_get(v___x_1381_, 1);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1385_ = v___x_1381_;
v_isShared_1386_ = v_isSharedCheck_1393_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_snd_1383_);
lean_inc(v_fst_1382_);
lean_dec(v___x_1381_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1393_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1387_; 
lean_inc_ref(v_f_1370_);
lean_inc(v_fst_1382_);
v___x_1387_ = lean_apply_2(v_f_1370_, v_fst_1382_, v_snd_1383_);
if (lean_obj_tag(v___x_1387_) == 0)
{
lean_del_object(v___x_1385_);
lean_dec(v_fst_1382_);
v___y_1376_ = v_b_1374_;
goto v___jp_1375_;
}
else
{
lean_object* v_val_1388_; lean_object* v___x_1390_; 
v_val_1388_ = lean_ctor_get(v___x_1387_, 0);
lean_inc(v_val_1388_);
lean_dec_ref(v___x_1387_);
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 1, v_val_1388_);
v___x_1390_ = v___x_1385_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_fst_1382_);
lean_ctor_set(v_reuseFailAlloc_1392_, 1, v_val_1388_);
v___x_1390_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
lean_object* v___x_1391_; 
v___x_1391_ = lean_array_push(v_b_1374_, v___x_1390_);
v___y_1376_ = v___x_1391_;
goto v___jp_1375_;
}
}
}
}
else
{
lean_dec_ref(v_f_1370_);
return v_b_1374_;
}
v___jp_1375_:
{
size_t v___x_1377_; size_t v___x_1378_; 
v___x_1377_ = ((size_t)1ULL);
v___x_1378_ = lean_usize_add(v_i_1372_, v___x_1377_);
v_i_1372_ = v___x_1378_;
v_b_1374_ = v___y_1376_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0_spec__0___boxed(lean_object* v_f_1394_, lean_object* v_as_1395_, lean_object* v_i_1396_, lean_object* v_stop_1397_, lean_object* v_b_1398_){
_start:
{
size_t v_i_boxed_1399_; size_t v_stop_boxed_1400_; lean_object* v_res_1401_; 
v_i_boxed_1399_ = lean_unbox_usize(v_i_1396_);
lean_dec(v_i_1396_);
v_stop_boxed_1400_ = lean_unbox_usize(v_stop_1397_);
lean_dec(v_stop_1397_);
v_res_1401_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0_spec__0(v_f_1394_, v_as_1395_, v_i_boxed_1399_, v_stop_boxed_1400_, v_b_1398_);
lean_dec_ref(v_as_1395_);
return v_res_1401_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0(lean_object* v_f_1402_, lean_object* v_as_1403_, lean_object* v_start_1404_, lean_object* v_stop_1405_){
_start:
{
lean_object* v___x_1406_; uint8_t v___x_1407_; 
v___x_1406_ = ((lean_object*)(l_Std_Http_instInhabitedHeaders_default___closed__0));
v___x_1407_ = lean_nat_dec_lt(v_start_1404_, v_stop_1405_);
if (v___x_1407_ == 0)
{
lean_dec_ref(v_f_1402_);
return v___x_1406_;
}
else
{
lean_object* v___x_1408_; uint8_t v___x_1409_; 
v___x_1408_ = lean_array_get_size(v_as_1403_);
v___x_1409_ = lean_nat_dec_le(v_stop_1405_, v___x_1408_);
if (v___x_1409_ == 0)
{
uint8_t v___x_1410_; 
v___x_1410_ = lean_nat_dec_lt(v_start_1404_, v___x_1408_);
if (v___x_1410_ == 0)
{
lean_dec_ref(v_f_1402_);
return v___x_1406_;
}
else
{
size_t v___x_1411_; size_t v___x_1412_; lean_object* v___x_1413_; 
v___x_1411_ = lean_usize_of_nat(v_start_1404_);
v___x_1412_ = lean_usize_of_nat(v___x_1408_);
v___x_1413_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0_spec__0(v_f_1402_, v_as_1403_, v___x_1411_, v___x_1412_, v___x_1406_);
return v___x_1413_;
}
}
else
{
size_t v___x_1414_; size_t v___x_1415_; lean_object* v___x_1416_; 
v___x_1414_ = lean_usize_of_nat(v_start_1404_);
v___x_1415_ = lean_usize_of_nat(v_stop_1405_);
v___x_1416_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0_spec__0(v_f_1402_, v_as_1403_, v___x_1414_, v___x_1415_, v___x_1406_);
return v___x_1416_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0___boxed(lean_object* v_f_1417_, lean_object* v_as_1418_, lean_object* v_start_1419_, lean_object* v_stop_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l_Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0(v_f_1417_, v_as_1418_, v_start_1419_, v_stop_1420_);
lean_dec(v_stop_1420_);
lean_dec(v_start_1419_);
lean_dec_ref(v_as_1418_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_filterMap(lean_object* v_headers_1422_, lean_object* v_f_1423_){
_start:
{
lean_object* v_entries_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v_pairs_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; uint8_t v___x_1430_; 
v_entries_1424_ = lean_ctor_get(v_headers_1422_, 0);
v___x_1425_ = lean_unsigned_to_nat(0u);
v___x_1426_ = lean_array_get_size(v_entries_1424_);
v_pairs_1427_ = l_Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0(v_f_1423_, v_entries_1424_, v___x_1425_, v___x_1426_);
v___x_1428_ = lean_obj_once(&l_Std_Http_Headers_empty___closed__0, &l_Std_Http_Headers_empty___closed__0_once, _init_l_Std_Http_Headers_empty___closed__0);
v___x_1429_ = lean_array_get_size(v_pairs_1427_);
v___x_1430_ = lean_nat_dec_lt(v___x_1425_, v___x_1429_);
if (v___x_1430_ == 0)
{
lean_dec_ref(v_pairs_1427_);
return v___x_1428_;
}
else
{
uint8_t v___x_1431_; 
v___x_1431_ = lean_nat_dec_le(v___x_1429_, v___x_1429_);
if (v___x_1431_ == 0)
{
if (v___x_1430_ == 0)
{
lean_dec_ref(v_pairs_1427_);
return v___x_1428_;
}
else
{
size_t v___x_1432_; size_t v___x_1433_; lean_object* v___x_1434_; 
v___x_1432_ = ((size_t)0ULL);
v___x_1433_ = lean_usize_of_nat(v___x_1429_);
v___x_1434_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_mapValues_spec__1(v_pairs_1427_, v___x_1432_, v___x_1433_, v___x_1428_);
lean_dec_ref(v_pairs_1427_);
return v___x_1434_;
}
}
else
{
size_t v___x_1435_; size_t v___x_1436_; lean_object* v___x_1437_; 
v___x_1435_ = ((size_t)0ULL);
v___x_1436_ = lean_usize_of_nat(v___x_1429_);
v___x_1437_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_mapValues_spec__1(v_pairs_1427_, v___x_1435_, v___x_1436_, v___x_1428_);
lean_dec_ref(v_pairs_1427_);
return v___x_1437_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_filterMap___boxed(lean_object* v_headers_1438_, lean_object* v_f_1439_){
_start:
{
lean_object* v_res_1440_; 
v_res_1440_ = l_Std_Http_Headers_filterMap(v_headers_1438_, v_f_1439_);
lean_dec_ref(v_headers_1438_);
return v_res_1440_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_filter___lam__0(lean_object* v_f_1441_, lean_object* v_k_1442_, lean_object* v_v_1443_){
_start:
{
lean_object* v___x_1444_; uint8_t v___x_1445_; 
lean_inc_ref(v_v_1443_);
v___x_1444_ = lean_apply_2(v_f_1441_, v_k_1442_, v_v_1443_);
v___x_1445_ = lean_unbox(v___x_1444_);
if (v___x_1445_ == 0)
{
lean_object* v___x_1446_; 
lean_dec_ref(v_v_1443_);
v___x_1446_ = lean_box(0);
return v___x_1446_;
}
else
{
lean_object* v___x_1447_; 
v___x_1447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1447_, 0, v_v_1443_);
return v___x_1447_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_filter(lean_object* v_headers_1448_, lean_object* v_f_1449_){
_start:
{
lean_object* v___f_1450_; lean_object* v___x_1451_; 
v___f_1450_ = lean_alloc_closure((void*)(l_Std_Http_Headers_filter___lam__0), 3, 1);
lean_closure_set(v___f_1450_, 0, v_f_1449_);
v___x_1451_ = l_Std_Http_Headers_filterMap(v_headers_1448_, v___f_1450_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_filter___boxed(lean_object* v_headers_1452_, lean_object* v_f_1453_){
_start:
{
lean_object* v_res_1454_; 
v_res_1454_ = l_Std_Http_Headers_filter(v_headers_1452_, v_f_1453_);
lean_dec_ref(v_headers_1452_);
return v_res_1454_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_update_spec__0(lean_object* v_name_1455_, lean_object* v_f_1456_, lean_object* v_as_1457_, size_t v_i_1458_, size_t v_stop_1459_, lean_object* v_b_1460_){
_start:
{
uint8_t v___x_1461_; 
v___x_1461_ = lean_usize_dec_eq(v_i_1458_, v_stop_1459_);
if (v___x_1461_ == 0)
{
lean_object* v___x_1462_; lean_object* v_fst_1463_; lean_object* v_snd_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1490_; 
v___x_1462_ = lean_array_uget(v_as_1457_, v_i_1458_);
v_fst_1463_ = lean_ctor_get(v___x_1462_, 0);
v_snd_1464_ = lean_ctor_get(v___x_1462_, 1);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1466_ = v___x_1462_;
v_isShared_1467_ = v_isSharedCheck_1490_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_snd_1464_);
lean_inc(v_fst_1463_);
lean_dec(v___x_1462_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1490_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___y_1469_; uint8_t v___x_1488_; 
v___x_1488_ = lean_string_dec_eq(v_fst_1463_, v_name_1455_);
if (v___x_1488_ == 0)
{
v___y_1469_ = v_snd_1464_;
goto v___jp_1468_;
}
else
{
lean_object* v___x_1489_; 
lean_inc_ref(v_f_1456_);
v___x_1489_ = lean_apply_1(v_f_1456_, v_snd_1464_);
v___y_1469_ = v___x_1489_;
goto v___jp_1468_;
}
v___jp_1468_:
{
lean_object* v_entries_1470_; lean_object* v_indexes_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1487_; 
v_entries_1470_ = lean_ctor_get(v_b_1460_, 0);
v_indexes_1471_ = lean_ctor_get(v_b_1460_, 1);
v_isSharedCheck_1487_ = !lean_is_exclusive(v_b_1460_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1473_ = v_b_1460_;
v_isShared_1474_ = v_isSharedCheck_1487_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_indexes_1471_);
lean_inc(v_entries_1470_);
lean_dec(v_b_1460_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1487_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v_i_1475_; lean_object* v___x_1477_; 
v_i_1475_ = lean_array_get_size(v_entries_1470_);
lean_inc(v_fst_1463_);
if (v_isShared_1467_ == 0)
{
lean_ctor_set(v___x_1466_, 1, v___y_1469_);
v___x_1477_ = v___x_1466_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_fst_1463_);
lean_ctor_set(v_reuseFailAlloc_1486_, 1, v___y_1469_);
v___x_1477_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
lean_object* v_entries_1478_; lean_object* v_indexes_1479_; lean_object* v___x_1481_; 
v_entries_1478_ = lean_array_push(v_entries_1470_, v___x_1477_);
v_indexes_1479_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0(v_i_1475_, v_indexes_1471_, v_fst_1463_);
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 1, v_indexes_1479_);
lean_ctor_set(v___x_1473_, 0, v_entries_1478_);
v___x_1481_ = v___x_1473_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_entries_1478_);
lean_ctor_set(v_reuseFailAlloc_1485_, 1, v_indexes_1479_);
v___x_1481_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
size_t v___x_1482_; size_t v___x_1483_; 
v___x_1482_ = ((size_t)1ULL);
v___x_1483_ = lean_usize_add(v_i_1458_, v___x_1482_);
v_i_1458_ = v___x_1483_;
v_b_1460_ = v___x_1481_;
goto _start;
}
}
}
}
}
}
else
{
lean_dec_ref(v_f_1456_);
return v_b_1460_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_update_spec__0___boxed(lean_object* v_name_1491_, lean_object* v_f_1492_, lean_object* v_as_1493_, lean_object* v_i_1494_, lean_object* v_stop_1495_, lean_object* v_b_1496_){
_start:
{
size_t v_i_boxed_1497_; size_t v_stop_boxed_1498_; lean_object* v_res_1499_; 
v_i_boxed_1497_ = lean_unbox_usize(v_i_1494_);
lean_dec(v_i_1494_);
v_stop_boxed_1498_ = lean_unbox_usize(v_stop_1495_);
lean_dec(v_stop_1495_);
v_res_1499_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_update_spec__0(v_name_1491_, v_f_1492_, v_as_1493_, v_i_boxed_1497_, v_stop_boxed_1498_, v_b_1496_);
lean_dec_ref(v_as_1493_);
lean_dec_ref(v_name_1491_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_update(lean_object* v_headers_1500_, lean_object* v_name_1501_, lean_object* v_f_1502_){
_start:
{
lean_object* v___f_1503_; lean_object* v___f_1504_; uint8_t v___x_1505_; 
v___f_1503_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_1504_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
lean_inc_ref(v_name_1501_);
v___x_1505_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_1503_, v___f_1504_, v_name_1501_, v_headers_1500_);
if (v___x_1505_ == 0)
{
lean_dec_ref(v_f_1502_);
lean_dec_ref(v_name_1501_);
lean_inc_ref(v_headers_1500_);
return v_headers_1500_;
}
else
{
lean_object* v_entries_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; uint8_t v___x_1510_; 
v_entries_1506_ = lean_ctor_get(v_headers_1500_, 0);
v___x_1507_ = lean_obj_once(&l_Std_Http_Headers_empty___closed__0, &l_Std_Http_Headers_empty___closed__0_once, _init_l_Std_Http_Headers_empty___closed__0);
v___x_1508_ = lean_unsigned_to_nat(0u);
v___x_1509_ = lean_array_get_size(v_entries_1506_);
v___x_1510_ = lean_nat_dec_lt(v___x_1508_, v___x_1509_);
if (v___x_1510_ == 0)
{
lean_dec_ref(v_f_1502_);
lean_dec_ref(v_name_1501_);
return v___x_1507_;
}
else
{
uint8_t v___x_1511_; 
v___x_1511_ = lean_nat_dec_le(v___x_1509_, v___x_1509_);
if (v___x_1511_ == 0)
{
if (v___x_1510_ == 0)
{
lean_dec_ref(v_f_1502_);
lean_dec_ref(v_name_1501_);
return v___x_1507_;
}
else
{
size_t v___x_1512_; size_t v___x_1513_; lean_object* v___x_1514_; 
v___x_1512_ = ((size_t)0ULL);
v___x_1513_ = lean_usize_of_nat(v___x_1509_);
v___x_1514_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_update_spec__0(v_name_1501_, v_f_1502_, v_entries_1506_, v___x_1512_, v___x_1513_, v___x_1507_);
lean_dec_ref(v_name_1501_);
return v___x_1514_;
}
}
else
{
size_t v___x_1515_; size_t v___x_1516_; lean_object* v___x_1517_; 
v___x_1515_ = ((size_t)0ULL);
v___x_1516_ = lean_usize_of_nat(v___x_1509_);
v___x_1517_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_update_spec__0(v_name_1501_, v_f_1502_, v_entries_1506_, v___x_1515_, v___x_1516_, v___x_1507_);
lean_dec_ref(v_name_1501_);
return v___x_1517_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_update___boxed(lean_object* v_headers_1518_, lean_object* v_name_1519_, lean_object* v_f_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l_Std_Http_Headers_update(v_headers_1518_, v_name_1519_, v_f_1520_);
lean_dec_ref(v_headers_1518_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_replaceLast(lean_object* v_headers_1522_, lean_object* v_name_1523_, lean_object* v_value_1524_){
_start:
{
lean_object* v___f_1525_; lean_object* v___f_1526_; uint8_t v___x_1527_; 
v___f_1525_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_1526_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
lean_inc_ref(v_name_1523_);
v___x_1527_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_1525_, v___f_1526_, v_name_1523_, v_headers_1522_);
if (v___x_1527_ == 0)
{
lean_dec_ref(v_value_1524_);
lean_dec_ref(v_name_1523_);
return v_headers_1522_;
}
else
{
lean_object* v_entries_1528_; lean_object* v_indexes_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1543_; 
v_entries_1528_ = lean_ctor_get(v_headers_1522_, 0);
v_indexes_1529_ = lean_ctor_get(v_headers_1522_, 1);
v_isSharedCheck_1543_ = !lean_is_exclusive(v_headers_1522_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1531_ = v_headers_1522_;
v_isShared_1532_ = v_isSharedCheck_1543_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_indexes_1529_);
lean_inc(v_entries_1528_);
lean_dec(v_headers_1522_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1543_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v_idxs_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v_lastIdx_1537_; lean_object* v___x_1538_; lean_object* v_entries_1539_; lean_object* v___x_1541_; 
lean_inc_ref(v_name_1523_);
v_idxs_1533_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v___f_1525_, v___f_1526_, v_indexes_1529_, v_name_1523_);
v___x_1534_ = lean_array_get_size(v_idxs_1533_);
v___x_1535_ = lean_unsigned_to_nat(1u);
v___x_1536_ = lean_nat_sub(v___x_1534_, v___x_1535_);
v_lastIdx_1537_ = lean_array_fget(v_idxs_1533_, v___x_1536_);
lean_dec(v___x_1536_);
lean_dec(v_idxs_1533_);
v___x_1538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1538_, 0, v_name_1523_);
lean_ctor_set(v___x_1538_, 1, v_value_1524_);
v_entries_1539_ = lean_array_fset(v_entries_1528_, v_lastIdx_1537_, v___x_1538_);
lean_dec(v_lastIdx_1537_);
if (v_isShared_1532_ == 0)
{
lean_ctor_set(v___x_1531_, 0, v_entries_1539_);
v___x_1541_ = v___x_1531_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v_entries_1539_);
lean_ctor_set(v_reuseFailAlloc_1542_, 1, v_indexes_1529_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
return v___x_1541_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instToString___lam__0(lean_object* v___x_1544_, lean_object* v___x_1545_, lean_object* v___x_1546_, lean_object* v_fst_1547_, lean_object* v___x_1548_, uint32_t v___x_1549_, lean_object* v___x_1550_, lean_object* v_it_1551_, lean_object* v_acc_1552_, lean_object* v_hP_1553_, lean_object* v_recur_1554_){
_start:
{
lean_object* v_it_1556_; lean_object* v_out_1557_; lean_object* v_it_1573_; lean_object* v_startInclusive_1574_; lean_object* v_endExclusive_1575_; 
if (lean_obj_tag(v_it_1551_) == 0)
{
lean_object* v_currPos_1587_; lean_object* v_searcher_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1610_; 
v_currPos_1587_ = lean_ctor_get(v_it_1551_, 0);
v_searcher_1588_ = lean_ctor_get(v_it_1551_, 1);
v_isSharedCheck_1610_ = !lean_is_exclusive(v_it_1551_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1590_ = v_it_1551_;
v_isShared_1591_ = v_isSharedCheck_1610_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_searcher_1588_);
lean_inc(v_currPos_1587_);
lean_dec(v_it_1551_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1610_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
uint8_t v___x_1592_; 
v___x_1592_ = lean_nat_dec_eq(v_searcher_1588_, v___x_1548_);
if (v___x_1592_ == 0)
{
uint32_t v___x_1593_; uint8_t v___x_1594_; 
lean_dec(v___x_1548_);
v___x_1593_ = lean_string_utf8_get_fast(v_fst_1547_, v_searcher_1588_);
v___x_1594_ = lean_uint32_dec_eq(v___x_1593_, v___x_1549_);
if (v___x_1594_ == 0)
{
lean_object* v___x_1595_; lean_object* v___x_1597_; 
v___x_1595_ = lean_string_utf8_next_fast(v_fst_1547_, v_searcher_1588_);
lean_dec(v_searcher_1588_);
if (v_isShared_1591_ == 0)
{
lean_ctor_set(v___x_1590_, 1, v___x_1595_);
v___x_1597_ = v___x_1590_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_currPos_1587_);
lean_ctor_set(v_reuseFailAlloc_1599_, 1, v___x_1595_);
v___x_1597_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
lean_object* v___x_1598_; 
v___x_1598_ = lean_apply_4(v_recur_1554_, v___x_1597_, v_acc_1552_, lean_box(0), lean_box(0));
return v___x_1598_;
}
}
else
{
lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v_slice_1603_; lean_object* v_nextIt_1605_; 
v___x_1600_ = lean_string_utf8_next_fast(v_fst_1547_, v_searcher_1588_);
v___x_1601_ = lean_nat_sub(v___x_1600_, v_searcher_1588_);
v___x_1602_ = lean_nat_add(v_searcher_1588_, v___x_1601_);
lean_dec(v___x_1601_);
v_slice_1603_ = l_String_Slice_subslice_x21(v___x_1550_, v_currPos_1587_, v_searcher_1588_);
lean_inc(v___x_1602_);
if (v_isShared_1591_ == 0)
{
lean_ctor_set(v___x_1590_, 1, v___x_1602_);
lean_ctor_set(v___x_1590_, 0, v___x_1602_);
v_nextIt_1605_ = v___x_1590_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v___x_1602_);
lean_ctor_set(v_reuseFailAlloc_1608_, 1, v___x_1602_);
v_nextIt_1605_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
lean_object* v_startInclusive_1606_; lean_object* v_endExclusive_1607_; 
v_startInclusive_1606_ = lean_ctor_get(v_slice_1603_, 0);
lean_inc(v_startInclusive_1606_);
v_endExclusive_1607_ = lean_ctor_get(v_slice_1603_, 1);
lean_inc(v_endExclusive_1607_);
lean_dec_ref(v_slice_1603_);
v_it_1573_ = v_nextIt_1605_;
v_startInclusive_1574_ = v_startInclusive_1606_;
v_endExclusive_1575_ = v_endExclusive_1607_;
goto v___jp_1572_;
}
}
}
else
{
lean_object* v___x_1609_; 
lean_del_object(v___x_1590_);
lean_dec(v_searcher_1588_);
v___x_1609_ = lean_box(1);
v_it_1573_ = v___x_1609_;
v_startInclusive_1574_ = v_currPos_1587_;
v_endExclusive_1575_ = v___x_1548_;
goto v___jp_1572_;
}
}
}
else
{
lean_dec_ref(v_recur_1554_);
lean_dec(v___x_1548_);
return v_acc_1552_;
}
v___jp_1555_:
{
if (lean_obj_tag(v_acc_1552_) == 0)
{
lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1558_, 0, v_out_1557_);
v___x_1559_ = lean_apply_4(v_recur_1554_, v_it_1556_, v___x_1558_, lean_box(0), lean_box(0));
return v___x_1559_;
}
else
{
lean_object* v_val_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1571_; 
v_val_1560_ = lean_ctor_get(v_acc_1552_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v_acc_1552_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1562_ = v_acc_1552_;
v_isShared_1563_ = v_isSharedCheck_1571_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_val_1560_);
lean_dec(v_acc_1552_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1571_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1568_; 
v___x_1564_ = lean_string_utf8_extract(v___x_1544_, v___x_1545_, v___x_1546_);
v___x_1565_ = lean_string_append(v_val_1560_, v___x_1564_);
lean_dec_ref(v___x_1564_);
v___x_1566_ = lean_string_append(v___x_1565_, v_out_1557_);
lean_dec_ref(v_out_1557_);
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 0, v___x_1566_);
v___x_1568_ = v___x_1562_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v___x_1566_);
v___x_1568_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
lean_object* v___x_1569_; 
v___x_1569_ = lean_apply_4(v_recur_1554_, v_it_1556_, v___x_1568_, lean_box(0), lean_box(0));
return v___x_1569_;
}
}
}
}
v___jp_1572_:
{
lean_object* v___x_1576_; uint32_t v___x_1577_; uint32_t v___x_1578_; uint8_t v___x_1579_; 
v___x_1576_ = lean_string_utf8_extract(v_fst_1547_, v_startInclusive_1574_, v_endExclusive_1575_);
lean_dec(v_endExclusive_1575_);
lean_dec(v_startInclusive_1574_);
v___x_1577_ = lean_string_utf8_get(v___x_1576_, v___x_1545_);
v___x_1578_ = 97;
v___x_1579_ = lean_uint32_dec_le(v___x_1578_, v___x_1577_);
if (v___x_1579_ == 0)
{
lean_object* v___x_1580_; 
v___x_1580_ = lean_string_utf8_set(v___x_1576_, v___x_1545_, v___x_1577_);
v_it_1556_ = v_it_1573_;
v_out_1557_ = v___x_1580_;
goto v___jp_1555_;
}
else
{
uint32_t v___x_1581_; uint8_t v___x_1582_; 
v___x_1581_ = 122;
v___x_1582_ = lean_uint32_dec_le(v___x_1577_, v___x_1581_);
if (v___x_1582_ == 0)
{
lean_object* v___x_1583_; 
v___x_1583_ = lean_string_utf8_set(v___x_1576_, v___x_1545_, v___x_1577_);
v_it_1556_ = v_it_1573_;
v_out_1557_ = v___x_1583_;
goto v___jp_1555_;
}
else
{
uint32_t v___x_1584_; uint32_t v___x_1585_; lean_object* v___x_1586_; 
v___x_1584_ = 4294967264;
v___x_1585_ = lean_uint32_add(v___x_1577_, v___x_1584_);
v___x_1586_ = lean_string_utf8_set(v___x_1576_, v___x_1545_, v___x_1585_);
v_it_1556_ = v_it_1573_;
v_out_1557_ = v___x_1586_;
goto v___jp_1555_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instToString___lam__0___boxed(lean_object* v___x_1611_, lean_object* v___x_1612_, lean_object* v___x_1613_, lean_object* v_fst_1614_, lean_object* v___x_1615_, lean_object* v___x_1616_, lean_object* v___x_1617_, lean_object* v_it_1618_, lean_object* v_acc_1619_, lean_object* v_hP_1620_, lean_object* v_recur_1621_){
_start:
{
uint32_t v___x_1744__boxed_1622_; lean_object* v_res_1623_; 
v___x_1744__boxed_1622_ = lean_unbox_uint32(v___x_1616_);
lean_dec(v___x_1616_);
v_res_1623_ = l_Std_Http_Headers_instToString___lam__0(v___x_1611_, v___x_1612_, v___x_1613_, v_fst_1614_, v___x_1615_, v___x_1744__boxed_1622_, v___x_1617_, v_it_1618_, v_acc_1619_, v_hP_1620_, v_recur_1621_);
lean_dec_ref(v___x_1617_);
lean_dec_ref(v_fst_1614_);
lean_dec(v___x_1613_);
lean_dec(v___x_1612_);
lean_dec_ref(v___x_1611_);
return v_res_1623_;
}
}
static lean_object* _init_l_Std_Http_Headers_instToString___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1627_ = ((lean_object*)(l_Std_Http_Headers_instToString___lam__1___closed__2));
v___x_1628_ = lean_string_utf8_byte_size(v___x_1627_);
return v___x_1628_;
}
}
static lean_object* _init_l_Std_Http_Headers_instToString___lam__1___boxed__const__1(void){
_start:
{
uint32_t v___x_1629_; lean_object* v___x_1630_; 
v___x_1629_ = 45;
v___x_1630_ = lean_box_uint32(v___x_1629_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instToString___lam__1(lean_object* v_x_1631_){
_start:
{
lean_object* v_fst_1632_; lean_object* v_snd_1633_; lean_object* v___y_1635_; lean_object* v___f_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v_it_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___f_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; 
v_fst_1632_ = lean_ctor_get(v_x_1631_, 0);
lean_inc_n(v_fst_1632_, 2);
v_snd_1633_ = lean_ctor_get(v_x_1631_, 1);
lean_inc(v_snd_1633_);
lean_dec_ref(v_x_1631_);
v___f_1639_ = ((lean_object*)(l_Std_Http_Headers_instToString___lam__1___closed__1));
v___x_1640_ = lean_unsigned_to_nat(0u);
v___x_1641_ = lean_string_utf8_byte_size(v_fst_1632_);
v___x_1642_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1642_, 0, v_fst_1632_);
lean_ctor_set(v___x_1642_, 1, v___x_1640_);
lean_ctor_set(v___x_1642_, 2, v___x_1641_);
lean_inc_ref(v___x_1642_);
v_it_1643_ = l_String_Slice_splitToSubslice___redArg(v___x_1642_, v___f_1639_);
v___x_1644_ = ((lean_object*)(l_Std_Http_Headers_instToString___lam__1___closed__2));
v___x_1645_ = lean_obj_once(&l_Std_Http_Headers_instToString___lam__1___closed__3, &l_Std_Http_Headers_instToString___lam__1___closed__3_once, _init_l_Std_Http_Headers_instToString___lam__1___closed__3);
v___x_1646_ = l_Std_Http_Headers_instToString___lam__1___boxed__const__1;
v___f_1647_ = lean_alloc_closure((void*)(l_Std_Http_Headers_instToString___lam__0___boxed), 11, 7);
lean_closure_set(v___f_1647_, 0, v___x_1644_);
lean_closure_set(v___f_1647_, 1, v___x_1640_);
lean_closure_set(v___f_1647_, 2, v___x_1645_);
lean_closure_set(v___f_1647_, 3, v_fst_1632_);
lean_closure_set(v___f_1647_, 4, v___x_1641_);
lean_closure_set(v___f_1647_, 5, v___x_1646_);
lean_closure_set(v___f_1647_, 6, v___x_1642_);
v___x_1648_ = lean_box(0);
v___x_1649_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1647_, v_it_1643_, v___x_1648_, lean_box(0));
if (lean_obj_tag(v___x_1649_) == 0)
{
lean_object* v___x_1650_; 
v___x_1650_ = ((lean_object*)(l_Std_Http_Headers_get_x21___closed__0));
v___y_1635_ = v___x_1650_;
goto v___jp_1634_;
}
else
{
lean_object* v_val_1651_; 
v_val_1651_ = lean_ctor_get(v___x_1649_, 0);
lean_inc(v_val_1651_);
lean_dec_ref(v___x_1649_);
v___y_1635_ = v_val_1651_;
goto v___jp_1634_;
}
v___jp_1634_:
{
lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
v___x_1636_ = ((lean_object*)(l_Std_Http_Headers_instToString___lam__1___closed__0));
v___x_1637_ = lean_string_append(v___y_1635_, v___x_1636_);
v___x_1638_ = lean_string_append(v___x_1637_, v_snd_1633_);
lean_dec(v_snd_1633_);
return v___x_1638_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instToString___lam__2(lean_object* v___f_1653_, lean_object* v_headers_1654_){
_start:
{
lean_object* v_entries_1655_; lean_object* v___x_1656_; size_t v_sz_1657_; size_t v___x_1658_; lean_object* v_pairs_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; 
v_entries_1655_ = lean_ctor_get(v_headers_1654_, 0);
lean_inc_ref(v_entries_1655_);
lean_dec_ref(v_headers_1654_);
v___x_1656_ = ((lean_object*)(l_Std_Http_Headers_getAll___redArg___closed__9));
v_sz_1657_ = lean_array_size(v_entries_1655_);
v___x_1658_ = ((size_t)0ULL);
v_pairs_1659_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1656_, v___f_1653_, v_sz_1657_, v___x_1658_, v_entries_1655_);
v___x_1660_ = ((lean_object*)(l_Std_Http_Headers_instToString___lam__2___closed__0));
v___x_1661_ = lean_array_to_list(v_pairs_1659_);
v___x_1662_ = l_String_intercalate(v___x_1660_, v___x_1661_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instEncodeV11___lam__0(lean_object* v___x_1667_, lean_object* v___x_1668_, lean_object* v___x_1669_, lean_object* v_name_1670_, lean_object* v___x_1671_, uint32_t v___x_1672_, lean_object* v___x_1673_, lean_object* v_it_1674_, lean_object* v_acc_1675_, lean_object* v_hP_1676_, lean_object* v_recur_1677_){
_start:
{
lean_object* v_it_1679_; lean_object* v_out_1680_; lean_object* v_it_1696_; lean_object* v_startInclusive_1697_; lean_object* v_endExclusive_1698_; 
if (lean_obj_tag(v_it_1674_) == 0)
{
lean_object* v_currPos_1710_; lean_object* v_searcher_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1733_; 
v_currPos_1710_ = lean_ctor_get(v_it_1674_, 0);
v_searcher_1711_ = lean_ctor_get(v_it_1674_, 1);
v_isSharedCheck_1733_ = !lean_is_exclusive(v_it_1674_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1713_ = v_it_1674_;
v_isShared_1714_ = v_isSharedCheck_1733_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_searcher_1711_);
lean_inc(v_currPos_1710_);
lean_dec(v_it_1674_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1733_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
uint8_t v___x_1715_; 
v___x_1715_ = lean_nat_dec_eq(v_searcher_1711_, v___x_1671_);
if (v___x_1715_ == 0)
{
uint32_t v___x_1716_; uint8_t v___x_1717_; 
lean_dec(v___x_1671_);
v___x_1716_ = lean_string_utf8_get_fast(v_name_1670_, v_searcher_1711_);
v___x_1717_ = lean_uint32_dec_eq(v___x_1716_, v___x_1672_);
if (v___x_1717_ == 0)
{
lean_object* v___x_1718_; lean_object* v___x_1720_; 
v___x_1718_ = lean_string_utf8_next_fast(v_name_1670_, v_searcher_1711_);
lean_dec(v_searcher_1711_);
if (v_isShared_1714_ == 0)
{
lean_ctor_set(v___x_1713_, 1, v___x_1718_);
v___x_1720_ = v___x_1713_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_currPos_1710_);
lean_ctor_set(v_reuseFailAlloc_1722_, 1, v___x_1718_);
v___x_1720_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
lean_object* v___x_1721_; 
v___x_1721_ = lean_apply_4(v_recur_1677_, v___x_1720_, v_acc_1675_, lean_box(0), lean_box(0));
return v___x_1721_;
}
}
else
{
lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v_slice_1726_; lean_object* v_nextIt_1728_; 
v___x_1723_ = lean_string_utf8_next_fast(v_name_1670_, v_searcher_1711_);
v___x_1724_ = lean_nat_sub(v___x_1723_, v_searcher_1711_);
v___x_1725_ = lean_nat_add(v_searcher_1711_, v___x_1724_);
lean_dec(v___x_1724_);
v_slice_1726_ = l_String_Slice_subslice_x21(v___x_1673_, v_currPos_1710_, v_searcher_1711_);
lean_inc(v___x_1725_);
if (v_isShared_1714_ == 0)
{
lean_ctor_set(v___x_1713_, 1, v___x_1725_);
lean_ctor_set(v___x_1713_, 0, v___x_1725_);
v_nextIt_1728_ = v___x_1713_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v___x_1725_);
lean_ctor_set(v_reuseFailAlloc_1731_, 1, v___x_1725_);
v_nextIt_1728_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
lean_object* v_startInclusive_1729_; lean_object* v_endExclusive_1730_; 
v_startInclusive_1729_ = lean_ctor_get(v_slice_1726_, 0);
lean_inc(v_startInclusive_1729_);
v_endExclusive_1730_ = lean_ctor_get(v_slice_1726_, 1);
lean_inc(v_endExclusive_1730_);
lean_dec_ref(v_slice_1726_);
v_it_1696_ = v_nextIt_1728_;
v_startInclusive_1697_ = v_startInclusive_1729_;
v_endExclusive_1698_ = v_endExclusive_1730_;
goto v___jp_1695_;
}
}
}
else
{
lean_object* v___x_1732_; 
lean_del_object(v___x_1713_);
lean_dec(v_searcher_1711_);
v___x_1732_ = lean_box(1);
v_it_1696_ = v___x_1732_;
v_startInclusive_1697_ = v_currPos_1710_;
v_endExclusive_1698_ = v___x_1671_;
goto v___jp_1695_;
}
}
}
else
{
lean_dec_ref(v_recur_1677_);
lean_dec(v___x_1671_);
return v_acc_1675_;
}
v___jp_1678_:
{
if (lean_obj_tag(v_acc_1675_) == 0)
{
lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1681_, 0, v_out_1680_);
v___x_1682_ = lean_apply_4(v_recur_1677_, v_it_1679_, v___x_1681_, lean_box(0), lean_box(0));
return v___x_1682_;
}
else
{
lean_object* v_val_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1694_; 
v_val_1683_ = lean_ctor_get(v_acc_1675_, 0);
v_isSharedCheck_1694_ = !lean_is_exclusive(v_acc_1675_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1685_ = v_acc_1675_;
v_isShared_1686_ = v_isSharedCheck_1694_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_val_1683_);
lean_dec(v_acc_1675_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1694_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1691_; 
v___x_1687_ = lean_string_utf8_extract(v___x_1667_, v___x_1668_, v___x_1669_);
v___x_1688_ = lean_string_append(v_val_1683_, v___x_1687_);
lean_dec_ref(v___x_1687_);
v___x_1689_ = lean_string_append(v___x_1688_, v_out_1680_);
lean_dec_ref(v_out_1680_);
if (v_isShared_1686_ == 0)
{
lean_ctor_set(v___x_1685_, 0, v___x_1689_);
v___x_1691_ = v___x_1685_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v___x_1689_);
v___x_1691_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
lean_object* v___x_1692_; 
v___x_1692_ = lean_apply_4(v_recur_1677_, v_it_1679_, v___x_1691_, lean_box(0), lean_box(0));
return v___x_1692_;
}
}
}
}
v___jp_1695_:
{
lean_object* v___x_1699_; uint32_t v___x_1700_; uint32_t v___x_1701_; uint8_t v___x_1702_; 
v___x_1699_ = lean_string_utf8_extract(v_name_1670_, v_startInclusive_1697_, v_endExclusive_1698_);
lean_dec(v_endExclusive_1698_);
lean_dec(v_startInclusive_1697_);
v___x_1700_ = lean_string_utf8_get(v___x_1699_, v___x_1668_);
v___x_1701_ = 97;
v___x_1702_ = lean_uint32_dec_le(v___x_1701_, v___x_1700_);
if (v___x_1702_ == 0)
{
lean_object* v___x_1703_; 
v___x_1703_ = lean_string_utf8_set(v___x_1699_, v___x_1668_, v___x_1700_);
v_it_1679_ = v_it_1696_;
v_out_1680_ = v___x_1703_;
goto v___jp_1678_;
}
else
{
uint32_t v___x_1704_; uint8_t v___x_1705_; 
v___x_1704_ = 122;
v___x_1705_ = lean_uint32_dec_le(v___x_1700_, v___x_1704_);
if (v___x_1705_ == 0)
{
lean_object* v___x_1706_; 
v___x_1706_ = lean_string_utf8_set(v___x_1699_, v___x_1668_, v___x_1700_);
v_it_1679_ = v_it_1696_;
v_out_1680_ = v___x_1706_;
goto v___jp_1678_;
}
else
{
uint32_t v___x_1707_; uint32_t v___x_1708_; lean_object* v___x_1709_; 
v___x_1707_ = 4294967264;
v___x_1708_ = lean_uint32_add(v___x_1700_, v___x_1707_);
v___x_1709_ = lean_string_utf8_set(v___x_1699_, v___x_1668_, v___x_1708_);
v_it_1679_ = v_it_1696_;
v_out_1680_ = v___x_1709_;
goto v___jp_1678_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instEncodeV11___lam__0___boxed(lean_object* v___x_1734_, lean_object* v___x_1735_, lean_object* v___x_1736_, lean_object* v_name_1737_, lean_object* v___x_1738_, lean_object* v___x_1739_, lean_object* v___x_1740_, lean_object* v_it_1741_, lean_object* v_acc_1742_, lean_object* v_hP_1743_, lean_object* v_recur_1744_){
_start:
{
uint32_t v___x_916__boxed_1745_; lean_object* v_res_1746_; 
v___x_916__boxed_1745_ = lean_unbox_uint32(v___x_1739_);
lean_dec(v___x_1739_);
v_res_1746_ = l_Std_Http_Headers_instEncodeV11___lam__0(v___x_1734_, v___x_1735_, v___x_1736_, v_name_1737_, v___x_1738_, v___x_916__boxed_1745_, v___x_1740_, v_it_1741_, v_acc_1742_, v_hP_1743_, v_recur_1744_);
lean_dec_ref(v___x_1740_);
lean_dec_ref(v_name_1737_);
lean_dec(v___x_1736_);
lean_dec(v___x_1735_);
lean_dec_ref(v___x_1734_);
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instEncodeV11___lam__1(lean_object* v_buf_1747_, lean_object* v_name_1748_, lean_object* v_value_1749_){
_start:
{
lean_object* v___y_1751_; lean_object* v___f_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v_it_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___f_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; 
v___f_1770_ = ((lean_object*)(l_Std_Http_Headers_instToString___lam__1___closed__1));
v___x_1771_ = lean_unsigned_to_nat(0u);
v___x_1772_ = lean_string_utf8_byte_size(v_name_1748_);
lean_inc_ref(v_name_1748_);
v___x_1773_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1773_, 0, v_name_1748_);
lean_ctor_set(v___x_1773_, 1, v___x_1771_);
lean_ctor_set(v___x_1773_, 2, v___x_1772_);
lean_inc_ref(v___x_1773_);
v_it_1774_ = l_String_Slice_splitToSubslice___redArg(v___x_1773_, v___f_1770_);
v___x_1775_ = ((lean_object*)(l_Std_Http_Headers_instToString___lam__1___closed__2));
v___x_1776_ = lean_obj_once(&l_Std_Http_Headers_instToString___lam__1___closed__3, &l_Std_Http_Headers_instToString___lam__1___closed__3_once, _init_l_Std_Http_Headers_instToString___lam__1___closed__3);
v___x_1777_ = l_Std_Http_Headers_instToString___lam__1___boxed__const__1;
v___f_1778_ = lean_alloc_closure((void*)(l_Std_Http_Headers_instEncodeV11___lam__0___boxed), 11, 7);
lean_closure_set(v___f_1778_, 0, v___x_1775_);
lean_closure_set(v___f_1778_, 1, v___x_1771_);
lean_closure_set(v___f_1778_, 2, v___x_1776_);
lean_closure_set(v___f_1778_, 3, v_name_1748_);
lean_closure_set(v___f_1778_, 4, v___x_1772_);
lean_closure_set(v___f_1778_, 5, v___x_1777_);
lean_closure_set(v___f_1778_, 6, v___x_1773_);
v___x_1779_ = lean_box(0);
v___x_1780_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1778_, v_it_1774_, v___x_1779_, lean_box(0));
if (lean_obj_tag(v___x_1780_) == 0)
{
lean_object* v___x_1781_; 
v___x_1781_ = ((lean_object*)(l_Std_Http_Headers_get_x21___closed__0));
v___y_1751_ = v___x_1781_;
goto v___jp_1750_;
}
else
{
lean_object* v_val_1782_; 
v_val_1782_ = lean_ctor_get(v___x_1780_, 0);
lean_inc(v_val_1782_);
lean_dec_ref(v___x_1780_);
v___y_1751_ = v_val_1782_;
goto v___jp_1750_;
}
v___jp_1750_:
{
lean_object* v_data_1752_; lean_object* v_size_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1769_; 
v_data_1752_ = lean_ctor_get(v_buf_1747_, 0);
v_size_1753_ = lean_ctor_get(v_buf_1747_, 1);
v_isSharedCheck_1769_ = !lean_is_exclusive(v_buf_1747_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1755_ = v_buf_1747_;
v_isShared_1756_ = v_isSharedCheck_1769_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_size_1753_);
lean_inc(v_data_1752_);
lean_dec(v_buf_1747_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1769_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1767_; 
v___x_1757_ = ((lean_object*)(l_Std_Http_Headers_instToString___lam__1___closed__0));
v___x_1758_ = lean_string_append(v___y_1751_, v___x_1757_);
v___x_1759_ = lean_string_append(v___x_1758_, v_value_1749_);
v___x_1760_ = ((lean_object*)(l_Std_Http_Headers_instToString___lam__2___closed__0));
v___x_1761_ = lean_string_append(v___x_1759_, v___x_1760_);
v___x_1762_ = lean_string_to_utf8(v___x_1761_);
lean_dec_ref(v___x_1761_);
lean_inc_ref(v___x_1762_);
v___x_1763_ = lean_array_push(v_data_1752_, v___x_1762_);
v___x_1764_ = lean_byte_array_size(v___x_1762_);
lean_dec_ref(v___x_1762_);
v___x_1765_ = lean_nat_add(v_size_1753_, v___x_1764_);
lean_dec(v_size_1753_);
if (v_isShared_1756_ == 0)
{
lean_ctor_set(v___x_1755_, 1, v___x_1765_);
lean_ctor_set(v___x_1755_, 0, v___x_1763_);
v___x_1767_ = v___x_1755_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v___x_1763_);
lean_ctor_set(v_reuseFailAlloc_1768_, 1, v___x_1765_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instEncodeV11___lam__1___boxed(lean_object* v_buf_1783_, lean_object* v_name_1784_, lean_object* v_value_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l_Std_Http_Headers_instEncodeV11___lam__1(v_buf_1783_, v_name_1784_, v_value_1785_);
lean_dec_ref(v_value_1785_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instEncodeV11___lam__2(lean_object* v___f_1787_, lean_object* v_buffer_1788_, lean_object* v_headers_1789_){
_start:
{
lean_object* v___x_1790_; 
v___x_1790_ = l_Std_Http_Headers_fold___redArg(v_headers_1789_, v_buffer_1788_, v___f_1787_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instEncodeV11___lam__2___boxed(lean_object* v___f_1791_, lean_object* v_buffer_1792_, lean_object* v_headers_1793_){
_start:
{
lean_object* v_res_1794_; 
v_res_1794_ = l_Std_Http_Headers_instEncodeV11___lam__2(v___f_1791_, v_buffer_1792_, v_headers_1793_);
lean_dec_ref(v_headers_1793_);
return v_res_1794_;
}
}
static lean_object* _init_l_Std_Http_Headers_instEmptyCollection(void){
_start:
{
lean_object* v___x_1799_; 
v___x_1799_ = lean_obj_once(&l_Std_Http_Headers_empty___closed__0, &l_Std_Http_Headers_empty___closed__0_once, _init_l_Std_Http_Headers_empty___closed__0);
return v___x_1799_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instSingletonProdNameValue___lam__1(lean_object* v_x_1800_){
_start:
{
lean_object* v_fst_1801_; lean_object* v___x_1802_; lean_object* v_entries_1803_; lean_object* v_indexes_1804_; lean_object* v___f_1805_; lean_object* v___f_1806_; lean_object* v_i_1807_; lean_object* v_f_1808_; lean_object* v_entries_1809_; lean_object* v_indexes_1810_; lean_object* v___x_1811_; 
v_fst_1801_ = lean_ctor_get(v_x_1800_, 0);
lean_inc(v_fst_1801_);
v___x_1802_ = lean_obj_once(&l_Std_Http_Headers_empty___closed__0, &l_Std_Http_Headers_empty___closed__0_once, _init_l_Std_Http_Headers_empty___closed__0);
v_entries_1803_ = lean_ctor_get(v___x_1802_, 0);
v_indexes_1804_ = lean_ctor_get(v___x_1802_, 1);
v___f_1805_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_1806_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v_i_1807_ = lean_array_get_size(v_entries_1803_);
v_f_1808_ = lean_alloc_closure((void*)(l_Std_Http_Headers_insert___lam__0), 2, 1);
lean_closure_set(v_f_1808_, 0, v_i_1807_);
lean_inc_ref(v_entries_1803_);
v_entries_1809_ = lean_array_push(v_entries_1803_, v_x_1800_);
lean_inc_ref(v_indexes_1804_);
v_indexes_1810_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_1805_, v___f_1806_, v_indexes_1804_, v_fst_1801_, v_f_1808_);
v___x_1811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1811_, 0, v_entries_1809_);
lean_ctor_set(v___x_1811_, 1, v_indexes_1810_);
return v___x_1811_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instInsertProdNameValue___lam__1(lean_object* v_x_1814_, lean_object* v_s_1815_){
_start:
{
lean_object* v_fst_1816_; lean_object* v_entries_1817_; lean_object* v_indexes_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1831_; 
v_fst_1816_ = lean_ctor_get(v_x_1814_, 0);
lean_inc(v_fst_1816_);
v_entries_1817_ = lean_ctor_get(v_s_1815_, 0);
v_indexes_1818_ = lean_ctor_get(v_s_1815_, 1);
v_isSharedCheck_1831_ = !lean_is_exclusive(v_s_1815_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1820_ = v_s_1815_;
v_isShared_1821_ = v_isSharedCheck_1831_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_indexes_1818_);
lean_inc(v_entries_1817_);
lean_dec(v_s_1815_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1831_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___f_1822_; lean_object* v___f_1823_; lean_object* v_i_1824_; lean_object* v_f_1825_; lean_object* v_entries_1826_; lean_object* v_indexes_1827_; lean_object* v___x_1829_; 
v___f_1822_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_1823_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v_i_1824_ = lean_array_get_size(v_entries_1817_);
v_f_1825_ = lean_alloc_closure((void*)(l_Std_Http_Headers_insert___lam__0), 2, 1);
lean_closure_set(v_f_1825_, 0, v_i_1824_);
v_entries_1826_ = lean_array_push(v_entries_1817_, v_x_1814_);
v_indexes_1827_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_1822_, v___f_1823_, v_indexes_1818_, v_fst_1816_, v_f_1825_);
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 1, v_indexes_1827_);
lean_ctor_set(v___x_1820_, 0, v_entries_1826_);
v___x_1829_ = v___x_1820_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_entries_1826_);
lean_ctor_set(v_reuseFailAlloc_1830_, 1, v_indexes_1827_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instForInProdNameValueOfMonad___redArg___lam__0(lean_object* v_f_1836_, lean_object* v_a_1837_, lean_object* v_x_1838_, lean_object* v___y_1839_){
_start:
{
lean_object* v___x_1840_; 
v___x_1840_ = lean_apply_2(v_f_1836_, v_a_1837_, v___y_1839_);
return v___x_1840_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instForInProdNameValueOfMonad___redArg___lam__1(lean_object* v_inst_1841_, lean_object* v_00_u03b2_1842_, lean_object* v_headers_1843_, lean_object* v_b_1844_, lean_object* v_f_1845_){
_start:
{
lean_object* v_entries_1846_; lean_object* v___f_1847_; size_t v_sz_1848_; size_t v___x_1849_; lean_object* v___x_1850_; 
v_entries_1846_ = lean_ctor_get(v_headers_1843_, 0);
lean_inc_ref(v_entries_1846_);
lean_dec_ref(v_headers_1843_);
v___f_1847_ = lean_alloc_closure((void*)(l_Std_Http_Headers_instForInProdNameValueOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1847_, 0, v_f_1845_);
v_sz_1848_ = lean_array_size(v_entries_1846_);
v___x_1849_ = ((size_t)0ULL);
v___x_1850_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1841_, v_entries_1846_, v___f_1847_, v_sz_1848_, v___x_1849_, v_b_1844_);
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instForInProdNameValueOfMonad___redArg(lean_object* v_inst_1851_){
_start:
{
lean_object* v___f_1852_; 
v___f_1852_ = lean_alloc_closure((void*)(l_Std_Http_Headers_instForInProdNameValueOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_1852_, 0, v_inst_1851_);
return v___f_1852_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instForInProdNameValueOfMonad(lean_object* v_m_1853_, lean_object* v_inst_1854_){
_start:
{
lean_object* v___f_1855_; 
v___f_1855_ = lean_alloc_closure((void*)(l_Std_Http_Headers_instForInProdNameValueOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_1855_, 0, v_inst_1854_);
return v___f_1855_;
}
}
lean_object* runtime_initialize_Std_Http_Data_Headers_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_Headers_Name(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_Headers_Value(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Data_Headers(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Http_Data_Headers_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_Headers_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_Headers_Value(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Http_instInhabitedHeaders_default = _init_l_Std_Http_instInhabitedHeaders_default();
lean_mark_persistent(l_Std_Http_instInhabitedHeaders_default);
l_Std_Http_instInhabitedHeaders = _init_l_Std_Http_instInhabitedHeaders();
lean_mark_persistent(l_Std_Http_instInhabitedHeaders);
l_Std_Http_instMembershipNameHeaders = _init_l_Std_Http_instMembershipNameHeaders();
lean_mark_persistent(l_Std_Http_instMembershipNameHeaders);
l_Std_Http_Headers_empty = _init_l_Std_Http_Headers_empty();
lean_mark_persistent(l_Std_Http_Headers_empty);
l_Std_Http_Headers_instToString___lam__1___boxed__const__1 = _init_l_Std_Http_Headers_instToString___lam__1___boxed__const__1();
lean_mark_persistent(l_Std_Http_Headers_instToString___lam__1___boxed__const__1);
l_Std_Http_Headers_instEmptyCollection = _init_l_Std_Http_Headers_instEmptyCollection();
lean_mark_persistent(l_Std_Http_Headers_instEmptyCollection);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Http_Data_Headers(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Http_Data_Headers_Basic(uint8_t builtin);
lean_object* initialize_Std_Http_Data_Headers_Name(uint8_t builtin);
lean_object* initialize_Std_Http_Data_Headers_Value(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Http_Data_Headers(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Http_Data_Headers_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Data_Headers_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Data_Headers_Value(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_Headers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Http_Data_Headers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Http_Data_Headers(builtin);
}
#ifdef __cplusplus
}
#endif
