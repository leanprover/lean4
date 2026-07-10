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
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t l_Std_Http_Header_instBEqValue_beq(lean_object*, lean_object*);
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
uint8_t lean_bool_not(uint8_t);
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
lean_dec_ref_known(v_x_51_, 2);
v___x_56_ = l_Std_Format_joinSep___at___00Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8_spec__13___lam__0(v_head_55_);
return v___x_56_;
}
else
{
lean_object* v_head_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
lean_inc(v_tail_54_);
v_head_57_ = lean_ctor_get(v_x_51_, 0);
lean_inc(v_head_57_);
lean_dec_ref_known(v_x_51_, 2);
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
lean_dec_ref_known(v_x_108_, 2);
return v_head_112_;
}
else
{
lean_object* v_head_113_; lean_object* v___x_114_; 
lean_inc(v_tail_111_);
v_head_113_ = lean_ctor_get(v_x_108_, 0);
lean_inc(v_head_113_);
lean_dec_ref_known(v_x_108_, 2);
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
lean_dec_ref_known(v_x_180_, 2);
v___x_185_ = l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg(v_head_184_);
return v___x_185_;
}
else
{
lean_object* v_head_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
lean_inc(v_tail_183_);
v_head_186_ = lean_ctor_get(v_x_180_, 0);
lean_inc(v_head_186_);
lean_dec_ref_known(v_x_180_, 2);
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
lean_dec_ref_known(v_x_266_, 2);
v___x_271_ = l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg(v_head_270_);
return v___x_271_;
}
else
{
lean_object* v_head_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
lean_inc(v_tail_269_);
v_head_272_ = lean_ctor_get(v_x_266_, 0);
lean_inc(v_head_272_);
lean_dec_ref_known(v_x_266_, 2);
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
lean_object* v_entries_551_; lean_object* v_indexes_552_; lean_object* v___f_553_; lean_object* v___f_554_; lean_object* v___x_555_; lean_object* v___f_556_; lean_object* v___x_557_; size_t v_sz_558_; size_t v___x_559_; lean_object* v_entries_560_; 
v_entries_551_ = lean_ctor_get(v_headers_549_, 0);
lean_inc_ref(v_entries_551_);
v_indexes_552_ = lean_ctor_get(v_headers_549_, 1);
lean_inc_ref(v_indexes_552_);
lean_dec_ref(v_headers_549_);
v___f_553_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_554_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v___x_555_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v___f_553_, v___f_554_, v_indexes_552_, v_name_550_);
lean_dec_ref(v_indexes_552_);
lean_inc_n(v___x_555_, 2);
v___f_556_ = lean_alloc_closure((void*)(l_Std_Http_Headers_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_556_, 0, v___x_555_);
lean_closure_set(v___f_556_, 1, v_entries_551_);
v___x_557_ = ((lean_object*)(l_Std_Http_Headers_getAll___redArg___closed__9));
v_sz_558_ = lean_array_size(v___x_555_);
v___x_559_ = ((size_t)0ULL);
v_entries_560_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_557_, v___x_555_, v___f_556_, v_sz_558_, v___x_559_, v___x_555_);
lean_dec(v___x_555_);
return v_entries_560_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_getAll(lean_object* v_headers_561_, lean_object* v_name_562_, lean_object* v_h_563_){
_start:
{
lean_object* v_entries_564_; lean_object* v_indexes_565_; lean_object* v___f_566_; lean_object* v___f_567_; lean_object* v___x_568_; lean_object* v___f_569_; lean_object* v___x_570_; size_t v_sz_571_; size_t v___x_572_; lean_object* v_entries_573_; 
v_entries_564_ = lean_ctor_get(v_headers_561_, 0);
lean_inc_ref(v_entries_564_);
v_indexes_565_ = lean_ctor_get(v_headers_561_, 1);
lean_inc_ref(v_indexes_565_);
lean_dec_ref(v_headers_561_);
v___f_566_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_567_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v___x_568_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v___f_566_, v___f_567_, v_indexes_565_, v_name_562_);
lean_dec_ref(v_indexes_565_);
lean_inc_n(v___x_568_, 2);
v___f_569_ = lean_alloc_closure((void*)(l_Std_Http_Headers_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_569_, 0, v___x_568_);
lean_closure_set(v___f_569_, 1, v_entries_564_);
v___x_570_ = ((lean_object*)(l_Std_Http_Headers_getAll___redArg___closed__9));
v_sz_571_ = lean_array_size(v___x_568_);
v___x_572_ = ((size_t)0ULL);
v_entries_573_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_570_, v___x_568_, v___f_569_, v_sz_571_, v___x_572_, v___x_568_);
lean_dec(v___x_568_);
return v_entries_573_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_getAll_x3f(lean_object* v_headers_574_, lean_object* v_name_575_){
_start:
{
lean_object* v___f_576_; lean_object* v___f_577_; uint8_t v___x_578_; 
v___f_576_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_577_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
lean_inc_ref(v_name_575_);
v___x_578_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_576_, v___f_577_, v_name_575_, v_headers_574_);
if (v___x_578_ == 0)
{
lean_object* v___x_579_; 
lean_dec_ref(v_name_575_);
lean_dec_ref(v_headers_574_);
v___x_579_ = lean_box(0);
return v___x_579_;
}
else
{
lean_object* v_entries_580_; lean_object* v_indexes_581_; lean_object* v___x_582_; lean_object* v___f_583_; lean_object* v___x_584_; size_t v_sz_585_; size_t v___x_586_; lean_object* v_entries_587_; lean_object* v___x_588_; 
v_entries_580_ = lean_ctor_get(v_headers_574_, 0);
lean_inc_ref(v_entries_580_);
v_indexes_581_ = lean_ctor_get(v_headers_574_, 1);
lean_inc_ref(v_indexes_581_);
lean_dec_ref(v_headers_574_);
v___x_582_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v___f_576_, v___f_577_, v_indexes_581_, v_name_575_);
lean_dec_ref(v_indexes_581_);
lean_inc_n(v___x_582_, 2);
v___f_583_ = lean_alloc_closure((void*)(l_Std_Http_Headers_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_583_, 0, v___x_582_);
lean_closure_set(v___f_583_, 1, v_entries_580_);
v___x_584_ = ((lean_object*)(l_Std_Http_Headers_getAll___redArg___closed__9));
v_sz_585_ = lean_array_size(v___x_582_);
v___x_586_ = ((size_t)0ULL);
v_entries_587_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_584_, v___x_582_, v___f_583_, v_sz_585_, v___x_586_, v___x_582_);
lean_dec(v___x_582_);
v___x_588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_588_, 0, v_entries_587_);
return v___x_588_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_get_x3f(lean_object* v_headers_589_, lean_object* v_name_590_){
_start:
{
lean_object* v___f_591_; lean_object* v___f_592_; uint8_t v___x_593_; 
v___f_591_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_592_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
lean_inc_ref(v_name_590_);
v___x_593_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_591_, v___f_592_, v_name_590_, v_headers_589_);
if (v___x_593_ == 0)
{
lean_object* v___x_594_; 
lean_dec_ref(v_name_590_);
v___x_594_ = lean_box(0);
return v___x_594_;
}
else
{
lean_object* v_entries_595_; lean_object* v_indexes_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v_entry_599_; lean_object* v___x_600_; lean_object* v_snd_601_; lean_object* v___x_602_; 
v_entries_595_ = lean_ctor_get(v_headers_589_, 0);
v_indexes_596_ = lean_ctor_get(v_headers_589_, 1);
v___x_597_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v___f_591_, v___f_592_, v_indexes_596_, v_name_590_);
v___x_598_ = lean_unsigned_to_nat(0u);
v_entry_599_ = lean_array_fget(v___x_597_, v___x_598_);
lean_dec(v___x_597_);
v___x_600_ = lean_array_fget_borrowed(v_entries_595_, v_entry_599_);
lean_dec(v_entry_599_);
v_snd_601_ = lean_ctor_get(v___x_600_, 1);
lean_inc(v_snd_601_);
v___x_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_602_, 0, v_snd_601_);
return v___x_602_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_get_x3f___boxed(lean_object* v_headers_603_, lean_object* v_name_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l_Std_Http_Headers_get_x3f(v_headers_603_, v_name_604_);
lean_dec_ref(v_headers_603_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_hasEntry___lam__1(lean_object* v_value_606_, lean_object* v___x_607_, lean_object* v___x_608_, lean_object* v_a_609_, lean_object* v_x_610_, lean_object* v___y_611_){
_start:
{
uint8_t v___x_612_; 
v___x_612_ = l_Std_Http_Header_instBEqValue_beq(v_a_609_, v_value_606_);
if (v___x_612_ == 0)
{
lean_object* v___x_613_; 
lean_dec_ref(v_a_609_);
v___x_613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_613_, 0, v___x_607_);
return v___x_613_;
}
else
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
lean_dec_ref(v___x_607_);
v___x_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_614_, 0, v_a_609_);
v___x_615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
v___x_616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_616_, 0, v___x_615_);
lean_ctor_set(v___x_616_, 1, v___x_608_);
v___x_617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_617_, 0, v___x_616_);
return v___x_617_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_hasEntry___lam__1___boxed(lean_object* v_value_618_, lean_object* v___x_619_, lean_object* v___x_620_, lean_object* v_a_621_, lean_object* v_x_622_, lean_object* v___y_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_Std_Http_Headers_hasEntry___lam__1(v_value_618_, v___x_619_, v___x_620_, v_a_621_, v_x_622_, v___y_623_);
lean_dec_ref(v___y_623_);
lean_dec_ref(v_value_618_);
return v_res_624_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Headers_hasEntry(lean_object* v_headers_628_, lean_object* v_name_629_, lean_object* v_value_630_){
_start:
{
lean_object* v___f_631_; lean_object* v___f_632_; uint8_t v___x_633_; 
v___f_631_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_632_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
lean_inc_ref(v_name_629_);
v___x_633_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_631_, v___f_632_, v_name_629_, v_headers_628_);
if (v___x_633_ == 0)
{
lean_dec_ref(v_value_630_);
lean_dec_ref(v_name_629_);
lean_dec_ref(v_headers_628_);
return v___x_633_;
}
else
{
lean_object* v_entries_634_; lean_object* v_indexes_635_; lean_object* v___x_636_; lean_object* v___f_637_; lean_object* v___x_638_; size_t v_sz_639_; size_t v___x_640_; lean_object* v_entries_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___f_644_; size_t v_sz_645_; lean_object* v___x_646_; lean_object* v_fst_647_; 
v_entries_634_ = lean_ctor_get(v_headers_628_, 0);
lean_inc_ref(v_entries_634_);
v_indexes_635_ = lean_ctor_get(v_headers_628_, 1);
lean_inc_ref(v_indexes_635_);
lean_dec_ref(v_headers_628_);
v___x_636_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v___f_631_, v___f_632_, v_indexes_635_, v_name_629_);
lean_dec_ref(v_indexes_635_);
lean_inc_n(v___x_636_, 2);
v___f_637_ = lean_alloc_closure((void*)(l_Std_Http_Headers_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_637_, 0, v___x_636_);
lean_closure_set(v___f_637_, 1, v_entries_634_);
v___x_638_ = ((lean_object*)(l_Std_Http_Headers_getAll___redArg___closed__9));
v_sz_639_ = lean_array_size(v___x_636_);
v___x_640_ = ((size_t)0ULL);
v_entries_641_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_638_, v___x_636_, v___f_637_, v_sz_639_, v___x_640_, v___x_636_);
lean_dec(v___x_636_);
v___x_642_ = lean_box(0);
v___x_643_ = ((lean_object*)(l_Std_Http_Headers_hasEntry___closed__0));
v___f_644_ = lean_alloc_closure((void*)(l_Std_Http_Headers_hasEntry___lam__1___boxed), 6, 3);
lean_closure_set(v___f_644_, 0, v_value_630_);
lean_closure_set(v___f_644_, 1, v___x_643_);
lean_closure_set(v___f_644_, 2, v___x_642_);
v_sz_645_ = lean_array_size(v_entries_641_);
v___x_646_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_638_, v_entries_641_, v___f_644_, v_sz_645_, v___x_640_, v___x_643_);
v_fst_647_ = lean_ctor_get(v___x_646_, 0);
lean_inc(v_fst_647_);
lean_dec(v___x_646_);
if (lean_obj_tag(v_fst_647_) == 0)
{
uint8_t v___x_648_; 
v___x_648_ = 0;
return v___x_648_;
}
else
{
lean_object* v_val_649_; 
v_val_649_ = lean_ctor_get(v_fst_647_, 0);
lean_inc(v_val_649_);
lean_dec_ref_known(v_fst_647_, 1);
if (lean_obj_tag(v_val_649_) == 0)
{
uint8_t v___x_650_; 
v___x_650_ = 0;
return v___x_650_;
}
else
{
lean_dec_ref_known(v_val_649_, 1);
return v___x_633_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_hasEntry___boxed(lean_object* v_headers_651_, lean_object* v_name_652_, lean_object* v_value_653_){
_start:
{
uint8_t v_res_654_; lean_object* v_r_655_; 
v_res_654_ = l_Std_Http_Headers_hasEntry(v_headers_651_, v_name_652_, v_value_653_);
v_r_655_ = lean_box(v_res_654_);
return v_r_655_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_getLast_x3f(lean_object* v_headers_656_, lean_object* v_name_657_){
_start:
{
lean_object* v___f_658_; lean_object* v___f_659_; uint8_t v___x_660_; 
v___f_658_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_659_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
lean_inc_ref(v_name_657_);
v___x_660_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_658_, v___f_659_, v_name_657_, v_headers_656_);
if (v___x_660_ == 0)
{
lean_object* v___x_661_; 
lean_dec_ref(v_name_657_);
lean_dec_ref(v_headers_656_);
v___x_661_ = lean_box(0);
return v___x_661_;
}
else
{
lean_object* v_entries_662_; lean_object* v_indexes_663_; lean_object* v___x_664_; lean_object* v___f_665_; lean_object* v___x_666_; size_t v_sz_667_; size_t v___x_668_; lean_object* v_entries_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; uint8_t v___x_673_; 
v_entries_662_ = lean_ctor_get(v_headers_656_, 0);
lean_inc_ref(v_entries_662_);
v_indexes_663_ = lean_ctor_get(v_headers_656_, 1);
lean_inc_ref(v_indexes_663_);
lean_dec_ref(v_headers_656_);
v___x_664_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v___f_658_, v___f_659_, v_indexes_663_, v_name_657_);
lean_dec_ref(v_indexes_663_);
lean_inc_n(v___x_664_, 2);
v___f_665_ = lean_alloc_closure((void*)(l_Std_Http_Headers_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_665_, 0, v___x_664_);
lean_closure_set(v___f_665_, 1, v_entries_662_);
v___x_666_ = ((lean_object*)(l_Std_Http_Headers_getAll___redArg___closed__9));
v_sz_667_ = lean_array_size(v___x_664_);
v___x_668_ = ((size_t)0ULL);
v_entries_669_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_666_, v___x_664_, v___f_665_, v_sz_667_, v___x_668_, v___x_664_);
lean_dec(v___x_664_);
v___x_670_ = lean_array_get_size(v_entries_669_);
v___x_671_ = lean_unsigned_to_nat(1u);
v___x_672_ = lean_nat_sub(v___x_670_, v___x_671_);
v___x_673_ = lean_nat_dec_lt(v___x_672_, v___x_670_);
if (v___x_673_ == 0)
{
lean_object* v___x_674_; 
lean_dec(v___x_672_);
lean_dec(v_entries_669_);
v___x_674_ = lean_box(0);
return v___x_674_;
}
else
{
lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_675_ = lean_array_fget(v_entries_669_, v___x_672_);
lean_dec(v___x_672_);
lean_dec(v_entries_669_);
v___x_676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_676_, 0, v___x_675_);
return v___x_676_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_getD(lean_object* v_headers_677_, lean_object* v_name_678_, lean_object* v_d_679_){
_start:
{
lean_object* v___f_680_; lean_object* v___f_681_; uint8_t v___x_682_; 
v___f_680_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_681_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
lean_inc_ref(v_name_678_);
v___x_682_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_680_, v___f_681_, v_name_678_, v_headers_677_);
if (v___x_682_ == 0)
{
lean_dec_ref(v_name_678_);
lean_inc_ref(v_d_679_);
return v_d_679_;
}
else
{
lean_object* v_entries_683_; lean_object* v_indexes_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v_entry_687_; lean_object* v___x_688_; lean_object* v_snd_689_; 
v_entries_683_ = lean_ctor_get(v_headers_677_, 0);
v_indexes_684_ = lean_ctor_get(v_headers_677_, 1);
v___x_685_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v___f_680_, v___f_681_, v_indexes_684_, v_name_678_);
v___x_686_ = lean_unsigned_to_nat(0u);
v_entry_687_ = lean_array_fget(v___x_685_, v___x_686_);
lean_dec(v___x_685_);
v___x_688_ = lean_array_fget_borrowed(v_entries_683_, v_entry_687_);
lean_dec(v_entry_687_);
v_snd_689_ = lean_ctor_get(v___x_688_, 1);
lean_inc(v_snd_689_);
return v_snd_689_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_getD___boxed(lean_object* v_headers_690_, lean_object* v_name_691_, lean_object* v_d_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Std_Http_Headers_getD(v_headers_690_, v_name_691_, v_d_692_);
lean_dec_ref(v_d_692_);
lean_dec_ref(v_headers_690_);
return v_res_693_;
}
}
static lean_object* _init_l_Std_Http_Headers_get_x21___closed__4(void){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_698_ = ((lean_object*)(l_Std_Http_Headers_get_x21___closed__3));
v___x_699_ = lean_unsigned_to_nat(14u);
v___x_700_ = lean_unsigned_to_nat(22u);
v___x_701_ = ((lean_object*)(l_Std_Http_Headers_get_x21___closed__2));
v___x_702_ = ((lean_object*)(l_Std_Http_Headers_get_x21___closed__1));
v___x_703_ = l_mkPanicMessageWithDecl(v___x_702_, v___x_701_, v___x_700_, v___x_699_, v___x_698_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_get_x21(lean_object* v_headers_704_, lean_object* v_name_705_){
_start:
{
lean_object* v___f_706_; lean_object* v___f_707_; uint8_t v___x_708_; 
v___f_706_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_707_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
lean_inc_ref(v_name_705_);
v___x_708_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_706_, v___f_707_, v_name_705_, v_headers_704_);
if (v___x_708_ == 0)
{
lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
lean_dec_ref(v_name_705_);
v___x_709_ = ((lean_object*)(l_Std_Http_Headers_get_x21___closed__0));
v___x_710_ = lean_obj_once(&l_Std_Http_Headers_get_x21___closed__4, &l_Std_Http_Headers_get_x21___closed__4_once, _init_l_Std_Http_Headers_get_x21___closed__4);
v___x_711_ = l_panic___redArg(v___x_709_, v___x_710_);
return v___x_711_;
}
else
{
lean_object* v_entries_712_; lean_object* v_indexes_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v_entry_716_; lean_object* v___x_717_; lean_object* v_snd_718_; 
v_entries_712_ = lean_ctor_get(v_headers_704_, 0);
v_indexes_713_ = lean_ctor_get(v_headers_704_, 1);
v___x_714_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v___f_706_, v___f_707_, v_indexes_713_, v_name_705_);
v___x_715_ = lean_unsigned_to_nat(0u);
v_entry_716_ = lean_array_fget(v___x_714_, v___x_715_);
lean_dec(v___x_714_);
v___x_717_ = lean_array_fget_borrowed(v_entries_712_, v_entry_716_);
lean_dec(v_entry_716_);
v_snd_718_ = lean_ctor_get(v___x_717_, 1);
lean_inc(v_snd_718_);
return v_snd_718_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_get_x21___boxed(lean_object* v_headers_719_, lean_object* v_name_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l_Std_Http_Headers_get_x21(v_headers_719_, v_name_720_);
lean_dec_ref(v_headers_719_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_insert___lam__0(lean_object* v_i_722_, lean_object* v_x_723_){
_start:
{
if (lean_obj_tag(v_x_723_) == 0)
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_724_ = lean_unsigned_to_nat(1u);
v___x_725_ = lean_mk_empty_array_with_capacity(v___x_724_);
v___x_726_ = lean_array_push(v___x_725_, v_i_722_);
v___x_727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
return v___x_727_;
}
else
{
lean_object* v_val_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_736_; 
v_val_728_ = lean_ctor_get(v_x_723_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v_x_723_);
if (v_isSharedCheck_736_ == 0)
{
v___x_730_ = v_x_723_;
v_isShared_731_ = v_isSharedCheck_736_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_val_728_);
lean_dec(v_x_723_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_736_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_732_; lean_object* v___x_734_; 
v___x_732_ = lean_array_push(v_val_728_, v_i_722_);
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 0, v___x_732_);
v___x_734_ = v___x_730_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v___x_732_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_insert(lean_object* v_headers_737_, lean_object* v_key_738_, lean_object* v_value_739_){
_start:
{
lean_object* v_entries_740_; lean_object* v_indexes_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_755_; 
v_entries_740_ = lean_ctor_get(v_headers_737_, 0);
v_indexes_741_ = lean_ctor_get(v_headers_737_, 1);
v_isSharedCheck_755_ = !lean_is_exclusive(v_headers_737_);
if (v_isSharedCheck_755_ == 0)
{
v___x_743_ = v_headers_737_;
v_isShared_744_ = v_isSharedCheck_755_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_indexes_741_);
lean_inc(v_entries_740_);
lean_dec(v_headers_737_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_755_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___f_745_; lean_object* v___f_746_; lean_object* v_i_747_; lean_object* v_f_748_; lean_object* v___x_749_; lean_object* v_entries_750_; lean_object* v_indexes_751_; lean_object* v___x_753_; 
v___f_745_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_746_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v_i_747_ = lean_array_get_size(v_entries_740_);
v_f_748_ = lean_alloc_closure((void*)(l_Std_Http_Headers_insert___lam__0), 2, 1);
lean_closure_set(v_f_748_, 0, v_i_747_);
lean_inc_ref(v_key_738_);
v___x_749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_749_, 0, v_key_738_);
lean_ctor_set(v___x_749_, 1, v_value_739_);
v_entries_750_ = lean_array_push(v_entries_740_, v___x_749_);
v_indexes_751_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_745_, v___f_746_, v_indexes_741_, v_key_738_, v_f_748_);
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 1, v_indexes_751_);
lean_ctor_set(v___x_743_, 0, v_entries_750_);
v___x_753_ = v___x_743_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_entries_750_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v_indexes_751_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_insert_x21(lean_object* v_headers_756_, lean_object* v_name_757_, lean_object* v_value_758_){
_start:
{
lean_object* v_entries_759_; lean_object* v_indexes_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_776_; 
v_entries_759_ = lean_ctor_get(v_headers_756_, 0);
v_indexes_760_ = lean_ctor_get(v_headers_756_, 1);
v_isSharedCheck_776_ = !lean_is_exclusive(v_headers_756_);
if (v_isSharedCheck_776_ == 0)
{
v___x_762_ = v_headers_756_;
v_isShared_763_ = v_isSharedCheck_776_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_indexes_760_);
lean_inc(v_entries_759_);
lean_dec(v_headers_756_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_776_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___f_766_; lean_object* v___f_767_; lean_object* v_i_768_; lean_object* v_f_769_; lean_object* v___x_770_; lean_object* v_entries_771_; lean_object* v_indexes_772_; lean_object* v___x_774_; 
v___x_764_ = l_Std_Http_Header_Name_ofString_x21(v_name_757_);
v___x_765_ = l_Std_Http_Header_Value_ofString_x21(v_value_758_);
v___f_766_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_767_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v_i_768_ = lean_array_get_size(v_entries_759_);
v_f_769_ = lean_alloc_closure((void*)(l_Std_Http_Headers_insert___lam__0), 2, 1);
lean_closure_set(v_f_769_, 0, v_i_768_);
lean_inc_ref(v___x_764_);
v___x_770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_770_, 0, v___x_764_);
lean_ctor_set(v___x_770_, 1, v___x_765_);
v_entries_771_ = lean_array_push(v_entries_759_, v___x_770_);
v_indexes_772_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_766_, v___f_767_, v_indexes_760_, v___x_764_, v_f_769_);
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 1, v_indexes_772_);
lean_ctor_set(v___x_762_, 0, v_entries_771_);
v___x_774_ = v___x_762_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_entries_771_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v_indexes_772_);
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
LEAN_EXPORT lean_object* l_Std_Http_Headers_insert_x3f(lean_object* v_headers_777_, lean_object* v_name_778_, lean_object* v_value_779_){
_start:
{
lean_object* v___x_780_; 
v___x_780_ = l_Std_Http_Header_Name_ofString_x3f(v_name_778_);
if (lean_obj_tag(v___x_780_) == 0)
{
lean_object* v___x_781_; 
lean_dec_ref(v_value_779_);
lean_dec_ref(v_headers_777_);
v___x_781_ = lean_box(0);
return v___x_781_;
}
else
{
lean_object* v_val_782_; lean_object* v___x_783_; 
v_val_782_ = lean_ctor_get(v___x_780_, 0);
lean_inc(v_val_782_);
lean_dec_ref_known(v___x_780_, 1);
v___x_783_ = l_Std_Http_Header_Value_ofString_x3f(v_value_779_);
if (lean_obj_tag(v___x_783_) == 0)
{
lean_object* v___x_784_; 
lean_dec(v_val_782_);
lean_dec_ref(v_headers_777_);
v___x_784_ = lean_box(0);
return v___x_784_;
}
else
{
lean_object* v_val_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_808_; 
v_val_785_ = lean_ctor_get(v___x_783_, 0);
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_808_ == 0)
{
v___x_787_ = v___x_783_;
v_isShared_788_ = v_isSharedCheck_808_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_val_785_);
lean_dec(v___x_783_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_808_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v_entries_789_; lean_object* v_indexes_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_807_; 
v_entries_789_ = lean_ctor_get(v_headers_777_, 0);
v_indexes_790_ = lean_ctor_get(v_headers_777_, 1);
v_isSharedCheck_807_ = !lean_is_exclusive(v_headers_777_);
if (v_isSharedCheck_807_ == 0)
{
v___x_792_ = v_headers_777_;
v_isShared_793_ = v_isSharedCheck_807_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_indexes_790_);
lean_inc(v_entries_789_);
lean_dec(v_headers_777_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_807_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___f_794_; lean_object* v___f_795_; lean_object* v_i_796_; lean_object* v_f_797_; lean_object* v___x_798_; lean_object* v_entries_799_; lean_object* v_indexes_800_; lean_object* v___x_802_; 
v___f_794_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_795_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v_i_796_ = lean_array_get_size(v_entries_789_);
v_f_797_ = lean_alloc_closure((void*)(l_Std_Http_Headers_insert___lam__0), 2, 1);
lean_closure_set(v_f_797_, 0, v_i_796_);
lean_inc(v_val_782_);
v___x_798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_798_, 0, v_val_782_);
lean_ctor_set(v___x_798_, 1, v_val_785_);
v_entries_799_ = lean_array_push(v_entries_789_, v___x_798_);
v_indexes_800_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_794_, v___f_795_, v_indexes_790_, v_val_782_, v_f_797_);
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 1, v_indexes_800_);
lean_ctor_set(v___x_792_, 0, v_entries_799_);
v___x_802_ = v___x_792_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_entries_799_);
lean_ctor_set(v_reuseFailAlloc_806_, 1, v_indexes_800_);
v___x_802_ = v_reuseFailAlloc_806_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
lean_object* v___x_804_; 
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 0, v___x_802_);
v___x_804_ = v___x_787_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_802_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_insertMany___lam__1(lean_object* v_key_809_, lean_object* v___f_810_, lean_object* v___f_811_, lean_object* v_x1_812_, lean_object* v_x2_813_){
_start:
{
lean_object* v_entries_814_; lean_object* v_indexes_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_827_; 
v_entries_814_ = lean_ctor_get(v_x1_812_, 0);
v_indexes_815_ = lean_ctor_get(v_x1_812_, 1);
v_isSharedCheck_827_ = !lean_is_exclusive(v_x1_812_);
if (v_isSharedCheck_827_ == 0)
{
v___x_817_ = v_x1_812_;
v_isShared_818_ = v_isSharedCheck_827_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_indexes_815_);
lean_inc(v_entries_814_);
lean_dec(v_x1_812_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_827_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v_i_819_; lean_object* v_f_820_; lean_object* v___x_821_; lean_object* v_entries_822_; lean_object* v_indexes_823_; lean_object* v___x_825_; 
v_i_819_ = lean_array_get_size(v_entries_814_);
v_f_820_ = lean_alloc_closure((void*)(l_Std_Http_Headers_insert___lam__0), 2, 1);
lean_closure_set(v_f_820_, 0, v_i_819_);
lean_inc_ref(v_key_809_);
v___x_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_821_, 0, v_key_809_);
lean_ctor_set(v___x_821_, 1, v_x2_813_);
v_entries_822_ = lean_array_push(v_entries_814_, v___x_821_);
v_indexes_823_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_810_, v___f_811_, v_indexes_815_, v_key_809_, v_f_820_);
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 1, v_indexes_823_);
lean_ctor_set(v___x_817_, 0, v_entries_822_);
v___x_825_ = v___x_817_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_entries_822_);
lean_ctor_set(v_reuseFailAlloc_826_, 1, v_indexes_823_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_insertMany(lean_object* v_headers_828_, lean_object* v_key_829_, lean_object* v_values_830_){
_start:
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; uint8_t v___x_834_; 
v___x_831_ = lean_unsigned_to_nat(0u);
v___x_832_ = lean_array_get_size(v_values_830_);
v___x_833_ = ((lean_object*)(l_Std_Http_Headers_getAll___redArg___closed__9));
v___x_834_ = lean_nat_dec_lt(v___x_831_, v___x_832_);
if (v___x_834_ == 0)
{
lean_dec_ref(v_values_830_);
lean_dec_ref(v_key_829_);
return v_headers_828_;
}
else
{
lean_object* v___f_835_; lean_object* v___f_836_; lean_object* v___f_837_; uint8_t v___x_838_; 
v___f_835_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_836_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v___f_837_ = lean_alloc_closure((void*)(l_Std_Http_Headers_insertMany___lam__1), 5, 3);
lean_closure_set(v___f_837_, 0, v_key_829_);
lean_closure_set(v___f_837_, 1, v___f_835_);
lean_closure_set(v___f_837_, 2, v___f_836_);
v___x_838_ = lean_nat_dec_le(v___x_832_, v___x_832_);
if (v___x_838_ == 0)
{
if (v___x_834_ == 0)
{
lean_dec_ref(v___f_837_);
lean_dec_ref(v_values_830_);
return v_headers_828_;
}
else
{
size_t v___x_839_; size_t v___x_840_; lean_object* v___x_841_; 
v___x_839_ = ((size_t)0ULL);
v___x_840_ = lean_usize_of_nat(v___x_832_);
v___x_841_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_833_, v___f_837_, v_values_830_, v___x_839_, v___x_840_, v_headers_828_);
return v___x_841_;
}
}
else
{
size_t v___x_842_; size_t v___x_843_; lean_object* v___x_844_; 
v___x_842_ = ((size_t)0ULL);
v___x_843_ = lean_usize_of_nat(v___x_832_);
v___x_844_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_833_, v___f_837_, v_values_830_, v___x_842_, v___x_843_, v_headers_828_);
return v___x_844_;
}
}
}
}
static lean_object* _init_l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__1(void){
_start:
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_847_ = lean_obj_once(&l_Std_Http_instInhabitedHeaders_default___closed__2, &l_Std_Http_instInhabitedHeaders_default___closed__2_once, _init_l_Std_Http_instInhabitedHeaders_default___closed__2);
v___x_848_ = ((lean_object*)(l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__0));
v___x_849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_849_, 0, v___x_848_);
lean_ctor_set(v___x_849_, 1, v___x_847_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0(lean_object* v_00_u03b2_850_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__1, &l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__1_once, _init_l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__1);
return v___x_851_;
}
}
static lean_object* _init_l_Std_Http_Headers_empty___closed__0(void){
_start:
{
lean_object* v___x_852_; 
v___x_852_ = l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0(lean_box(0));
return v___x_852_;
}
}
static lean_object* _init_l_Std_Http_Headers_empty(void){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = lean_obj_once(&l_Std_Http_Headers_empty___closed__0, &l_Std_Http_Headers_empty___closed__0_once, _init_l_Std_Http_Headers_empty___closed__0);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__3(lean_object* v_i_854_, lean_object* v_a_855_, lean_object* v_x_856_){
_start:
{
if (lean_obj_tag(v_x_856_) == 0)
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v_val_859_; lean_object* v___x_860_; 
v___x_857_ = lean_box(0);
v___x_858_ = l_Std_Http_Headers_insert___lam__0(v_i_854_, v___x_857_);
v_val_859_ = lean_ctor_get(v___x_858_, 0);
lean_inc(v_val_859_);
lean_dec(v___x_858_);
v___x_860_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_860_, 0, v_a_855_);
lean_ctor_set(v___x_860_, 1, v_val_859_);
lean_ctor_set(v___x_860_, 2, v_x_856_);
return v___x_860_;
}
else
{
lean_object* v_key_861_; lean_object* v_value_862_; lean_object* v_tail_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_878_; 
v_key_861_ = lean_ctor_get(v_x_856_, 0);
v_value_862_ = lean_ctor_get(v_x_856_, 1);
v_tail_863_ = lean_ctor_get(v_x_856_, 2);
v_isSharedCheck_878_ = !lean_is_exclusive(v_x_856_);
if (v_isSharedCheck_878_ == 0)
{
v___x_865_ = v_x_856_;
v_isShared_866_ = v_isSharedCheck_878_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_tail_863_);
lean_inc(v_value_862_);
lean_inc(v_key_861_);
lean_dec(v_x_856_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_878_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
uint8_t v___x_867_; 
v___x_867_ = lean_string_dec_eq(v_key_861_, v_a_855_);
if (v___x_867_ == 0)
{
lean_object* v_tail_868_; lean_object* v___x_870_; 
v_tail_868_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__3(v_i_854_, v_a_855_, v_tail_863_);
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 2, v_tail_868_);
v___x_870_ = v___x_865_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_key_861_);
lean_ctor_set(v_reuseFailAlloc_871_, 1, v_value_862_);
lean_ctor_set(v_reuseFailAlloc_871_, 2, v_tail_868_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
else
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v_val_874_; lean_object* v___x_876_; 
lean_dec(v_key_861_);
v___x_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_872_, 0, v_value_862_);
v___x_873_ = l_Std_Http_Headers_insert___lam__0(v_i_854_, v___x_872_);
v_val_874_ = lean_ctor_get(v___x_873_, 0);
lean_inc(v_val_874_);
lean_dec(v___x_873_);
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 1, v_val_874_);
lean_ctor_set(v___x_865_, 0, v_a_855_);
v___x_876_ = v___x_865_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_a_855_);
lean_ctor_set(v_reuseFailAlloc_877_, 1, v_val_874_);
lean_ctor_set(v_reuseFailAlloc_877_, 2, v_tail_863_);
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
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_x_879_, lean_object* v_x_880_){
_start:
{
if (lean_obj_tag(v_x_880_) == 0)
{
return v_x_879_;
}
else
{
lean_object* v_key_881_; lean_object* v_value_882_; lean_object* v_tail_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_906_; 
v_key_881_ = lean_ctor_get(v_x_880_, 0);
v_value_882_ = lean_ctor_get(v_x_880_, 1);
v_tail_883_ = lean_ctor_get(v_x_880_, 2);
v_isSharedCheck_906_ = !lean_is_exclusive(v_x_880_);
if (v_isSharedCheck_906_ == 0)
{
v___x_885_ = v_x_880_;
v_isShared_886_ = v_isSharedCheck_906_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_tail_883_);
lean_inc(v_value_882_);
lean_inc(v_key_881_);
lean_dec(v_x_880_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_906_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_887_; uint64_t v___x_888_; uint64_t v___x_889_; uint64_t v___x_890_; uint64_t v_fold_891_; uint64_t v___x_892_; uint64_t v___x_893_; uint64_t v___x_894_; size_t v___x_895_; size_t v___x_896_; size_t v___x_897_; size_t v___x_898_; size_t v___x_899_; lean_object* v___x_900_; lean_object* v___x_902_; 
v___x_887_ = lean_array_get_size(v_x_879_);
v___x_888_ = lean_string_hash(v_key_881_);
v___x_889_ = 32ULL;
v___x_890_ = lean_uint64_shift_right(v___x_888_, v___x_889_);
v_fold_891_ = lean_uint64_xor(v___x_888_, v___x_890_);
v___x_892_ = 16ULL;
v___x_893_ = lean_uint64_shift_right(v_fold_891_, v___x_892_);
v___x_894_ = lean_uint64_xor(v_fold_891_, v___x_893_);
v___x_895_ = lean_uint64_to_usize(v___x_894_);
v___x_896_ = lean_usize_of_nat(v___x_887_);
v___x_897_ = ((size_t)1ULL);
v___x_898_ = lean_usize_sub(v___x_896_, v___x_897_);
v___x_899_ = lean_usize_land(v___x_895_, v___x_898_);
v___x_900_ = lean_array_uget_borrowed(v_x_879_, v___x_899_);
lean_inc(v___x_900_);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 2, v___x_900_);
v___x_902_ = v___x_885_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_key_881_);
lean_ctor_set(v_reuseFailAlloc_905_, 1, v_value_882_);
lean_ctor_set(v_reuseFailAlloc_905_, 2, v___x_900_);
v___x_902_ = v_reuseFailAlloc_905_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
lean_object* v___x_903_; 
v___x_903_ = lean_array_uset(v_x_879_, v___x_899_, v___x_902_);
v_x_879_ = v___x_903_;
v_x_880_ = v_tail_883_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_i_907_, lean_object* v_source_908_, lean_object* v_target_909_){
_start:
{
lean_object* v___x_910_; uint8_t v___x_911_; 
v___x_910_ = lean_array_get_size(v_source_908_);
v___x_911_ = lean_nat_dec_lt(v_i_907_, v___x_910_);
if (v___x_911_ == 0)
{
lean_dec_ref(v_source_908_);
lean_dec(v_i_907_);
return v_target_909_;
}
else
{
lean_object* v_es_912_; lean_object* v___x_913_; lean_object* v_source_914_; lean_object* v_target_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v_es_912_ = lean_array_fget(v_source_908_, v_i_907_);
v___x_913_ = lean_box(0);
v_source_914_ = lean_array_fset(v_source_908_, v_i_907_, v___x_913_);
v_target_915_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_target_909_, v_es_912_);
v___x_916_ = lean_unsigned_to_nat(1u);
v___x_917_ = lean_nat_add(v_i_907_, v___x_916_);
lean_dec(v_i_907_);
v_i_907_ = v___x_917_;
v_source_908_ = v_source_914_;
v_target_909_ = v_target_915_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2___redArg(lean_object* v_data_919_){
_start:
{
lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v_nbuckets_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_920_ = lean_array_get_size(v_data_919_);
v___x_921_ = lean_unsigned_to_nat(2u);
v_nbuckets_922_ = lean_nat_mul(v___x_920_, v___x_921_);
v___x_923_ = lean_unsigned_to_nat(0u);
v___x_924_ = lean_box(0);
v___x_925_ = lean_mk_array(v_nbuckets_922_, v___x_924_);
v___x_926_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2_spec__3___redArg(v___x_923_, v_data_919_, v___x_925_);
return v___x_926_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1___redArg(lean_object* v_a_927_, lean_object* v_x_928_){
_start:
{
if (lean_obj_tag(v_x_928_) == 0)
{
uint8_t v___x_929_; 
v___x_929_ = 0;
return v___x_929_;
}
else
{
lean_object* v_key_930_; lean_object* v_tail_931_; uint8_t v___x_932_; 
v_key_930_ = lean_ctor_get(v_x_928_, 0);
v_tail_931_ = lean_ctor_get(v_x_928_, 2);
v___x_932_ = lean_string_dec_eq(v_key_930_, v_a_927_);
if (v___x_932_ == 0)
{
v_x_928_ = v_tail_931_;
goto _start;
}
else
{
return v___x_932_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_a_934_, lean_object* v_x_935_){
_start:
{
uint8_t v_res_936_; lean_object* v_r_937_; 
v_res_936_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1___redArg(v_a_934_, v_x_935_);
lean_dec(v_x_935_);
lean_dec_ref(v_a_934_);
v_r_937_ = lean_box(v_res_936_);
return v_r_937_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0(lean_object* v_i_938_, lean_object* v_m_939_, lean_object* v_a_940_){
_start:
{
lean_object* v_size_941_; lean_object* v_buckets_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_992_; 
v_size_941_ = lean_ctor_get(v_m_939_, 0);
v_buckets_942_ = lean_ctor_get(v_m_939_, 1);
v_isSharedCheck_992_ = !lean_is_exclusive(v_m_939_);
if (v_isSharedCheck_992_ == 0)
{
v___x_944_ = v_m_939_;
v_isShared_945_ = v_isSharedCheck_992_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_buckets_942_);
lean_inc(v_size_941_);
lean_dec(v_m_939_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_992_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_946_; uint64_t v___x_947_; uint64_t v___x_948_; uint64_t v___x_949_; uint64_t v_fold_950_; uint64_t v___x_951_; uint64_t v___x_952_; uint64_t v___x_953_; size_t v___x_954_; size_t v___x_955_; size_t v___x_956_; size_t v___x_957_; size_t v___x_958_; lean_object* v_bkt_959_; uint8_t v___x_960_; 
v___x_946_ = lean_array_get_size(v_buckets_942_);
v___x_947_ = lean_string_hash(v_a_940_);
v___x_948_ = 32ULL;
v___x_949_ = lean_uint64_shift_right(v___x_947_, v___x_948_);
v_fold_950_ = lean_uint64_xor(v___x_947_, v___x_949_);
v___x_951_ = 16ULL;
v___x_952_ = lean_uint64_shift_right(v_fold_950_, v___x_951_);
v___x_953_ = lean_uint64_xor(v_fold_950_, v___x_952_);
v___x_954_ = lean_uint64_to_usize(v___x_953_);
v___x_955_ = lean_usize_of_nat(v___x_946_);
v___x_956_ = ((size_t)1ULL);
v___x_957_ = lean_usize_sub(v___x_955_, v___x_956_);
v___x_958_ = lean_usize_land(v___x_954_, v___x_957_);
v_bkt_959_ = lean_array_uget_borrowed(v_buckets_942_, v___x_958_);
v___x_960_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1___redArg(v_a_940_, v_bkt_959_);
if (v___x_960_ == 0)
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v_size_x27_964_; lean_object* v___x_965_; lean_object* v_buckets_x27_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; uint8_t v___x_972_; 
v___x_961_ = lean_unsigned_to_nat(1u);
v___x_962_ = lean_mk_empty_array_with_capacity(v___x_961_);
v___x_963_ = lean_array_push(v___x_962_, v_i_938_);
v_size_x27_964_ = lean_nat_add(v_size_941_, v___x_961_);
lean_dec(v_size_941_);
lean_inc(v_bkt_959_);
v___x_965_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_965_, 0, v_a_940_);
lean_ctor_set(v___x_965_, 1, v___x_963_);
lean_ctor_set(v___x_965_, 2, v_bkt_959_);
v_buckets_x27_966_ = lean_array_uset(v_buckets_942_, v___x_958_, v___x_965_);
v___x_967_ = lean_unsigned_to_nat(4u);
v___x_968_ = lean_nat_mul(v_size_x27_964_, v___x_967_);
v___x_969_ = lean_unsigned_to_nat(3u);
v___x_970_ = lean_nat_div(v___x_968_, v___x_969_);
lean_dec(v___x_968_);
v___x_971_ = lean_array_get_size(v_buckets_x27_966_);
v___x_972_ = lean_nat_dec_le(v___x_970_, v___x_971_);
lean_dec(v___x_970_);
if (v___x_972_ == 0)
{
lean_object* v_val_973_; lean_object* v___x_975_; 
v_val_973_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2___redArg(v_buckets_x27_966_);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 1, v_val_973_);
lean_ctor_set(v___x_944_, 0, v_size_x27_964_);
v___x_975_ = v___x_944_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_size_x27_964_);
lean_ctor_set(v_reuseFailAlloc_976_, 1, v_val_973_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
else
{
lean_object* v___x_978_; 
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 1, v_buckets_x27_966_);
lean_ctor_set(v___x_944_, 0, v_size_x27_964_);
v___x_978_ = v___x_944_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_size_x27_964_);
lean_ctor_set(v_reuseFailAlloc_979_, 1, v_buckets_x27_966_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
else
{
lean_object* v___x_980_; lean_object* v_buckets_x27_981_; lean_object* v_bkt_x27_982_; lean_object* v___y_984_; uint8_t v___x_989_; 
lean_inc(v_bkt_959_);
v___x_980_ = lean_box(0);
v_buckets_x27_981_ = lean_array_uset(v_buckets_942_, v___x_958_, v___x_980_);
lean_inc_ref(v_a_940_);
v_bkt_x27_982_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__3(v_i_938_, v_a_940_, v_bkt_959_);
v___x_989_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1___redArg(v_a_940_, v_bkt_x27_982_);
lean_dec_ref(v_a_940_);
if (v___x_989_ == 0)
{
lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_990_ = lean_unsigned_to_nat(1u);
v___x_991_ = lean_nat_sub(v_size_941_, v___x_990_);
lean_dec(v_size_941_);
v___y_984_ = v___x_991_;
goto v___jp_983_;
}
else
{
v___y_984_ = v_size_941_;
goto v___jp_983_;
}
v___jp_983_:
{
lean_object* v___x_985_; lean_object* v___x_987_; 
v___x_985_ = lean_array_uset(v_buckets_x27_981_, v___x_958_, v_bkt_x27_982_);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 1, v___x_985_);
lean_ctor_set(v___x_944_, 0, v___y_984_);
v___x_987_ = v___x_944_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v___y_984_);
lean_ctor_set(v_reuseFailAlloc_988_, 1, v___x_985_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1___redArg(lean_object* v_x_993_, lean_object* v_x_994_){
_start:
{
if (lean_obj_tag(v_x_994_) == 0)
{
return v_x_993_;
}
else
{
lean_object* v_head_995_; lean_object* v_tail_996_; lean_object* v_fst_997_; lean_object* v_entries_998_; lean_object* v_indexes_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1010_; 
v_head_995_ = lean_ctor_get(v_x_994_, 0);
lean_inc(v_head_995_);
v_tail_996_ = lean_ctor_get(v_x_994_, 1);
lean_inc(v_tail_996_);
lean_dec_ref_known(v_x_994_, 2);
v_fst_997_ = lean_ctor_get(v_head_995_, 0);
lean_inc(v_fst_997_);
v_entries_998_ = lean_ctor_get(v_x_993_, 0);
v_indexes_999_ = lean_ctor_get(v_x_993_, 1);
v_isSharedCheck_1010_ = !lean_is_exclusive(v_x_993_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1001_ = v_x_993_;
v_isShared_1002_ = v_isSharedCheck_1010_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_indexes_999_);
lean_inc(v_entries_998_);
lean_dec(v_x_993_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1010_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v_i_1003_; lean_object* v_entries_1004_; lean_object* v_indexes_1005_; lean_object* v___x_1007_; 
v_i_1003_ = lean_array_get_size(v_entries_998_);
v_entries_1004_ = lean_array_push(v_entries_998_, v_head_995_);
v_indexes_1005_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0(v_i_1003_, v_indexes_999_, v_fst_997_);
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 1, v_indexes_1005_);
lean_ctor_set(v___x_1001_, 0, v_entries_1004_);
v___x_1007_ = v___x_1001_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_entries_1004_);
lean_ctor_set(v_reuseFailAlloc_1009_, 1, v_indexes_1005_);
v___x_1007_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
v_x_993_ = v___x_1007_;
v_x_994_ = v_tail_996_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1011_; 
v___x_1011_ = l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0(lean_box(0));
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0___redArg(lean_object* v_pairs_1012_){
_start:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1013_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0___redArg___closed__0, &l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0___redArg___closed__0_once, _init_l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0___redArg___closed__0);
v___x_1014_ = l_List_foldl___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1___redArg(v___x_1013_, v_pairs_1012_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_ofList(lean_object* v_pairs_1015_){
_start:
{
lean_object* v___x_1016_; 
v___x_1016_ = l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0___redArg(v_pairs_1015_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0(lean_object* v_00_u03b2_1017_, lean_object* v_inst_1018_, lean_object* v_inst_1019_, lean_object* v_pairs_1020_){
_start:
{
lean_object* v___x_1021_; 
v___x_1021_ = l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0___redArg(v_pairs_1020_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1(lean_object* v_00_u03b2_1022_, lean_object* v_x_1023_, lean_object* v_x_1024_){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = l_List_foldl___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1___redArg(v_x_1023_, v_x_1024_);
return v___x_1025_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1026_, lean_object* v_a_1027_, lean_object* v_x_1028_){
_start:
{
uint8_t v___x_1029_; 
v___x_1029_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1___redArg(v_a_1027_, v_x_1028_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1030_, lean_object* v_a_1031_, lean_object* v_x_1032_){
_start:
{
uint8_t v_res_1033_; lean_object* v_r_1034_; 
v_res_1033_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1(v_00_u03b2_1030_, v_a_1031_, v_x_1032_);
lean_dec(v_x_1032_);
lean_dec_ref(v_a_1031_);
v_r_1034_ = lean_box(v_res_1033_);
return v_r_1034_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1035_, lean_object* v_data_1036_){
_start:
{
lean_object* v___x_1037_; 
v___x_1037_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2___redArg(v_data_1036_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_1038_, lean_object* v_i_1039_, lean_object* v_source_1040_, lean_object* v_target_1041_){
_start:
{
lean_object* v___x_1042_; 
v___x_1042_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2_spec__3___redArg(v_i_1039_, v_source_1040_, v_target_1041_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_1043_, lean_object* v_x_1044_, lean_object* v_x_1045_){
_start:
{
lean_object* v___x_1046_; 
v___x_1046_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_x_1044_, v_x_1045_);
return v___x_1046_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Headers_contains(lean_object* v_headers_1047_, lean_object* v_name_1048_){
_start:
{
lean_object* v_indexes_1049_; lean_object* v___f_1050_; lean_object* v___f_1051_; uint8_t v___x_1052_; 
v_indexes_1049_ = lean_ctor_get(v_headers_1047_, 1);
v___f_1050_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_1051_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v___x_1052_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_1050_, v___f_1051_, v_indexes_1049_, v_name_1048_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_contains___boxed(lean_object* v_headers_1053_, lean_object* v_name_1054_){
_start:
{
uint8_t v_res_1055_; lean_object* v_r_1056_; 
v_res_1055_ = l_Std_Http_Headers_contains(v_headers_1053_, v_name_1054_);
lean_dec_ref(v_headers_1053_);
v_r_1056_ = lean_box(v_res_1055_);
return v_r_1056_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_erase___lam__1(lean_object* v___f_1057_, lean_object* v___f_1058_, lean_object* v_x1_1059_, lean_object* v_x2_1060_){
_start:
{
lean_object* v_fst_1061_; lean_object* v_entries_1062_; lean_object* v_indexes_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1074_; 
v_fst_1061_ = lean_ctor_get(v_x2_1060_, 0);
lean_inc(v_fst_1061_);
v_entries_1062_ = lean_ctor_get(v_x1_1059_, 0);
v_indexes_1063_ = lean_ctor_get(v_x1_1059_, 1);
v_isSharedCheck_1074_ = !lean_is_exclusive(v_x1_1059_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1065_ = v_x1_1059_;
v_isShared_1066_ = v_isSharedCheck_1074_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_indexes_1063_);
lean_inc(v_entries_1062_);
lean_dec(v_x1_1059_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1074_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v_i_1067_; lean_object* v_f_1068_; lean_object* v_entries_1069_; lean_object* v_indexes_1070_; lean_object* v___x_1072_; 
v_i_1067_ = lean_array_get_size(v_entries_1062_);
v_f_1068_ = lean_alloc_closure((void*)(l_Std_Http_Headers_insert___lam__0), 2, 1);
lean_closure_set(v_f_1068_, 0, v_i_1067_);
v_entries_1069_ = lean_array_push(v_entries_1062_, v_x2_1060_);
v_indexes_1070_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_1057_, v___f_1058_, v_indexes_1063_, v_fst_1061_, v_f_1068_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 1, v_indexes_1070_);
lean_ctor_set(v___x_1065_, 0, v_entries_1069_);
v___x_1072_ = v___x_1065_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v_entries_1069_);
lean_ctor_set(v_reuseFailAlloc_1073_, 1, v_indexes_1070_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_erase___lam__0(lean_object* v_name_1075_, lean_object* v_x1_1076_, lean_object* v_x2_1077_){
_start:
{
lean_object* v_fst_1078_; uint8_t v___x_1079_; uint8_t v___x_1080_; 
v_fst_1078_ = lean_ctor_get(v_x2_1077_, 0);
v___x_1079_ = lean_string_dec_eq(v_fst_1078_, v_name_1075_);
v___x_1080_ = lean_bool_not(v___x_1079_);
if (v___x_1080_ == 0)
{
lean_dec_ref(v_x2_1077_);
return v_x1_1076_;
}
else
{
lean_object* v___x_1081_; 
v___x_1081_ = lean_array_push(v_x1_1076_, v_x2_1077_);
return v___x_1081_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_erase___lam__0___boxed(lean_object* v_name_1082_, lean_object* v_x1_1083_, lean_object* v_x2_1084_){
_start:
{
lean_object* v_res_1085_; 
v_res_1085_ = l_Std_Http_Headers_erase___lam__0(v_name_1082_, v_x1_1083_, v_x2_1084_);
lean_dec_ref(v_name_1082_);
return v_res_1085_;
}
}
static lean_object* _init_l_Std_Http_Headers_erase___closed__1(void){
_start:
{
lean_object* v___f_1089_; lean_object* v___f_1090_; lean_object* v___x_1091_; 
v___f_1089_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v___f_1090_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___x_1091_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v___f_1090_, v___f_1089_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_erase(lean_object* v_headers_1092_, lean_object* v_name_1093_){
_start:
{
lean_object* v___f_1094_; lean_object* v___f_1095_; uint8_t v___x_1096_; 
v___f_1094_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_1095_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
lean_inc_ref(v_name_1093_);
v___x_1096_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_1094_, v___f_1095_, v_name_1093_, v_headers_1092_);
if (v___x_1096_ == 0)
{
lean_dec_ref(v_name_1093_);
return v_headers_1092_;
}
else
{
lean_object* v_entries_1097_; lean_object* v___f_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___y_1102_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; uint8_t v___x_1116_; 
v_entries_1097_ = lean_ctor_get(v_headers_1092_, 0);
lean_inc_ref(v_entries_1097_);
lean_dec_ref(v_headers_1092_);
v___f_1098_ = ((lean_object*)(l_Std_Http_Headers_erase___closed__0));
v___x_1099_ = lean_obj_once(&l_Std_Http_Headers_erase___closed__1, &l_Std_Http_Headers_erase___closed__1_once, _init_l_Std_Http_Headers_erase___closed__1);
v___x_1100_ = lean_unsigned_to_nat(0u);
v___x_1113_ = lean_array_get_size(v_entries_1097_);
v___x_1114_ = ((lean_object*)(l_Std_Http_instInhabitedHeaders_default___closed__0));
v___x_1115_ = ((lean_object*)(l_Std_Http_Headers_getAll___redArg___closed__9));
v___x_1116_ = lean_nat_dec_lt(v___x_1100_, v___x_1113_);
if (v___x_1116_ == 0)
{
lean_dec_ref(v_entries_1097_);
lean_dec_ref(v_name_1093_);
v___y_1102_ = v___x_1114_;
goto v___jp_1101_;
}
else
{
lean_object* v___f_1117_; uint8_t v___x_1118_; 
v___f_1117_ = lean_alloc_closure((void*)(l_Std_Http_Headers_erase___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1117_, 0, v_name_1093_);
v___x_1118_ = lean_nat_dec_le(v___x_1113_, v___x_1113_);
if (v___x_1118_ == 0)
{
if (v___x_1116_ == 0)
{
lean_dec_ref(v___f_1117_);
lean_dec_ref(v_entries_1097_);
v___y_1102_ = v___x_1114_;
goto v___jp_1101_;
}
else
{
size_t v___x_1119_; size_t v___x_1120_; lean_object* v___x_1121_; 
v___x_1119_ = ((size_t)0ULL);
v___x_1120_ = lean_usize_of_nat(v___x_1113_);
v___x_1121_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1115_, v___f_1117_, v_entries_1097_, v___x_1119_, v___x_1120_, v___x_1114_);
v___y_1102_ = v___x_1121_;
goto v___jp_1101_;
}
}
else
{
size_t v___x_1122_; size_t v___x_1123_; lean_object* v___x_1124_; 
v___x_1122_ = ((size_t)0ULL);
v___x_1123_ = lean_usize_of_nat(v___x_1113_);
v___x_1124_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1115_, v___f_1117_, v_entries_1097_, v___x_1122_, v___x_1123_, v___x_1114_);
v___y_1102_ = v___x_1124_;
goto v___jp_1101_;
}
}
v___jp_1101_:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; uint8_t v___x_1105_; 
v___x_1103_ = lean_array_get_size(v___y_1102_);
v___x_1104_ = ((lean_object*)(l_Std_Http_Headers_getAll___redArg___closed__9));
v___x_1105_ = lean_nat_dec_lt(v___x_1100_, v___x_1103_);
if (v___x_1105_ == 0)
{
lean_dec_ref(v___y_1102_);
return v___x_1099_;
}
else
{
uint8_t v___x_1106_; 
v___x_1106_ = lean_nat_dec_le(v___x_1103_, v___x_1103_);
if (v___x_1106_ == 0)
{
if (v___x_1105_ == 0)
{
lean_dec_ref(v___y_1102_);
return v___x_1099_;
}
else
{
size_t v___x_1107_; size_t v___x_1108_; lean_object* v___x_1109_; 
v___x_1107_ = ((size_t)0ULL);
v___x_1108_ = lean_usize_of_nat(v___x_1103_);
v___x_1109_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1104_, v___f_1098_, v___y_1102_, v___x_1107_, v___x_1108_, v___x_1099_);
return v___x_1109_;
}
}
else
{
size_t v___x_1110_; size_t v___x_1111_; lean_object* v___x_1112_; 
v___x_1110_ = ((size_t)0ULL);
v___x_1111_ = lean_usize_of_nat(v___x_1103_);
v___x_1112_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1104_, v___f_1098_, v___y_1102_, v___x_1110_, v___x_1111_, v___x_1099_);
return v___x_1112_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_size(lean_object* v_headers_1125_){
_start:
{
lean_object* v_entries_1126_; lean_object* v___x_1127_; 
v_entries_1126_ = lean_ctor_get(v_headers_1125_, 0);
v___x_1127_ = lean_array_get_size(v_entries_1126_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_size___boxed(lean_object* v_headers_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_Std_Http_Headers_size(v_headers_1128_);
lean_dec_ref(v_headers_1128_);
return v_res_1129_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Headers_isEmpty(lean_object* v_headers_1130_){
_start:
{
lean_object* v_entries_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; uint8_t v___x_1134_; 
v_entries_1131_ = lean_ctor_get(v_headers_1130_, 0);
v___x_1132_ = lean_array_get_size(v_entries_1131_);
v___x_1133_ = lean_unsigned_to_nat(0u);
v___x_1134_ = lean_nat_dec_eq(v___x_1132_, v___x_1133_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_isEmpty___boxed(lean_object* v_headers_1135_){
_start:
{
uint8_t v_res_1136_; lean_object* v_r_1137_; 
v_res_1136_ = l_Std_Http_Headers_isEmpty(v_headers_1135_);
lean_dec_ref(v_headers_1135_);
v_r_1137_ = lean_box(v_res_1136_);
return v_r_1137_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___redArg(lean_object* v_as_1138_, size_t v_i_1139_, size_t v_stop_1140_, lean_object* v_b_1141_){
_start:
{
uint8_t v___x_1142_; 
v___x_1142_ = lean_usize_dec_eq(v_i_1139_, v_stop_1140_);
if (v___x_1142_ == 0)
{
lean_object* v___x_1143_; lean_object* v_fst_1144_; lean_object* v_entries_1145_; lean_object* v_indexes_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1159_; 
v___x_1143_ = lean_array_uget_borrowed(v_as_1138_, v_i_1139_);
v_fst_1144_ = lean_ctor_get(v___x_1143_, 0);
v_entries_1145_ = lean_ctor_get(v_b_1141_, 0);
v_indexes_1146_ = lean_ctor_get(v_b_1141_, 1);
v_isSharedCheck_1159_ = !lean_is_exclusive(v_b_1141_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1148_ = v_b_1141_;
v_isShared_1149_ = v_isSharedCheck_1159_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_indexes_1146_);
lean_inc(v_entries_1145_);
lean_dec(v_b_1141_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1159_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v_i_1150_; lean_object* v_entries_1151_; lean_object* v_indexes_1152_; lean_object* v___x_1154_; 
v_i_1150_ = lean_array_get_size(v_entries_1145_);
lean_inc(v___x_1143_);
v_entries_1151_ = lean_array_push(v_entries_1145_, v___x_1143_);
lean_inc(v_fst_1144_);
v_indexes_1152_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0(v_i_1150_, v_indexes_1146_, v_fst_1144_);
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 1, v_indexes_1152_);
lean_ctor_set(v___x_1148_, 0, v_entries_1151_);
v___x_1154_ = v___x_1148_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_entries_1151_);
lean_ctor_set(v_reuseFailAlloc_1158_, 1, v_indexes_1152_);
v___x_1154_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
size_t v___x_1155_; size_t v___x_1156_; 
v___x_1155_ = ((size_t)1ULL);
v___x_1156_ = lean_usize_add(v_i_1139_, v___x_1155_);
v_i_1139_ = v___x_1156_;
v_b_1141_ = v___x_1154_;
goto _start;
}
}
}
else
{
return v_b_1141_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___redArg___boxed(lean_object* v_as_1160_, lean_object* v_i_1161_, lean_object* v_stop_1162_, lean_object* v_b_1163_){
_start:
{
size_t v_i_boxed_1164_; size_t v_stop_boxed_1165_; lean_object* v_res_1166_; 
v_i_boxed_1164_ = lean_unbox_usize(v_i_1161_);
lean_dec(v_i_1161_);
v_stop_boxed_1165_ = lean_unbox_usize(v_stop_1162_);
lean_dec(v_stop_1162_);
v_res_1166_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___redArg(v_as_1160_, v_i_boxed_1164_, v_stop_boxed_1165_, v_b_1163_);
lean_dec_ref(v_as_1160_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0___redArg(lean_object* v_m1_1167_, lean_object* v_m2_1168_){
_start:
{
lean_object* v_entries_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; uint8_t v___x_1172_; 
v_entries_1169_ = lean_ctor_get(v_m2_1168_, 0);
v___x_1170_ = lean_unsigned_to_nat(0u);
v___x_1171_ = lean_array_get_size(v_entries_1169_);
v___x_1172_ = lean_nat_dec_lt(v___x_1170_, v___x_1171_);
if (v___x_1172_ == 0)
{
return v_m1_1167_;
}
else
{
uint8_t v___x_1173_; 
v___x_1173_ = lean_nat_dec_le(v___x_1171_, v___x_1171_);
if (v___x_1173_ == 0)
{
if (v___x_1172_ == 0)
{
return v_m1_1167_;
}
else
{
size_t v___x_1174_; size_t v___x_1175_; lean_object* v___x_1176_; 
v___x_1174_ = ((size_t)0ULL);
v___x_1175_ = lean_usize_of_nat(v___x_1171_);
v___x_1176_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___redArg(v_entries_1169_, v___x_1174_, v___x_1175_, v_m1_1167_);
return v___x_1176_;
}
}
else
{
size_t v___x_1177_; size_t v___x_1178_; lean_object* v___x_1179_; 
v___x_1177_ = ((size_t)0ULL);
v___x_1178_ = lean_usize_of_nat(v___x_1171_);
v___x_1179_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___redArg(v_entries_1169_, v___x_1177_, v___x_1178_, v_m1_1167_);
return v___x_1179_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0___redArg___boxed(lean_object* v_m1_1180_, lean_object* v_m2_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0___redArg(v_m1_1180_, v_m2_1181_);
lean_dec_ref(v_m2_1181_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_merge(lean_object* v_headers1_1183_, lean_object* v_headers2_1184_){
_start:
{
lean_object* v___x_1185_; 
v___x_1185_ = l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0___redArg(v_headers1_1183_, v_headers2_1184_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_merge___boxed(lean_object* v_headers1_1186_, lean_object* v_headers2_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l_Std_Http_Headers_merge(v_headers1_1186_, v_headers2_1187_);
lean_dec_ref(v_headers2_1187_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0(lean_object* v_00_u03b2_1189_, lean_object* v_inst_1190_, lean_object* v_inst_1191_, lean_object* v_m1_1192_, lean_object* v_m2_1193_){
_start:
{
lean_object* v___x_1194_; 
v___x_1194_ = l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0___redArg(v_m1_1192_, v_m2_1193_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0___boxed(lean_object* v_00_u03b2_1195_, lean_object* v_inst_1196_, lean_object* v_inst_1197_, lean_object* v_m1_1198_, lean_object* v_m2_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0(v_00_u03b2_1195_, v_inst_1196_, v_inst_1197_, v_m1_1198_, v_m2_1199_);
lean_dec_ref(v_m2_1199_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0(lean_object* v_00_u03b2_1201_, lean_object* v_as_1202_, size_t v_i_1203_, size_t v_stop_1204_, lean_object* v_b_1205_){
_start:
{
lean_object* v___x_1206_; 
v___x_1206_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___redArg(v_as_1202_, v_i_1203_, v_stop_1204_, v_b_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1207_, lean_object* v_as_1208_, lean_object* v_i_1209_, lean_object* v_stop_1210_, lean_object* v_b_1211_){
_start:
{
size_t v_i_boxed_1212_; size_t v_stop_boxed_1213_; lean_object* v_res_1214_; 
v_i_boxed_1212_ = lean_unbox_usize(v_i_1209_);
lean_dec(v_i_1209_);
v_stop_boxed_1213_ = lean_unbox_usize(v_stop_1210_);
lean_dec(v_stop_1210_);
v_res_1214_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0(v_00_u03b2_1207_, v_as_1208_, v_i_boxed_1212_, v_stop_boxed_1213_, v_b_1211_);
lean_dec_ref(v_as_1208_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toList___at___00Std_Http_Headers_toList_spec__0___redArg(lean_object* v_map_1215_){
_start:
{
lean_object* v_entries_1216_; lean_object* v___x_1217_; 
v_entries_1216_ = lean_ctor_get(v_map_1215_, 0);
lean_inc_ref(v_entries_1216_);
lean_dec_ref(v_map_1215_);
v___x_1217_ = lean_array_to_list(v_entries_1216_);
return v___x_1217_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toList___at___00Std_Http_Headers_toList_spec__0(lean_object* v_00_u03b2_1218_, lean_object* v_map_1219_){
_start:
{
lean_object* v___x_1220_; 
v___x_1220_ = l_Std_Internal_IndexMultiMap_toList___at___00Std_Http_Headers_toList_spec__0___redArg(v_map_1219_);
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_toList(lean_object* v_headers_1221_){
_start:
{
lean_object* v___x_1222_; 
v___x_1222_ = l_Std_Internal_IndexMultiMap_toList___at___00Std_Http_Headers_toList_spec__0___redArg(v_headers_1221_);
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_toArray(lean_object* v_headers_1223_){
_start:
{
lean_object* v_entries_1224_; 
v_entries_1224_ = lean_ctor_get(v_headers_1223_, 0);
lean_inc_ref(v_entries_1224_);
return v_entries_1224_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_toArray___boxed(lean_object* v_headers_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l_Std_Http_Headers_toArray(v_headers_1225_);
lean_dec_ref(v_headers_1225_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___redArg(lean_object* v_f_1227_, lean_object* v_as_1228_, size_t v_i_1229_, size_t v_stop_1230_, lean_object* v_b_1231_){
_start:
{
uint8_t v___x_1232_; 
v___x_1232_ = lean_usize_dec_eq(v_i_1229_, v_stop_1230_);
if (v___x_1232_ == 0)
{
lean_object* v___x_1233_; lean_object* v_fst_1234_; lean_object* v_snd_1235_; lean_object* v___x_1236_; size_t v___x_1237_; size_t v___x_1238_; 
v___x_1233_ = lean_array_uget_borrowed(v_as_1228_, v_i_1229_);
v_fst_1234_ = lean_ctor_get(v___x_1233_, 0);
v_snd_1235_ = lean_ctor_get(v___x_1233_, 1);
lean_inc(v_f_1227_);
lean_inc(v_snd_1235_);
lean_inc(v_fst_1234_);
v___x_1236_ = lean_apply_3(v_f_1227_, v_b_1231_, v_fst_1234_, v_snd_1235_);
v___x_1237_ = ((size_t)1ULL);
v___x_1238_ = lean_usize_add(v_i_1229_, v___x_1237_);
v_i_1229_ = v___x_1238_;
v_b_1231_ = v___x_1236_;
goto _start;
}
else
{
lean_dec(v_f_1227_);
return v_b_1231_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___redArg___boxed(lean_object* v_f_1240_, lean_object* v_as_1241_, lean_object* v_i_1242_, lean_object* v_stop_1243_, lean_object* v_b_1244_){
_start:
{
size_t v_i_boxed_1245_; size_t v_stop_boxed_1246_; lean_object* v_res_1247_; 
v_i_boxed_1245_ = lean_unbox_usize(v_i_1242_);
lean_dec(v_i_1242_);
v_stop_boxed_1246_ = lean_unbox_usize(v_stop_1243_);
lean_dec(v_stop_1243_);
v_res_1247_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___redArg(v_f_1240_, v_as_1241_, v_i_boxed_1245_, v_stop_boxed_1246_, v_b_1244_);
lean_dec_ref(v_as_1241_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_fold___redArg(lean_object* v_headers_1248_, lean_object* v_init_1249_, lean_object* v_f_1250_){
_start:
{
lean_object* v_entries_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; uint8_t v___x_1254_; 
v_entries_1251_ = lean_ctor_get(v_headers_1248_, 0);
v___x_1252_ = lean_unsigned_to_nat(0u);
v___x_1253_ = lean_array_get_size(v_entries_1251_);
v___x_1254_ = lean_nat_dec_lt(v___x_1252_, v___x_1253_);
if (v___x_1254_ == 0)
{
lean_dec(v_f_1250_);
return v_init_1249_;
}
else
{
uint8_t v___x_1255_; 
v___x_1255_ = lean_nat_dec_le(v___x_1253_, v___x_1253_);
if (v___x_1255_ == 0)
{
if (v___x_1254_ == 0)
{
lean_dec(v_f_1250_);
return v_init_1249_;
}
else
{
size_t v___x_1256_; size_t v___x_1257_; lean_object* v___x_1258_; 
v___x_1256_ = ((size_t)0ULL);
v___x_1257_ = lean_usize_of_nat(v___x_1253_);
v___x_1258_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___redArg(v_f_1250_, v_entries_1251_, v___x_1256_, v___x_1257_, v_init_1249_);
return v___x_1258_;
}
}
else
{
size_t v___x_1259_; size_t v___x_1260_; lean_object* v___x_1261_; 
v___x_1259_ = ((size_t)0ULL);
v___x_1260_ = lean_usize_of_nat(v___x_1253_);
v___x_1261_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___redArg(v_f_1250_, v_entries_1251_, v___x_1259_, v___x_1260_, v_init_1249_);
return v___x_1261_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_fold___redArg___boxed(lean_object* v_headers_1262_, lean_object* v_init_1263_, lean_object* v_f_1264_){
_start:
{
lean_object* v_res_1265_; 
v_res_1265_ = l_Std_Http_Headers_fold___redArg(v_headers_1262_, v_init_1263_, v_f_1264_);
lean_dec_ref(v_headers_1262_);
return v_res_1265_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_fold(lean_object* v_00_u03b1_1266_, lean_object* v_headers_1267_, lean_object* v_init_1268_, lean_object* v_f_1269_){
_start:
{
lean_object* v___x_1270_; 
v___x_1270_ = l_Std_Http_Headers_fold___redArg(v_headers_1267_, v_init_1268_, v_f_1269_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_fold___boxed(lean_object* v_00_u03b1_1271_, lean_object* v_headers_1272_, lean_object* v_init_1273_, lean_object* v_f_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l_Std_Http_Headers_fold(v_00_u03b1_1271_, v_headers_1272_, v_init_1273_, v_f_1274_);
lean_dec_ref(v_headers_1272_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0(lean_object* v_00_u03b1_1276_, lean_object* v_f_1277_, lean_object* v_as_1278_, size_t v_i_1279_, size_t v_stop_1280_, lean_object* v_b_1281_){
_start:
{
lean_object* v___x_1282_; 
v___x_1282_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___redArg(v_f_1277_, v_as_1278_, v_i_1279_, v_stop_1280_, v_b_1281_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___boxed(lean_object* v_00_u03b1_1283_, lean_object* v_f_1284_, lean_object* v_as_1285_, lean_object* v_i_1286_, lean_object* v_stop_1287_, lean_object* v_b_1288_){
_start:
{
size_t v_i_boxed_1289_; size_t v_stop_boxed_1290_; lean_object* v_res_1291_; 
v_i_boxed_1289_ = lean_unbox_usize(v_i_1286_);
lean_dec(v_i_1286_);
v_stop_boxed_1290_ = lean_unbox_usize(v_stop_1287_);
lean_dec(v_stop_1287_);
v_res_1291_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0(v_00_u03b1_1283_, v_f_1284_, v_as_1285_, v_i_boxed_1289_, v_stop_boxed_1290_, v_b_1288_);
lean_dec_ref(v_as_1285_);
return v_res_1291_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Headers_mapValues_spec__0(lean_object* v_f_1292_, size_t v_sz_1293_, size_t v_i_1294_, lean_object* v_bs_1295_){
_start:
{
uint8_t v___x_1296_; 
v___x_1296_ = lean_usize_dec_lt(v_i_1294_, v_sz_1293_);
if (v___x_1296_ == 0)
{
lean_dec_ref(v_f_1292_);
return v_bs_1295_;
}
else
{
lean_object* v_v_1297_; lean_object* v_fst_1298_; lean_object* v_snd_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1313_; 
v_v_1297_ = lean_array_uget(v_bs_1295_, v_i_1294_);
v_fst_1298_ = lean_ctor_get(v_v_1297_, 0);
v_snd_1299_ = lean_ctor_get(v_v_1297_, 1);
v_isSharedCheck_1313_ = !lean_is_exclusive(v_v_1297_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1301_ = v_v_1297_;
v_isShared_1302_ = v_isSharedCheck_1313_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_snd_1299_);
lean_inc(v_fst_1298_);
lean_dec(v_v_1297_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1313_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1303_; lean_object* v_bs_x27_1304_; lean_object* v___x_1305_; lean_object* v___x_1307_; 
v___x_1303_ = lean_unsigned_to_nat(0u);
v_bs_x27_1304_ = lean_array_uset(v_bs_1295_, v_i_1294_, v___x_1303_);
lean_inc_ref(v_f_1292_);
lean_inc(v_fst_1298_);
v___x_1305_ = lean_apply_2(v_f_1292_, v_fst_1298_, v_snd_1299_);
if (v_isShared_1302_ == 0)
{
lean_ctor_set(v___x_1301_, 1, v___x_1305_);
v___x_1307_ = v___x_1301_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_fst_1298_);
lean_ctor_set(v_reuseFailAlloc_1312_, 1, v___x_1305_);
v___x_1307_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
size_t v___x_1308_; size_t v___x_1309_; lean_object* v___x_1310_; 
v___x_1308_ = ((size_t)1ULL);
v___x_1309_ = lean_usize_add(v_i_1294_, v___x_1308_);
v___x_1310_ = lean_array_uset(v_bs_x27_1304_, v_i_1294_, v___x_1307_);
v_i_1294_ = v___x_1309_;
v_bs_1295_ = v___x_1310_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Headers_mapValues_spec__0___boxed(lean_object* v_f_1314_, lean_object* v_sz_1315_, lean_object* v_i_1316_, lean_object* v_bs_1317_){
_start:
{
size_t v_sz_boxed_1318_; size_t v_i_boxed_1319_; lean_object* v_res_1320_; 
v_sz_boxed_1318_ = lean_unbox_usize(v_sz_1315_);
lean_dec(v_sz_1315_);
v_i_boxed_1319_ = lean_unbox_usize(v_i_1316_);
lean_dec(v_i_1316_);
v_res_1320_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Headers_mapValues_spec__0(v_f_1314_, v_sz_boxed_1318_, v_i_boxed_1319_, v_bs_1317_);
return v_res_1320_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_mapValues_spec__1(lean_object* v_as_1321_, size_t v_i_1322_, size_t v_stop_1323_, lean_object* v_b_1324_){
_start:
{
uint8_t v___x_1325_; 
v___x_1325_ = lean_usize_dec_eq(v_i_1322_, v_stop_1323_);
if (v___x_1325_ == 0)
{
lean_object* v___x_1326_; lean_object* v_fst_1327_; lean_object* v_entries_1328_; lean_object* v_indexes_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1342_; 
v___x_1326_ = lean_array_uget_borrowed(v_as_1321_, v_i_1322_);
v_fst_1327_ = lean_ctor_get(v___x_1326_, 0);
v_entries_1328_ = lean_ctor_get(v_b_1324_, 0);
v_indexes_1329_ = lean_ctor_get(v_b_1324_, 1);
v_isSharedCheck_1342_ = !lean_is_exclusive(v_b_1324_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1331_ = v_b_1324_;
v_isShared_1332_ = v_isSharedCheck_1342_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_indexes_1329_);
lean_inc(v_entries_1328_);
lean_dec(v_b_1324_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1342_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v_i_1333_; lean_object* v_entries_1334_; lean_object* v_indexes_1335_; lean_object* v___x_1337_; 
v_i_1333_ = lean_array_get_size(v_entries_1328_);
lean_inc(v___x_1326_);
v_entries_1334_ = lean_array_push(v_entries_1328_, v___x_1326_);
lean_inc(v_fst_1327_);
v_indexes_1335_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0(v_i_1333_, v_indexes_1329_, v_fst_1327_);
if (v_isShared_1332_ == 0)
{
lean_ctor_set(v___x_1331_, 1, v_indexes_1335_);
lean_ctor_set(v___x_1331_, 0, v_entries_1334_);
v___x_1337_ = v___x_1331_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_entries_1334_);
lean_ctor_set(v_reuseFailAlloc_1341_, 1, v_indexes_1335_);
v___x_1337_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
size_t v___x_1338_; size_t v___x_1339_; 
v___x_1338_ = ((size_t)1ULL);
v___x_1339_ = lean_usize_add(v_i_1322_, v___x_1338_);
v_i_1322_ = v___x_1339_;
v_b_1324_ = v___x_1337_;
goto _start;
}
}
}
else
{
return v_b_1324_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_mapValues_spec__1___boxed(lean_object* v_as_1343_, lean_object* v_i_1344_, lean_object* v_stop_1345_, lean_object* v_b_1346_){
_start:
{
size_t v_i_boxed_1347_; size_t v_stop_boxed_1348_; lean_object* v_res_1349_; 
v_i_boxed_1347_ = lean_unbox_usize(v_i_1344_);
lean_dec(v_i_1344_);
v_stop_boxed_1348_ = lean_unbox_usize(v_stop_1345_);
lean_dec(v_stop_1345_);
v_res_1349_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_mapValues_spec__1(v_as_1343_, v_i_boxed_1347_, v_stop_boxed_1348_, v_b_1346_);
lean_dec_ref(v_as_1343_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_mapValues(lean_object* v_headers_1350_, lean_object* v_f_1351_){
_start:
{
lean_object* v_entries_1352_; size_t v_sz_1353_; size_t v___x_1354_; lean_object* v_pairs_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; uint8_t v___x_1359_; 
v_entries_1352_ = lean_ctor_get(v_headers_1350_, 0);
lean_inc_ref(v_entries_1352_);
lean_dec_ref(v_headers_1350_);
v_sz_1353_ = lean_array_size(v_entries_1352_);
v___x_1354_ = ((size_t)0ULL);
v_pairs_1355_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Headers_mapValues_spec__0(v_f_1351_, v_sz_1353_, v___x_1354_, v_entries_1352_);
v___x_1356_ = lean_obj_once(&l_Std_Http_Headers_empty___closed__0, &l_Std_Http_Headers_empty___closed__0_once, _init_l_Std_Http_Headers_empty___closed__0);
v___x_1357_ = lean_unsigned_to_nat(0u);
v___x_1358_ = lean_array_get_size(v_pairs_1355_);
v___x_1359_ = lean_nat_dec_lt(v___x_1357_, v___x_1358_);
if (v___x_1359_ == 0)
{
lean_dec_ref(v_pairs_1355_);
return v___x_1356_;
}
else
{
uint8_t v___x_1360_; 
v___x_1360_ = lean_nat_dec_le(v___x_1358_, v___x_1358_);
if (v___x_1360_ == 0)
{
if (v___x_1359_ == 0)
{
lean_dec_ref(v_pairs_1355_);
return v___x_1356_;
}
else
{
size_t v___x_1361_; lean_object* v___x_1362_; 
v___x_1361_ = lean_usize_of_nat(v___x_1358_);
v___x_1362_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_mapValues_spec__1(v_pairs_1355_, v___x_1354_, v___x_1361_, v___x_1356_);
lean_dec_ref(v_pairs_1355_);
return v___x_1362_;
}
}
else
{
size_t v___x_1363_; lean_object* v___x_1364_; 
v___x_1363_ = lean_usize_of_nat(v___x_1358_);
v___x_1364_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_mapValues_spec__1(v_pairs_1355_, v___x_1354_, v___x_1363_, v___x_1356_);
lean_dec_ref(v_pairs_1355_);
return v___x_1364_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0_spec__0(lean_object* v_f_1365_, lean_object* v_as_1366_, size_t v_i_1367_, size_t v_stop_1368_, lean_object* v_b_1369_){
_start:
{
lean_object* v___y_1371_; uint8_t v___x_1375_; 
v___x_1375_ = lean_usize_dec_eq(v_i_1367_, v_stop_1368_);
if (v___x_1375_ == 0)
{
lean_object* v___x_1376_; lean_object* v_fst_1377_; lean_object* v_snd_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1388_; 
v___x_1376_ = lean_array_uget(v_as_1366_, v_i_1367_);
v_fst_1377_ = lean_ctor_get(v___x_1376_, 0);
v_snd_1378_ = lean_ctor_get(v___x_1376_, 1);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1380_ = v___x_1376_;
v_isShared_1381_ = v_isSharedCheck_1388_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_snd_1378_);
lean_inc(v_fst_1377_);
lean_dec(v___x_1376_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1388_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1382_; 
lean_inc_ref(v_f_1365_);
lean_inc(v_fst_1377_);
v___x_1382_ = lean_apply_2(v_f_1365_, v_fst_1377_, v_snd_1378_);
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_del_object(v___x_1380_);
lean_dec(v_fst_1377_);
v___y_1371_ = v_b_1369_;
goto v___jp_1370_;
}
else
{
lean_object* v_val_1383_; lean_object* v___x_1385_; 
v_val_1383_ = lean_ctor_get(v___x_1382_, 0);
lean_inc(v_val_1383_);
lean_dec_ref_known(v___x_1382_, 1);
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 1, v_val_1383_);
v___x_1385_ = v___x_1380_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_fst_1377_);
lean_ctor_set(v_reuseFailAlloc_1387_, 1, v_val_1383_);
v___x_1385_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
lean_object* v___x_1386_; 
v___x_1386_ = lean_array_push(v_b_1369_, v___x_1385_);
v___y_1371_ = v___x_1386_;
goto v___jp_1370_;
}
}
}
}
else
{
lean_dec_ref(v_f_1365_);
return v_b_1369_;
}
v___jp_1370_:
{
size_t v___x_1372_; size_t v___x_1373_; 
v___x_1372_ = ((size_t)1ULL);
v___x_1373_ = lean_usize_add(v_i_1367_, v___x_1372_);
v_i_1367_ = v___x_1373_;
v_b_1369_ = v___y_1371_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0_spec__0___boxed(lean_object* v_f_1389_, lean_object* v_as_1390_, lean_object* v_i_1391_, lean_object* v_stop_1392_, lean_object* v_b_1393_){
_start:
{
size_t v_i_boxed_1394_; size_t v_stop_boxed_1395_; lean_object* v_res_1396_; 
v_i_boxed_1394_ = lean_unbox_usize(v_i_1391_);
lean_dec(v_i_1391_);
v_stop_boxed_1395_ = lean_unbox_usize(v_stop_1392_);
lean_dec(v_stop_1392_);
v_res_1396_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0_spec__0(v_f_1389_, v_as_1390_, v_i_boxed_1394_, v_stop_boxed_1395_, v_b_1393_);
lean_dec_ref(v_as_1390_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0(lean_object* v_f_1397_, lean_object* v_as_1398_, lean_object* v_start_1399_, lean_object* v_stop_1400_){
_start:
{
lean_object* v___x_1401_; uint8_t v___x_1402_; 
v___x_1401_ = ((lean_object*)(l_Std_Http_instInhabitedHeaders_default___closed__0));
v___x_1402_ = lean_nat_dec_lt(v_start_1399_, v_stop_1400_);
if (v___x_1402_ == 0)
{
lean_dec_ref(v_f_1397_);
return v___x_1401_;
}
else
{
lean_object* v___x_1403_; uint8_t v___x_1404_; 
v___x_1403_ = lean_array_get_size(v_as_1398_);
v___x_1404_ = lean_nat_dec_le(v_stop_1400_, v___x_1403_);
if (v___x_1404_ == 0)
{
uint8_t v___x_1405_; 
v___x_1405_ = lean_nat_dec_lt(v_start_1399_, v___x_1403_);
if (v___x_1405_ == 0)
{
lean_dec_ref(v_f_1397_);
return v___x_1401_;
}
else
{
size_t v___x_1406_; size_t v___x_1407_; lean_object* v___x_1408_; 
v___x_1406_ = lean_usize_of_nat(v_start_1399_);
v___x_1407_ = lean_usize_of_nat(v___x_1403_);
v___x_1408_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0_spec__0(v_f_1397_, v_as_1398_, v___x_1406_, v___x_1407_, v___x_1401_);
return v___x_1408_;
}
}
else
{
size_t v___x_1409_; size_t v___x_1410_; lean_object* v___x_1411_; 
v___x_1409_ = lean_usize_of_nat(v_start_1399_);
v___x_1410_ = lean_usize_of_nat(v_stop_1400_);
v___x_1411_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0_spec__0(v_f_1397_, v_as_1398_, v___x_1409_, v___x_1410_, v___x_1401_);
return v___x_1411_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0___boxed(lean_object* v_f_1412_, lean_object* v_as_1413_, lean_object* v_start_1414_, lean_object* v_stop_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0(v_f_1412_, v_as_1413_, v_start_1414_, v_stop_1415_);
lean_dec(v_stop_1415_);
lean_dec(v_start_1414_);
lean_dec_ref(v_as_1413_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_filterMap(lean_object* v_headers_1417_, lean_object* v_f_1418_){
_start:
{
lean_object* v_entries_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v_pairs_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; uint8_t v___x_1425_; 
v_entries_1419_ = lean_ctor_get(v_headers_1417_, 0);
v___x_1420_ = lean_unsigned_to_nat(0u);
v___x_1421_ = lean_array_get_size(v_entries_1419_);
v_pairs_1422_ = l_Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0(v_f_1418_, v_entries_1419_, v___x_1420_, v___x_1421_);
v___x_1423_ = lean_obj_once(&l_Std_Http_Headers_empty___closed__0, &l_Std_Http_Headers_empty___closed__0_once, _init_l_Std_Http_Headers_empty___closed__0);
v___x_1424_ = lean_array_get_size(v_pairs_1422_);
v___x_1425_ = lean_nat_dec_lt(v___x_1420_, v___x_1424_);
if (v___x_1425_ == 0)
{
lean_dec_ref(v_pairs_1422_);
return v___x_1423_;
}
else
{
uint8_t v___x_1426_; 
v___x_1426_ = lean_nat_dec_le(v___x_1424_, v___x_1424_);
if (v___x_1426_ == 0)
{
if (v___x_1425_ == 0)
{
lean_dec_ref(v_pairs_1422_);
return v___x_1423_;
}
else
{
size_t v___x_1427_; size_t v___x_1428_; lean_object* v___x_1429_; 
v___x_1427_ = ((size_t)0ULL);
v___x_1428_ = lean_usize_of_nat(v___x_1424_);
v___x_1429_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_mapValues_spec__1(v_pairs_1422_, v___x_1427_, v___x_1428_, v___x_1423_);
lean_dec_ref(v_pairs_1422_);
return v___x_1429_;
}
}
else
{
size_t v___x_1430_; size_t v___x_1431_; lean_object* v___x_1432_; 
v___x_1430_ = ((size_t)0ULL);
v___x_1431_ = lean_usize_of_nat(v___x_1424_);
v___x_1432_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_mapValues_spec__1(v_pairs_1422_, v___x_1430_, v___x_1431_, v___x_1423_);
lean_dec_ref(v_pairs_1422_);
return v___x_1432_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_filterMap___boxed(lean_object* v_headers_1433_, lean_object* v_f_1434_){
_start:
{
lean_object* v_res_1435_; 
v_res_1435_ = l_Std_Http_Headers_filterMap(v_headers_1433_, v_f_1434_);
lean_dec_ref(v_headers_1433_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_filter___lam__0(lean_object* v_f_1436_, lean_object* v_k_1437_, lean_object* v_v_1438_){
_start:
{
lean_object* v___x_1439_; uint8_t v___x_1440_; 
lean_inc_ref(v_v_1438_);
v___x_1439_ = lean_apply_2(v_f_1436_, v_k_1437_, v_v_1438_);
v___x_1440_ = lean_unbox(v___x_1439_);
if (v___x_1440_ == 0)
{
lean_object* v___x_1441_; 
lean_dec_ref(v_v_1438_);
v___x_1441_ = lean_box(0);
return v___x_1441_;
}
else
{
lean_object* v___x_1442_; 
v___x_1442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1442_, 0, v_v_1438_);
return v___x_1442_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_filter(lean_object* v_headers_1443_, lean_object* v_f_1444_){
_start:
{
lean_object* v___f_1445_; lean_object* v___x_1446_; 
v___f_1445_ = lean_alloc_closure((void*)(l_Std_Http_Headers_filter___lam__0), 3, 1);
lean_closure_set(v___f_1445_, 0, v_f_1444_);
v___x_1446_ = l_Std_Http_Headers_filterMap(v_headers_1443_, v___f_1445_);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_filter___boxed(lean_object* v_headers_1447_, lean_object* v_f_1448_){
_start:
{
lean_object* v_res_1449_; 
v_res_1449_ = l_Std_Http_Headers_filter(v_headers_1447_, v_f_1448_);
lean_dec_ref(v_headers_1447_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_update_spec__0(lean_object* v_name_1450_, lean_object* v_f_1451_, lean_object* v_as_1452_, size_t v_i_1453_, size_t v_stop_1454_, lean_object* v_b_1455_){
_start:
{
uint8_t v___x_1456_; 
v___x_1456_ = lean_usize_dec_eq(v_i_1453_, v_stop_1454_);
if (v___x_1456_ == 0)
{
lean_object* v___x_1457_; lean_object* v_fst_1458_; lean_object* v_snd_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1485_; 
v___x_1457_ = lean_array_uget(v_as_1452_, v_i_1453_);
v_fst_1458_ = lean_ctor_get(v___x_1457_, 0);
v_snd_1459_ = lean_ctor_get(v___x_1457_, 1);
v_isSharedCheck_1485_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1461_ = v___x_1457_;
v_isShared_1462_ = v_isSharedCheck_1485_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_snd_1459_);
lean_inc(v_fst_1458_);
lean_dec(v___x_1457_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1485_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___y_1464_; uint8_t v___x_1483_; 
v___x_1483_ = lean_string_dec_eq(v_fst_1458_, v_name_1450_);
if (v___x_1483_ == 0)
{
v___y_1464_ = v_snd_1459_;
goto v___jp_1463_;
}
else
{
lean_object* v___x_1484_; 
lean_inc_ref(v_f_1451_);
v___x_1484_ = lean_apply_1(v_f_1451_, v_snd_1459_);
v___y_1464_ = v___x_1484_;
goto v___jp_1463_;
}
v___jp_1463_:
{
lean_object* v_entries_1465_; lean_object* v_indexes_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1482_; 
v_entries_1465_ = lean_ctor_get(v_b_1455_, 0);
v_indexes_1466_ = lean_ctor_get(v_b_1455_, 1);
v_isSharedCheck_1482_ = !lean_is_exclusive(v_b_1455_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1468_ = v_b_1455_;
v_isShared_1469_ = v_isSharedCheck_1482_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_indexes_1466_);
lean_inc(v_entries_1465_);
lean_dec(v_b_1455_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1482_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v_i_1470_; lean_object* v___x_1472_; 
v_i_1470_ = lean_array_get_size(v_entries_1465_);
lean_inc(v_fst_1458_);
if (v_isShared_1462_ == 0)
{
lean_ctor_set(v___x_1461_, 1, v___y_1464_);
v___x_1472_ = v___x_1461_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v_fst_1458_);
lean_ctor_set(v_reuseFailAlloc_1481_, 1, v___y_1464_);
v___x_1472_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
lean_object* v_entries_1473_; lean_object* v_indexes_1474_; lean_object* v___x_1476_; 
v_entries_1473_ = lean_array_push(v_entries_1465_, v___x_1472_);
v_indexes_1474_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0(v_i_1470_, v_indexes_1466_, v_fst_1458_);
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 1, v_indexes_1474_);
lean_ctor_set(v___x_1468_, 0, v_entries_1473_);
v___x_1476_ = v___x_1468_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_entries_1473_);
lean_ctor_set(v_reuseFailAlloc_1480_, 1, v_indexes_1474_);
v___x_1476_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
size_t v___x_1477_; size_t v___x_1478_; 
v___x_1477_ = ((size_t)1ULL);
v___x_1478_ = lean_usize_add(v_i_1453_, v___x_1477_);
v_i_1453_ = v___x_1478_;
v_b_1455_ = v___x_1476_;
goto _start;
}
}
}
}
}
}
else
{
lean_dec_ref(v_f_1451_);
return v_b_1455_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_update_spec__0___boxed(lean_object* v_name_1486_, lean_object* v_f_1487_, lean_object* v_as_1488_, lean_object* v_i_1489_, lean_object* v_stop_1490_, lean_object* v_b_1491_){
_start:
{
size_t v_i_boxed_1492_; size_t v_stop_boxed_1493_; lean_object* v_res_1494_; 
v_i_boxed_1492_ = lean_unbox_usize(v_i_1489_);
lean_dec(v_i_1489_);
v_stop_boxed_1493_ = lean_unbox_usize(v_stop_1490_);
lean_dec(v_stop_1490_);
v_res_1494_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_update_spec__0(v_name_1486_, v_f_1487_, v_as_1488_, v_i_boxed_1492_, v_stop_boxed_1493_, v_b_1491_);
lean_dec_ref(v_as_1488_);
lean_dec_ref(v_name_1486_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_update(lean_object* v_headers_1495_, lean_object* v_name_1496_, lean_object* v_f_1497_){
_start:
{
lean_object* v___f_1498_; lean_object* v___f_1499_; uint8_t v___x_1500_; 
v___f_1498_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_1499_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
lean_inc_ref(v_name_1496_);
v___x_1500_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_1498_, v___f_1499_, v_name_1496_, v_headers_1495_);
if (v___x_1500_ == 0)
{
lean_dec_ref(v_f_1497_);
lean_dec_ref(v_name_1496_);
lean_inc_ref(v_headers_1495_);
return v_headers_1495_;
}
else
{
lean_object* v_entries_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; uint8_t v___x_1505_; 
v_entries_1501_ = lean_ctor_get(v_headers_1495_, 0);
v___x_1502_ = lean_obj_once(&l_Std_Http_Headers_empty___closed__0, &l_Std_Http_Headers_empty___closed__0_once, _init_l_Std_Http_Headers_empty___closed__0);
v___x_1503_ = lean_unsigned_to_nat(0u);
v___x_1504_ = lean_array_get_size(v_entries_1501_);
v___x_1505_ = lean_nat_dec_lt(v___x_1503_, v___x_1504_);
if (v___x_1505_ == 0)
{
lean_dec_ref(v_f_1497_);
lean_dec_ref(v_name_1496_);
return v___x_1502_;
}
else
{
uint8_t v___x_1506_; 
v___x_1506_ = lean_nat_dec_le(v___x_1504_, v___x_1504_);
if (v___x_1506_ == 0)
{
if (v___x_1505_ == 0)
{
lean_dec_ref(v_f_1497_);
lean_dec_ref(v_name_1496_);
return v___x_1502_;
}
else
{
size_t v___x_1507_; size_t v___x_1508_; lean_object* v___x_1509_; 
v___x_1507_ = ((size_t)0ULL);
v___x_1508_ = lean_usize_of_nat(v___x_1504_);
v___x_1509_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_update_spec__0(v_name_1496_, v_f_1497_, v_entries_1501_, v___x_1507_, v___x_1508_, v___x_1502_);
lean_dec_ref(v_name_1496_);
return v___x_1509_;
}
}
else
{
size_t v___x_1510_; size_t v___x_1511_; lean_object* v___x_1512_; 
v___x_1510_ = ((size_t)0ULL);
v___x_1511_ = lean_usize_of_nat(v___x_1504_);
v___x_1512_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_update_spec__0(v_name_1496_, v_f_1497_, v_entries_1501_, v___x_1510_, v___x_1511_, v___x_1502_);
lean_dec_ref(v_name_1496_);
return v___x_1512_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_update___boxed(lean_object* v_headers_1513_, lean_object* v_name_1514_, lean_object* v_f_1515_){
_start:
{
lean_object* v_res_1516_; 
v_res_1516_ = l_Std_Http_Headers_update(v_headers_1513_, v_name_1514_, v_f_1515_);
lean_dec_ref(v_headers_1513_);
return v_res_1516_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_replaceLast(lean_object* v_headers_1517_, lean_object* v_name_1518_, lean_object* v_value_1519_){
_start:
{
lean_object* v___f_1520_; lean_object* v___f_1521_; uint8_t v___x_1522_; 
v___f_1520_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_1521_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
lean_inc_ref(v_name_1518_);
v___x_1522_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_1520_, v___f_1521_, v_name_1518_, v_headers_1517_);
if (v___x_1522_ == 0)
{
lean_dec_ref(v_value_1519_);
lean_dec_ref(v_name_1518_);
return v_headers_1517_;
}
else
{
lean_object* v_entries_1523_; lean_object* v_indexes_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1538_; 
v_entries_1523_ = lean_ctor_get(v_headers_1517_, 0);
v_indexes_1524_ = lean_ctor_get(v_headers_1517_, 1);
v_isSharedCheck_1538_ = !lean_is_exclusive(v_headers_1517_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1526_ = v_headers_1517_;
v_isShared_1527_ = v_isSharedCheck_1538_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_indexes_1524_);
lean_inc(v_entries_1523_);
lean_dec(v_headers_1517_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1538_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v_idxs_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v_lastIdx_1532_; lean_object* v___x_1533_; lean_object* v_entries_1534_; lean_object* v___x_1536_; 
lean_inc_ref(v_name_1518_);
v_idxs_1528_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v___f_1520_, v___f_1521_, v_indexes_1524_, v_name_1518_);
v___x_1529_ = lean_array_get_size(v_idxs_1528_);
v___x_1530_ = lean_unsigned_to_nat(1u);
v___x_1531_ = lean_nat_sub(v___x_1529_, v___x_1530_);
v_lastIdx_1532_ = lean_array_fget(v_idxs_1528_, v___x_1531_);
lean_dec(v___x_1531_);
lean_dec(v_idxs_1528_);
v___x_1533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1533_, 0, v_name_1518_);
lean_ctor_set(v___x_1533_, 1, v_value_1519_);
v_entries_1534_ = lean_array_fset(v_entries_1523_, v_lastIdx_1532_, v___x_1533_);
lean_dec(v_lastIdx_1532_);
if (v_isShared_1527_ == 0)
{
lean_ctor_set(v___x_1526_, 0, v_entries_1534_);
v___x_1536_ = v___x_1526_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_entries_1534_);
lean_ctor_set(v_reuseFailAlloc_1537_, 1, v_indexes_1524_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instToString___lam__0(lean_object* v___x_1539_, lean_object* v___x_1540_, lean_object* v___x_1541_, lean_object* v_fst_1542_, lean_object* v___x_1543_, uint32_t v___x_1544_, lean_object* v___x_1545_, lean_object* v_it_1546_, lean_object* v_acc_1547_, lean_object* v_hP_1548_, lean_object* v_recur_1549_){
_start:
{
lean_object* v_it_1551_; lean_object* v_out_1552_; lean_object* v_it_1568_; lean_object* v_startInclusive_1569_; lean_object* v_endExclusive_1570_; 
if (lean_obj_tag(v_it_1546_) == 0)
{
lean_object* v_currPos_1582_; lean_object* v_searcher_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1605_; 
v_currPos_1582_ = lean_ctor_get(v_it_1546_, 0);
v_searcher_1583_ = lean_ctor_get(v_it_1546_, 1);
v_isSharedCheck_1605_ = !lean_is_exclusive(v_it_1546_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1585_ = v_it_1546_;
v_isShared_1586_ = v_isSharedCheck_1605_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_searcher_1583_);
lean_inc(v_currPos_1582_);
lean_dec(v_it_1546_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1605_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
uint8_t v___x_1587_; 
v___x_1587_ = lean_nat_dec_eq(v_searcher_1583_, v___x_1543_);
if (v___x_1587_ == 0)
{
uint32_t v___x_1588_; uint8_t v___x_1589_; 
lean_dec(v___x_1543_);
v___x_1588_ = lean_string_utf8_get_fast(v_fst_1542_, v_searcher_1583_);
v___x_1589_ = lean_uint32_dec_eq(v___x_1588_, v___x_1544_);
if (v___x_1589_ == 0)
{
lean_object* v___x_1590_; lean_object* v___x_1592_; 
v___x_1590_ = lean_string_utf8_next_fast(v_fst_1542_, v_searcher_1583_);
lean_dec(v_searcher_1583_);
if (v_isShared_1586_ == 0)
{
lean_ctor_set(v___x_1585_, 1, v___x_1590_);
v___x_1592_ = v___x_1585_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_currPos_1582_);
lean_ctor_set(v_reuseFailAlloc_1594_, 1, v___x_1590_);
v___x_1592_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
lean_object* v___x_1593_; 
v___x_1593_ = lean_apply_4(v_recur_1549_, v___x_1592_, v_acc_1547_, lean_box(0), lean_box(0));
return v___x_1593_;
}
}
else
{
lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v_slice_1598_; lean_object* v_nextIt_1600_; 
v___x_1595_ = lean_string_utf8_next_fast(v_fst_1542_, v_searcher_1583_);
v___x_1596_ = lean_nat_sub(v___x_1595_, v_searcher_1583_);
v___x_1597_ = lean_nat_add(v_searcher_1583_, v___x_1596_);
lean_dec(v___x_1596_);
v_slice_1598_ = l_String_Slice_subslice_x21(v___x_1545_, v_currPos_1582_, v_searcher_1583_);
lean_inc(v___x_1597_);
if (v_isShared_1586_ == 0)
{
lean_ctor_set(v___x_1585_, 1, v___x_1597_);
lean_ctor_set(v___x_1585_, 0, v___x_1597_);
v_nextIt_1600_ = v___x_1585_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v___x_1597_);
lean_ctor_set(v_reuseFailAlloc_1603_, 1, v___x_1597_);
v_nextIt_1600_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
lean_object* v_startInclusive_1601_; lean_object* v_endExclusive_1602_; 
v_startInclusive_1601_ = lean_ctor_get(v_slice_1598_, 0);
lean_inc(v_startInclusive_1601_);
v_endExclusive_1602_ = lean_ctor_get(v_slice_1598_, 1);
lean_inc(v_endExclusive_1602_);
lean_dec_ref(v_slice_1598_);
v_it_1568_ = v_nextIt_1600_;
v_startInclusive_1569_ = v_startInclusive_1601_;
v_endExclusive_1570_ = v_endExclusive_1602_;
goto v___jp_1567_;
}
}
}
else
{
lean_object* v___x_1604_; 
lean_del_object(v___x_1585_);
lean_dec(v_searcher_1583_);
v___x_1604_ = lean_box(1);
v_it_1568_ = v___x_1604_;
v_startInclusive_1569_ = v_currPos_1582_;
v_endExclusive_1570_ = v___x_1543_;
goto v___jp_1567_;
}
}
}
else
{
lean_dec_ref(v_recur_1549_);
lean_dec(v___x_1543_);
return v_acc_1547_;
}
v___jp_1550_:
{
if (lean_obj_tag(v_acc_1547_) == 0)
{
lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1553_, 0, v_out_1552_);
v___x_1554_ = lean_apply_4(v_recur_1549_, v_it_1551_, v___x_1553_, lean_box(0), lean_box(0));
return v___x_1554_;
}
else
{
lean_object* v_val_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1566_; 
v_val_1555_ = lean_ctor_get(v_acc_1547_, 0);
v_isSharedCheck_1566_ = !lean_is_exclusive(v_acc_1547_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1557_ = v_acc_1547_;
v_isShared_1558_ = v_isSharedCheck_1566_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_val_1555_);
lean_dec(v_acc_1547_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1566_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1563_; 
v___x_1559_ = lean_string_utf8_extract(v___x_1539_, v___x_1540_, v___x_1541_);
v___x_1560_ = lean_string_append(v_val_1555_, v___x_1559_);
lean_dec_ref(v___x_1559_);
v___x_1561_ = lean_string_append(v___x_1560_, v_out_1552_);
lean_dec_ref(v_out_1552_);
if (v_isShared_1558_ == 0)
{
lean_ctor_set(v___x_1557_, 0, v___x_1561_);
v___x_1563_ = v___x_1557_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v___x_1561_);
v___x_1563_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
lean_object* v___x_1564_; 
v___x_1564_ = lean_apply_4(v_recur_1549_, v_it_1551_, v___x_1563_, lean_box(0), lean_box(0));
return v___x_1564_;
}
}
}
}
v___jp_1567_:
{
lean_object* v___x_1571_; uint32_t v___x_1572_; uint32_t v___x_1573_; uint8_t v___x_1574_; 
v___x_1571_ = lean_string_utf8_extract(v_fst_1542_, v_startInclusive_1569_, v_endExclusive_1570_);
lean_dec(v_endExclusive_1570_);
lean_dec(v_startInclusive_1569_);
v___x_1572_ = lean_string_utf8_get(v___x_1571_, v___x_1540_);
v___x_1573_ = 97;
v___x_1574_ = lean_uint32_dec_le(v___x_1573_, v___x_1572_);
if (v___x_1574_ == 0)
{
lean_object* v___x_1575_; 
v___x_1575_ = lean_string_utf8_set(v___x_1571_, v___x_1540_, v___x_1572_);
v_it_1551_ = v_it_1568_;
v_out_1552_ = v___x_1575_;
goto v___jp_1550_;
}
else
{
uint32_t v___x_1576_; uint8_t v___x_1577_; 
v___x_1576_ = 122;
v___x_1577_ = lean_uint32_dec_le(v___x_1572_, v___x_1576_);
if (v___x_1577_ == 0)
{
lean_object* v___x_1578_; 
v___x_1578_ = lean_string_utf8_set(v___x_1571_, v___x_1540_, v___x_1572_);
v_it_1551_ = v_it_1568_;
v_out_1552_ = v___x_1578_;
goto v___jp_1550_;
}
else
{
uint32_t v___x_1579_; uint32_t v___x_1580_; lean_object* v___x_1581_; 
v___x_1579_ = 4294967264;
v___x_1580_ = lean_uint32_add(v___x_1572_, v___x_1579_);
v___x_1581_ = lean_string_utf8_set(v___x_1571_, v___x_1540_, v___x_1580_);
v_it_1551_ = v_it_1568_;
v_out_1552_ = v___x_1581_;
goto v___jp_1550_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instToString___lam__0___boxed(lean_object* v___x_1606_, lean_object* v___x_1607_, lean_object* v___x_1608_, lean_object* v_fst_1609_, lean_object* v___x_1610_, lean_object* v___x_1611_, lean_object* v___x_1612_, lean_object* v_it_1613_, lean_object* v_acc_1614_, lean_object* v_hP_1615_, lean_object* v_recur_1616_){
_start:
{
uint32_t v___x_1744__boxed_1617_; lean_object* v_res_1618_; 
v___x_1744__boxed_1617_ = lean_unbox_uint32(v___x_1611_);
lean_dec(v___x_1611_);
v_res_1618_ = l_Std_Http_Headers_instToString___lam__0(v___x_1606_, v___x_1607_, v___x_1608_, v_fst_1609_, v___x_1610_, v___x_1744__boxed_1617_, v___x_1612_, v_it_1613_, v_acc_1614_, v_hP_1615_, v_recur_1616_);
lean_dec_ref(v___x_1612_);
lean_dec_ref(v_fst_1609_);
lean_dec(v___x_1608_);
lean_dec(v___x_1607_);
lean_dec_ref(v___x_1606_);
return v_res_1618_;
}
}
static lean_object* _init_l_Std_Http_Headers_instToString___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1622_ = ((lean_object*)(l_Std_Http_Headers_instToString___lam__1___closed__2));
v___x_1623_ = lean_string_utf8_byte_size(v___x_1622_);
return v___x_1623_;
}
}
static lean_object* _init_l_Std_Http_Headers_instToString___lam__1___boxed__const__1(void){
_start:
{
uint32_t v___x_1624_; lean_object* v___x_1625_; 
v___x_1624_ = 45;
v___x_1625_ = lean_box_uint32(v___x_1624_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instToString___lam__1(lean_object* v_x_1626_){
_start:
{
lean_object* v_fst_1627_; lean_object* v_snd_1628_; lean_object* v___y_1630_; lean_object* v___f_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v_it_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___f_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
v_fst_1627_ = lean_ctor_get(v_x_1626_, 0);
lean_inc_n(v_fst_1627_, 2);
v_snd_1628_ = lean_ctor_get(v_x_1626_, 1);
lean_inc(v_snd_1628_);
lean_dec_ref(v_x_1626_);
v___f_1634_ = ((lean_object*)(l_Std_Http_Headers_instToString___lam__1___closed__1));
v___x_1635_ = lean_unsigned_to_nat(0u);
v___x_1636_ = lean_string_utf8_byte_size(v_fst_1627_);
v___x_1637_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1637_, 0, v_fst_1627_);
lean_ctor_set(v___x_1637_, 1, v___x_1635_);
lean_ctor_set(v___x_1637_, 2, v___x_1636_);
lean_inc_ref(v___x_1637_);
v_it_1638_ = l_String_Slice_splitToSubslice___redArg(v___x_1637_, v___f_1634_);
v___x_1639_ = ((lean_object*)(l_Std_Http_Headers_instToString___lam__1___closed__2));
v___x_1640_ = lean_obj_once(&l_Std_Http_Headers_instToString___lam__1___closed__3, &l_Std_Http_Headers_instToString___lam__1___closed__3_once, _init_l_Std_Http_Headers_instToString___lam__1___closed__3);
v___x_1641_ = l_Std_Http_Headers_instToString___lam__1___boxed__const__1;
v___f_1642_ = lean_alloc_closure((void*)(l_Std_Http_Headers_instToString___lam__0___boxed), 11, 7);
lean_closure_set(v___f_1642_, 0, v___x_1639_);
lean_closure_set(v___f_1642_, 1, v___x_1635_);
lean_closure_set(v___f_1642_, 2, v___x_1640_);
lean_closure_set(v___f_1642_, 3, v_fst_1627_);
lean_closure_set(v___f_1642_, 4, v___x_1636_);
lean_closure_set(v___f_1642_, 5, v___x_1641_);
lean_closure_set(v___f_1642_, 6, v___x_1637_);
v___x_1643_ = lean_box(0);
v___x_1644_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1642_, v_it_1638_, v___x_1643_, lean_box(0));
if (lean_obj_tag(v___x_1644_) == 0)
{
lean_object* v___x_1645_; 
v___x_1645_ = ((lean_object*)(l_Std_Http_Headers_get_x21___closed__0));
v___y_1630_ = v___x_1645_;
goto v___jp_1629_;
}
else
{
lean_object* v_val_1646_; 
v_val_1646_ = lean_ctor_get(v___x_1644_, 0);
lean_inc(v_val_1646_);
lean_dec_ref_known(v___x_1644_, 1);
v___y_1630_ = v_val_1646_;
goto v___jp_1629_;
}
v___jp_1629_:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___x_1631_ = ((lean_object*)(l_Std_Http_Headers_instToString___lam__1___closed__0));
v___x_1632_ = lean_string_append(v___y_1630_, v___x_1631_);
v___x_1633_ = lean_string_append(v___x_1632_, v_snd_1628_);
lean_dec(v_snd_1628_);
return v___x_1633_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instToString___lam__2(lean_object* v___f_1648_, lean_object* v_headers_1649_){
_start:
{
lean_object* v_entries_1650_; lean_object* v___x_1651_; size_t v_sz_1652_; size_t v___x_1653_; lean_object* v_pairs_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
v_entries_1650_ = lean_ctor_get(v_headers_1649_, 0);
lean_inc_ref(v_entries_1650_);
lean_dec_ref(v_headers_1649_);
v___x_1651_ = ((lean_object*)(l_Std_Http_Headers_getAll___redArg___closed__9));
v_sz_1652_ = lean_array_size(v_entries_1650_);
v___x_1653_ = ((size_t)0ULL);
v_pairs_1654_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1651_, v___f_1648_, v_sz_1652_, v___x_1653_, v_entries_1650_);
v___x_1655_ = ((lean_object*)(l_Std_Http_Headers_instToString___lam__2___closed__0));
v___x_1656_ = lean_array_to_list(v_pairs_1654_);
v___x_1657_ = l_String_intercalate(v___x_1655_, v___x_1656_);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instEncodeV11___lam__0(lean_object* v___x_1662_, lean_object* v___x_1663_, lean_object* v___x_1664_, lean_object* v_name_1665_, lean_object* v___x_1666_, uint32_t v___x_1667_, lean_object* v___x_1668_, lean_object* v_it_1669_, lean_object* v_acc_1670_, lean_object* v_hP_1671_, lean_object* v_recur_1672_){
_start:
{
lean_object* v_it_1674_; lean_object* v_out_1675_; lean_object* v_it_1691_; lean_object* v_startInclusive_1692_; lean_object* v_endExclusive_1693_; 
if (lean_obj_tag(v_it_1669_) == 0)
{
lean_object* v_currPos_1705_; lean_object* v_searcher_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1728_; 
v_currPos_1705_ = lean_ctor_get(v_it_1669_, 0);
v_searcher_1706_ = lean_ctor_get(v_it_1669_, 1);
v_isSharedCheck_1728_ = !lean_is_exclusive(v_it_1669_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1708_ = v_it_1669_;
v_isShared_1709_ = v_isSharedCheck_1728_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_searcher_1706_);
lean_inc(v_currPos_1705_);
lean_dec(v_it_1669_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1728_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
uint8_t v___x_1710_; 
v___x_1710_ = lean_nat_dec_eq(v_searcher_1706_, v___x_1666_);
if (v___x_1710_ == 0)
{
uint32_t v___x_1711_; uint8_t v___x_1712_; 
lean_dec(v___x_1666_);
v___x_1711_ = lean_string_utf8_get_fast(v_name_1665_, v_searcher_1706_);
v___x_1712_ = lean_uint32_dec_eq(v___x_1711_, v___x_1667_);
if (v___x_1712_ == 0)
{
lean_object* v___x_1713_; lean_object* v___x_1715_; 
v___x_1713_ = lean_string_utf8_next_fast(v_name_1665_, v_searcher_1706_);
lean_dec(v_searcher_1706_);
if (v_isShared_1709_ == 0)
{
lean_ctor_set(v___x_1708_, 1, v___x_1713_);
v___x_1715_ = v___x_1708_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_currPos_1705_);
lean_ctor_set(v_reuseFailAlloc_1717_, 1, v___x_1713_);
v___x_1715_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
lean_object* v___x_1716_; 
v___x_1716_ = lean_apply_4(v_recur_1672_, v___x_1715_, v_acc_1670_, lean_box(0), lean_box(0));
return v___x_1716_;
}
}
else
{
lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v_slice_1721_; lean_object* v_nextIt_1723_; 
v___x_1718_ = lean_string_utf8_next_fast(v_name_1665_, v_searcher_1706_);
v___x_1719_ = lean_nat_sub(v___x_1718_, v_searcher_1706_);
v___x_1720_ = lean_nat_add(v_searcher_1706_, v___x_1719_);
lean_dec(v___x_1719_);
v_slice_1721_ = l_String_Slice_subslice_x21(v___x_1668_, v_currPos_1705_, v_searcher_1706_);
lean_inc(v___x_1720_);
if (v_isShared_1709_ == 0)
{
lean_ctor_set(v___x_1708_, 1, v___x_1720_);
lean_ctor_set(v___x_1708_, 0, v___x_1720_);
v_nextIt_1723_ = v___x_1708_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v___x_1720_);
lean_ctor_set(v_reuseFailAlloc_1726_, 1, v___x_1720_);
v_nextIt_1723_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
lean_object* v_startInclusive_1724_; lean_object* v_endExclusive_1725_; 
v_startInclusive_1724_ = lean_ctor_get(v_slice_1721_, 0);
lean_inc(v_startInclusive_1724_);
v_endExclusive_1725_ = lean_ctor_get(v_slice_1721_, 1);
lean_inc(v_endExclusive_1725_);
lean_dec_ref(v_slice_1721_);
v_it_1691_ = v_nextIt_1723_;
v_startInclusive_1692_ = v_startInclusive_1724_;
v_endExclusive_1693_ = v_endExclusive_1725_;
goto v___jp_1690_;
}
}
}
else
{
lean_object* v___x_1727_; 
lean_del_object(v___x_1708_);
lean_dec(v_searcher_1706_);
v___x_1727_ = lean_box(1);
v_it_1691_ = v___x_1727_;
v_startInclusive_1692_ = v_currPos_1705_;
v_endExclusive_1693_ = v___x_1666_;
goto v___jp_1690_;
}
}
}
else
{
lean_dec_ref(v_recur_1672_);
lean_dec(v___x_1666_);
return v_acc_1670_;
}
v___jp_1673_:
{
if (lean_obj_tag(v_acc_1670_) == 0)
{
lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1676_, 0, v_out_1675_);
v___x_1677_ = lean_apply_4(v_recur_1672_, v_it_1674_, v___x_1676_, lean_box(0), lean_box(0));
return v___x_1677_;
}
else
{
lean_object* v_val_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1689_; 
v_val_1678_ = lean_ctor_get(v_acc_1670_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v_acc_1670_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1680_ = v_acc_1670_;
v_isShared_1681_ = v_isSharedCheck_1689_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_val_1678_);
lean_dec(v_acc_1670_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1689_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1686_; 
v___x_1682_ = lean_string_utf8_extract(v___x_1662_, v___x_1663_, v___x_1664_);
v___x_1683_ = lean_string_append(v_val_1678_, v___x_1682_);
lean_dec_ref(v___x_1682_);
v___x_1684_ = lean_string_append(v___x_1683_, v_out_1675_);
lean_dec_ref(v_out_1675_);
if (v_isShared_1681_ == 0)
{
lean_ctor_set(v___x_1680_, 0, v___x_1684_);
v___x_1686_ = v___x_1680_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v___x_1684_);
v___x_1686_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
lean_object* v___x_1687_; 
v___x_1687_ = lean_apply_4(v_recur_1672_, v_it_1674_, v___x_1686_, lean_box(0), lean_box(0));
return v___x_1687_;
}
}
}
}
v___jp_1690_:
{
lean_object* v___x_1694_; uint32_t v___x_1695_; uint32_t v___x_1696_; uint8_t v___x_1697_; 
v___x_1694_ = lean_string_utf8_extract(v_name_1665_, v_startInclusive_1692_, v_endExclusive_1693_);
lean_dec(v_endExclusive_1693_);
lean_dec(v_startInclusive_1692_);
v___x_1695_ = lean_string_utf8_get(v___x_1694_, v___x_1663_);
v___x_1696_ = 97;
v___x_1697_ = lean_uint32_dec_le(v___x_1696_, v___x_1695_);
if (v___x_1697_ == 0)
{
lean_object* v___x_1698_; 
v___x_1698_ = lean_string_utf8_set(v___x_1694_, v___x_1663_, v___x_1695_);
v_it_1674_ = v_it_1691_;
v_out_1675_ = v___x_1698_;
goto v___jp_1673_;
}
else
{
uint32_t v___x_1699_; uint8_t v___x_1700_; 
v___x_1699_ = 122;
v___x_1700_ = lean_uint32_dec_le(v___x_1695_, v___x_1699_);
if (v___x_1700_ == 0)
{
lean_object* v___x_1701_; 
v___x_1701_ = lean_string_utf8_set(v___x_1694_, v___x_1663_, v___x_1695_);
v_it_1674_ = v_it_1691_;
v_out_1675_ = v___x_1701_;
goto v___jp_1673_;
}
else
{
uint32_t v___x_1702_; uint32_t v___x_1703_; lean_object* v___x_1704_; 
v___x_1702_ = 4294967264;
v___x_1703_ = lean_uint32_add(v___x_1695_, v___x_1702_);
v___x_1704_ = lean_string_utf8_set(v___x_1694_, v___x_1663_, v___x_1703_);
v_it_1674_ = v_it_1691_;
v_out_1675_ = v___x_1704_;
goto v___jp_1673_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instEncodeV11___lam__0___boxed(lean_object* v___x_1729_, lean_object* v___x_1730_, lean_object* v___x_1731_, lean_object* v_name_1732_, lean_object* v___x_1733_, lean_object* v___x_1734_, lean_object* v___x_1735_, lean_object* v_it_1736_, lean_object* v_acc_1737_, lean_object* v_hP_1738_, lean_object* v_recur_1739_){
_start:
{
uint32_t v___x_916__boxed_1740_; lean_object* v_res_1741_; 
v___x_916__boxed_1740_ = lean_unbox_uint32(v___x_1734_);
lean_dec(v___x_1734_);
v_res_1741_ = l_Std_Http_Headers_instEncodeV11___lam__0(v___x_1729_, v___x_1730_, v___x_1731_, v_name_1732_, v___x_1733_, v___x_916__boxed_1740_, v___x_1735_, v_it_1736_, v_acc_1737_, v_hP_1738_, v_recur_1739_);
lean_dec_ref(v___x_1735_);
lean_dec_ref(v_name_1732_);
lean_dec(v___x_1731_);
lean_dec(v___x_1730_);
lean_dec_ref(v___x_1729_);
return v_res_1741_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instEncodeV11___lam__1(lean_object* v_buf_1742_, lean_object* v_name_1743_, lean_object* v_value_1744_){
_start:
{
lean_object* v___y_1746_; lean_object* v___f_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v_it_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___f_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___f_1765_ = ((lean_object*)(l_Std_Http_Headers_instToString___lam__1___closed__1));
v___x_1766_ = lean_unsigned_to_nat(0u);
v___x_1767_ = lean_string_utf8_byte_size(v_name_1743_);
lean_inc_ref(v_name_1743_);
v___x_1768_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1768_, 0, v_name_1743_);
lean_ctor_set(v___x_1768_, 1, v___x_1766_);
lean_ctor_set(v___x_1768_, 2, v___x_1767_);
lean_inc_ref(v___x_1768_);
v_it_1769_ = l_String_Slice_splitToSubslice___redArg(v___x_1768_, v___f_1765_);
v___x_1770_ = ((lean_object*)(l_Std_Http_Headers_instToString___lam__1___closed__2));
v___x_1771_ = lean_obj_once(&l_Std_Http_Headers_instToString___lam__1___closed__3, &l_Std_Http_Headers_instToString___lam__1___closed__3_once, _init_l_Std_Http_Headers_instToString___lam__1___closed__3);
v___x_1772_ = l_Std_Http_Headers_instToString___lam__1___boxed__const__1;
v___f_1773_ = lean_alloc_closure((void*)(l_Std_Http_Headers_instEncodeV11___lam__0___boxed), 11, 7);
lean_closure_set(v___f_1773_, 0, v___x_1770_);
lean_closure_set(v___f_1773_, 1, v___x_1766_);
lean_closure_set(v___f_1773_, 2, v___x_1771_);
lean_closure_set(v___f_1773_, 3, v_name_1743_);
lean_closure_set(v___f_1773_, 4, v___x_1767_);
lean_closure_set(v___f_1773_, 5, v___x_1772_);
lean_closure_set(v___f_1773_, 6, v___x_1768_);
v___x_1774_ = lean_box(0);
v___x_1775_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1773_, v_it_1769_, v___x_1774_, lean_box(0));
if (lean_obj_tag(v___x_1775_) == 0)
{
lean_object* v___x_1776_; 
v___x_1776_ = ((lean_object*)(l_Std_Http_Headers_get_x21___closed__0));
v___y_1746_ = v___x_1776_;
goto v___jp_1745_;
}
else
{
lean_object* v_val_1777_; 
v_val_1777_ = lean_ctor_get(v___x_1775_, 0);
lean_inc(v_val_1777_);
lean_dec_ref_known(v___x_1775_, 1);
v___y_1746_ = v_val_1777_;
goto v___jp_1745_;
}
v___jp_1745_:
{
lean_object* v_data_1747_; lean_object* v_size_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1764_; 
v_data_1747_ = lean_ctor_get(v_buf_1742_, 0);
v_size_1748_ = lean_ctor_get(v_buf_1742_, 1);
v_isSharedCheck_1764_ = !lean_is_exclusive(v_buf_1742_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1750_ = v_buf_1742_;
v_isShared_1751_ = v_isSharedCheck_1764_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_size_1748_);
lean_inc(v_data_1747_);
lean_dec(v_buf_1742_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1764_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1762_; 
v___x_1752_ = ((lean_object*)(l_Std_Http_Headers_instToString___lam__1___closed__0));
v___x_1753_ = lean_string_append(v___y_1746_, v___x_1752_);
v___x_1754_ = lean_string_append(v___x_1753_, v_value_1744_);
v___x_1755_ = ((lean_object*)(l_Std_Http_Headers_instToString___lam__2___closed__0));
v___x_1756_ = lean_string_append(v___x_1754_, v___x_1755_);
v___x_1757_ = lean_string_to_utf8(v___x_1756_);
lean_dec_ref(v___x_1756_);
lean_inc_ref(v___x_1757_);
v___x_1758_ = lean_array_push(v_data_1747_, v___x_1757_);
v___x_1759_ = lean_byte_array_size(v___x_1757_);
lean_dec_ref(v___x_1757_);
v___x_1760_ = lean_nat_add(v_size_1748_, v___x_1759_);
lean_dec(v_size_1748_);
if (v_isShared_1751_ == 0)
{
lean_ctor_set(v___x_1750_, 1, v___x_1760_);
lean_ctor_set(v___x_1750_, 0, v___x_1758_);
v___x_1762_ = v___x_1750_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v___x_1758_);
lean_ctor_set(v_reuseFailAlloc_1763_, 1, v___x_1760_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
return v___x_1762_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instEncodeV11___lam__1___boxed(lean_object* v_buf_1778_, lean_object* v_name_1779_, lean_object* v_value_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = l_Std_Http_Headers_instEncodeV11___lam__1(v_buf_1778_, v_name_1779_, v_value_1780_);
lean_dec_ref(v_value_1780_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instEncodeV11___lam__2(lean_object* v___f_1782_, lean_object* v_buffer_1783_, lean_object* v_headers_1784_){
_start:
{
lean_object* v___x_1785_; 
v___x_1785_ = l_Std_Http_Headers_fold___redArg(v_headers_1784_, v_buffer_1783_, v___f_1782_);
return v___x_1785_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instEncodeV11___lam__2___boxed(lean_object* v___f_1786_, lean_object* v_buffer_1787_, lean_object* v_headers_1788_){
_start:
{
lean_object* v_res_1789_; 
v_res_1789_ = l_Std_Http_Headers_instEncodeV11___lam__2(v___f_1786_, v_buffer_1787_, v_headers_1788_);
lean_dec_ref(v_headers_1788_);
return v_res_1789_;
}
}
static lean_object* _init_l_Std_Http_Headers_instEmptyCollection(void){
_start:
{
lean_object* v___x_1794_; 
v___x_1794_ = lean_obj_once(&l_Std_Http_Headers_empty___closed__0, &l_Std_Http_Headers_empty___closed__0_once, _init_l_Std_Http_Headers_empty___closed__0);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instSingletonProdNameValue___lam__1(lean_object* v_x_1795_){
_start:
{
lean_object* v_fst_1796_; lean_object* v___x_1797_; lean_object* v_entries_1798_; lean_object* v_indexes_1799_; lean_object* v___f_1800_; lean_object* v___f_1801_; lean_object* v_i_1802_; lean_object* v_f_1803_; lean_object* v_entries_1804_; lean_object* v_indexes_1805_; lean_object* v___x_1806_; 
v_fst_1796_ = lean_ctor_get(v_x_1795_, 0);
lean_inc(v_fst_1796_);
v___x_1797_ = lean_obj_once(&l_Std_Http_Headers_empty___closed__0, &l_Std_Http_Headers_empty___closed__0_once, _init_l_Std_Http_Headers_empty___closed__0);
v_entries_1798_ = lean_ctor_get(v___x_1797_, 0);
v_indexes_1799_ = lean_ctor_get(v___x_1797_, 1);
v___f_1800_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_1801_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v_i_1802_ = lean_array_get_size(v_entries_1798_);
v_f_1803_ = lean_alloc_closure((void*)(l_Std_Http_Headers_insert___lam__0), 2, 1);
lean_closure_set(v_f_1803_, 0, v_i_1802_);
lean_inc_ref(v_entries_1798_);
v_entries_1804_ = lean_array_push(v_entries_1798_, v_x_1795_);
lean_inc_ref(v_indexes_1799_);
v_indexes_1805_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_1800_, v___f_1801_, v_indexes_1799_, v_fst_1796_, v_f_1803_);
v___x_1806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1806_, 0, v_entries_1804_);
lean_ctor_set(v___x_1806_, 1, v_indexes_1805_);
return v___x_1806_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instInsertProdNameValue___lam__1(lean_object* v_x_1809_, lean_object* v_s_1810_){
_start:
{
lean_object* v_fst_1811_; lean_object* v_entries_1812_; lean_object* v_indexes_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1826_; 
v_fst_1811_ = lean_ctor_get(v_x_1809_, 0);
lean_inc(v_fst_1811_);
v_entries_1812_ = lean_ctor_get(v_s_1810_, 0);
v_indexes_1813_ = lean_ctor_get(v_s_1810_, 1);
v_isSharedCheck_1826_ = !lean_is_exclusive(v_s_1810_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1815_ = v_s_1810_;
v_isShared_1816_ = v_isSharedCheck_1826_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_indexes_1813_);
lean_inc(v_entries_1812_);
lean_dec(v_s_1810_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1826_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___f_1817_; lean_object* v___f_1818_; lean_object* v_i_1819_; lean_object* v_f_1820_; lean_object* v_entries_1821_; lean_object* v_indexes_1822_; lean_object* v___x_1824_; 
v___f_1817_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_1818_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v_i_1819_ = lean_array_get_size(v_entries_1812_);
v_f_1820_ = lean_alloc_closure((void*)(l_Std_Http_Headers_insert___lam__0), 2, 1);
lean_closure_set(v_f_1820_, 0, v_i_1819_);
v_entries_1821_ = lean_array_push(v_entries_1812_, v_x_1809_);
v_indexes_1822_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_1817_, v___f_1818_, v_indexes_1813_, v_fst_1811_, v_f_1820_);
if (v_isShared_1816_ == 0)
{
lean_ctor_set(v___x_1815_, 1, v_indexes_1822_);
lean_ctor_set(v___x_1815_, 0, v_entries_1821_);
v___x_1824_ = v___x_1815_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v_entries_1821_);
lean_ctor_set(v_reuseFailAlloc_1825_, 1, v_indexes_1822_);
v___x_1824_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
return v___x_1824_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instForInProdNameValueOfMonad___redArg___lam__0(lean_object* v_f_1831_, lean_object* v_a_1832_, lean_object* v_x_1833_, lean_object* v___y_1834_){
_start:
{
lean_object* v___x_1835_; 
v___x_1835_ = lean_apply_2(v_f_1831_, v_a_1832_, v___y_1834_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instForInProdNameValueOfMonad___redArg___lam__1(lean_object* v_inst_1836_, lean_object* v_00_u03b2_1837_, lean_object* v_headers_1838_, lean_object* v_b_1839_, lean_object* v_f_1840_){
_start:
{
lean_object* v_entries_1841_; lean_object* v___f_1842_; size_t v_sz_1843_; size_t v___x_1844_; lean_object* v___x_1845_; 
v_entries_1841_ = lean_ctor_get(v_headers_1838_, 0);
lean_inc_ref(v_entries_1841_);
lean_dec_ref(v_headers_1838_);
v___f_1842_ = lean_alloc_closure((void*)(l_Std_Http_Headers_instForInProdNameValueOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1842_, 0, v_f_1840_);
v_sz_1843_ = lean_array_size(v_entries_1841_);
v___x_1844_ = ((size_t)0ULL);
v___x_1845_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1836_, v_entries_1841_, v___f_1842_, v_sz_1843_, v___x_1844_, v_b_1839_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instForInProdNameValueOfMonad___redArg(lean_object* v_inst_1846_){
_start:
{
lean_object* v___f_1847_; 
v___f_1847_ = lean_alloc_closure((void*)(l_Std_Http_Headers_instForInProdNameValueOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_1847_, 0, v_inst_1846_);
return v___f_1847_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instForInProdNameValueOfMonad(lean_object* v_m_1848_, lean_object* v_inst_1849_){
_start:
{
lean_object* v___f_1850_; 
v___f_1850_ = lean_alloc_closure((void*)(l_Std_Http_Headers_instForInProdNameValueOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_1850_, 0, v_inst_1849_);
return v___f_1850_;
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
