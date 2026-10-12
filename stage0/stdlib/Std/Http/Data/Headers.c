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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
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
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___redArg___lam__0___boxed(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_byte_array_size(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_splitToSubslice___redArg(lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Std_Http_Header_Name_ofString_x21(lean_object*);
lean_object* l_Std_Http_Header_Value_ofString_x21(lean_object*);
lean_object* l_Std_Internal_IndexMultiMap_empty___redArg();
uint8_t l_Array_contains___redArg(lean_object*, lean_object*, lean_object*);
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
static const lean_array_object l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___redArg___closed__0 = (const lean_object*)&l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___redArg___closed__0_value;
static lean_once_cell_t l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___redArg();
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___redArg___boxed(lean_object*);
static lean_once_cell_t l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_empty;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1___redArg(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_Headers_erase___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_erase___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Http_Headers_erase___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Headers_erase___closed__0;
LEAN_EXPORT lean_object* l_Std_Http_Headers_erase(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_eraseMany___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_eraseMany(lean_object*, lean_object*);
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
static const lean_closure_object l_Std_Http_Headers_instToString___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Headers_instToString___lam__1___closed__1 = (const lean_object*)&l_Std_Http_Headers_instToString___lam__1___closed__1_value;
static const lean_string_object l_Std_Http_Headers_instToString___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Std_Http_Headers_instToString___lam__1___closed__2 = (const lean_object*)&l_Std_Http_Headers_instToString___lam__1___closed__2_value;
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__3(lean_object* v_as_301_, size_t v_i_302_, size_t v_stop_303_, lean_object* v_b_304_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_301_ = stack[0].m_obj;
size_t v_i_302_ = stack[1].m_num;
size_t v_stop_303_ = stack[2].m_num;
lean_object* v_b_304_ = stack[3].m_obj;
lean_object* v_res_311_;
v_res_311_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__3(v_as_301_, v_i_302_, v_stop_303_, v_b_304_);
stack->m_obj
 = v_res_311_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__3___boxed(lean_object* v_as_312_, lean_object* v_i_313_, lean_object* v_stop_314_, lean_object* v_b_315_){
_start:
{
size_t v_i_boxed_316_; size_t v_stop_boxed_317_; lean_object* v_res_318_; 
v_i_boxed_316_ = lean_unbox_usize(v_i_313_);
lean_dec(v_i_313_);
v_stop_boxed_317_ = lean_unbox_usize(v_stop_314_);
lean_dec(v_stop_314_);
v_res_318_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__3(v_as_312_, v_i_boxed_316_, v_stop_boxed_317_, v_b_315_);
lean_dec_ref(v_as_312_);
return v_res_318_;
}
}
static lean_object* _init_l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_332_ = lean_unsigned_to_nat(11u);
v___x_333_ = lean_nat_to_int(v___x_332_);
return v___x_333_;
}
}
static lean_object* _init_l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__17(void){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_347_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__6));
v___x_348_ = lean_string_length(v___x_347_);
return v___x_348_;
}
}
static lean_object* _init_l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__18(void){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = lean_obj_once(&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__17, &l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__17_once, _init_l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__17);
v___x_350_ = lean_nat_to_int(v___x_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg(lean_object* v_x_355_){
_start:
{
lean_object* v_indexes_356_; lean_object* v_entries_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_416_; 
v_indexes_356_ = lean_ctor_get(v_x_355_, 1);
v_entries_357_ = lean_ctor_get(v_x_355_, 0);
v_isSharedCheck_416_ = !lean_is_exclusive(v_x_355_);
if (v_isSharedCheck_416_ == 0)
{
v___x_359_ = v_x_355_;
v_isShared_360_ = v_isSharedCheck_416_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_indexes_356_);
lean_inc(v_entries_357_);
lean_dec(v_x_355_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_416_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v_buckets_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_414_; 
v_buckets_361_ = lean_ctor_get(v_indexes_356_, 1);
v_isSharedCheck_414_ = !lean_is_exclusive(v_indexes_356_);
if (v_isSharedCheck_414_ == 0)
{
lean_object* v_unused_415_; 
v_unused_415_ = lean_ctor_get(v_indexes_356_, 0);
lean_dec(v_unused_415_);
v___x_363_ = v_indexes_356_;
v_isShared_364_ = v_isSharedCheck_414_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_buckets_361_);
lean_dec(v_indexes_356_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_414_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_370_; 
v___x_365_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__4));
v___x_366_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__5));
v___x_367_ = lean_obj_once(&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__7, &l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__7_once, _init_l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__7);
v___x_368_ = l_Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0(v_entries_357_);
if (v_isShared_364_ == 0)
{
lean_ctor_set_tag(v___x_363_, 4);
lean_ctor_set(v___x_363_, 1, v___x_368_);
lean_ctor_set(v___x_363_, 0, v___x_367_);
v___x_370_ = v___x_363_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v___x_367_);
lean_ctor_set(v_reuseFailAlloc_413_, 1, v___x_368_);
v___x_370_ = v_reuseFailAlloc_413_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
uint8_t v___x_371_; lean_object* v___x_372_; lean_object* v___x_374_; 
v___x_371_ = 0;
v___x_372_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_372_, 0, v___x_370_);
lean_ctor_set_uint8(v___x_372_, sizeof(void*)*1, v___x_371_);
if (v_isShared_360_ == 0)
{
lean_ctor_set_tag(v___x_359_, 5);
lean_ctor_set(v___x_359_, 1, v___x_372_);
lean_ctor_set(v___x_359_, 0, v___x_366_);
v___x_374_ = v___x_359_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_366_);
lean_ctor_set(v_reuseFailAlloc_412_, 1, v___x_372_);
v___x_374_ = v_reuseFailAlloc_412_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___y_385_; lean_object* v___x_406_; lean_object* v___x_407_; uint8_t v___x_408_; 
v___x_375_ = ((lean_object*)(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__2));
v___x_376_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_376_, 0, v___x_374_);
lean_ctor_set(v___x_376_, 1, v___x_375_);
v___x_377_ = lean_box(1);
v___x_378_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_378_, 0, v___x_376_);
lean_ctor_set(v___x_378_, 1, v___x_377_);
v___x_379_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__9));
v___x_380_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_380_, 0, v___x_378_);
lean_ctor_set(v___x_380_, 1, v___x_379_);
v___x_381_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
lean_ctor_set(v___x_381_, 1, v___x_365_);
v___x_382_ = lean_unsigned_to_nat(0u);
v___x_383_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__11));
v___x_406_ = lean_box(0);
v___x_407_ = lean_array_get_size(v_buckets_361_);
v___x_408_ = lean_nat_dec_lt(v___x_382_, v___x_407_);
if (v___x_408_ == 0)
{
lean_dec_ref(v_buckets_361_);
v___y_385_ = v___x_406_;
goto v___jp_384_;
}
else
{
size_t v___x_409_; size_t v___x_410_; lean_object* v___x_411_; 
v___x_409_ = lean_usize_of_nat(v___x_407_);
v___x_410_ = ((size_t)0ULL);
v___x_411_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__3(v_buckets_361_, v___x_409_, v___x_410_, v___x_406_);
lean_dec_ref(v_buckets_361_);
v___y_385_ = v___x_411_;
goto v___jp_384_;
}
v___jp_384_:
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_386_ = l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg(v___y_385_);
v___x_387_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_387_, 0, v___x_383_);
lean_ctor_set(v___x_387_, 1, v___x_386_);
v___x_388_ = l_Repr_addAppParen(v___x_387_, v___x_382_);
v___x_389_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_389_, 0, v___x_367_);
lean_ctor_set(v___x_389_, 1, v___x_388_);
v___x_390_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_390_, 0, v___x_389_);
lean_ctor_set_uint8(v___x_390_, sizeof(void*)*1, v___x_371_);
v___x_391_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_391_, 0, v___x_381_);
lean_ctor_set(v___x_391_, 1, v___x_390_);
v___x_392_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
lean_ctor_set(v___x_392_, 1, v___x_375_);
v___x_393_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_393_, 0, v___x_392_);
lean_ctor_set(v___x_393_, 1, v___x_377_);
v___x_394_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__13));
v___x_395_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_395_, 0, v___x_393_);
lean_ctor_set(v___x_395_, 1, v___x_394_);
v___x_396_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_396_, 0, v___x_395_);
lean_ctor_set(v___x_396_, 1, v___x_365_);
v___x_397_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__15));
v___x_398_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_398_, 0, v___x_396_);
lean_ctor_set(v___x_398_, 1, v___x_397_);
v___x_399_ = lean_obj_once(&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__18, &l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__18_once, _init_l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__18);
v___x_400_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__19));
v___x_401_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_401_, 0, v___x_400_);
lean_ctor_set(v___x_401_, 1, v___x_398_);
v___x_402_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__20));
v___x_403_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_403_, 0, v___x_401_);
lean_ctor_set(v___x_403_, 1, v___x_402_);
v___x_404_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_404_, 0, v___x_399_);
lean_ctor_set(v___x_404_, 1, v___x_403_);
v___x_405_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_405_, 0, v___x_404_);
lean_ctor_set_uint8(v___x_405_, sizeof(void*)*1, v___x_371_);
return v___x_405_;
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
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = lean_unsigned_to_nat(7u);
v___x_427_ = lean_nat_to_int(v___x_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprHeaders_repr___redArg(lean_object* v_x_428_){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; uint8_t v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_429_ = ((lean_object*)(l_Std_Http_instReprHeaders_repr___redArg___closed__3));
v___x_430_ = lean_obj_once(&l_Std_Http_instReprHeaders_repr___redArg___closed__4, &l_Std_Http_instReprHeaders_repr___redArg___closed__4_once, _init_l_Std_Http_instReprHeaders_repr___redArg___closed__4);
v___x_431_ = l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg(v_x_428_);
v___x_432_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_432_, 0, v___x_430_);
lean_ctor_set(v___x_432_, 1, v___x_431_);
v___x_433_ = 0;
v___x_434_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_434_, 0, v___x_432_);
lean_ctor_set_uint8(v___x_434_, sizeof(void*)*1, v___x_433_);
v___x_435_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_435_, 0, v___x_429_);
lean_ctor_set(v___x_435_, 1, v___x_434_);
v___x_436_ = lean_obj_once(&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__18, &l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__18_once, _init_l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__18);
v___x_437_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__19));
v___x_438_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_438_, 0, v___x_437_);
lean_ctor_set(v___x_438_, 1, v___x_435_);
v___x_439_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__20));
v___x_440_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_440_, 0, v___x_438_);
lean_ctor_set(v___x_440_, 1, v___x_439_);
v___x_441_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_441_, 0, v___x_436_);
lean_ctor_set(v___x_441_, 1, v___x_440_);
v___x_442_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_442_, 0, v___x_441_);
lean_ctor_set_uint8(v___x_442_, sizeof(void*)*1, v___x_433_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprHeaders_repr(lean_object* v_x_443_, lean_object* v_prec_444_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l_Std_Http_instReprHeaders_repr___redArg(v_x_443_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprHeaders_repr___boxed(lean_object* v_x_446_, lean_object* v_prec_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_Std_Http_instReprHeaders_repr(v_x_446_, v_prec_447_);
lean_dec(v_prec_447_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0(lean_object* v_x_449_, lean_object* v_prec_450_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg(v_x_449_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___boxed(lean_object* v_x_452_, lean_object* v_prec_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0(v_x_452_, v_prec_453_);
lean_dec(v_prec_453_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1(lean_object* v_a_455_, lean_object* v_n_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg(v_a_455_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___boxed(lean_object* v_a_458_, lean_object* v_n_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1(v_a_458_, v_n_459_);
lean_dec(v_n_459_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2(lean_object* v_x_461_, lean_object* v_x_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg(v_x_461_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___boxed(lean_object* v_x_464_, lean_object* v_x_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2(v_x_464_, v_x_465_);
lean_dec(v_x_465_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5(lean_object* v_x_467_, lean_object* v_x_468_){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg(v_x_467_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___boxed(lean_object* v_x_470_, lean_object* v_x_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5(v_x_470_, v_x_471_);
lean_dec(v_x_471_);
return v_res_472_;
}
}
static lean_object* _init_l_Std_Http_instMembershipNameHeaders(void){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = lean_box(0);
return v___x_475_;
}
}
uint8_t l_Std_Http_instDecidableMemNameHeaders(lean_object* v_name_478_, lean_object* v_h_479_){
_start:
{
lean_object* v___f_480_; lean_object* v___f_481_; uint8_t v___x_482_; 
v___f_480_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_481_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v___x_482_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_480_, v___f_481_, v_name_478_, v_h_479_);
return v___x_482_;
}
}
LEAN_EXPORT void l_Std_Http_instDecidableMemNameHeaders_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_478_ = stack[0].m_obj;
lean_object* v_h_479_ = stack[1].m_obj;
uint8_t v_res_483_;
v_res_483_ = l_Std_Http_instDecidableMemNameHeaders(v_name_478_, v_h_479_);
stack->m_num = v_res_483_;
}
LEAN_EXPORT lean_object* l_Std_Http_instDecidableMemNameHeaders___boxed(lean_object* v_name_484_, lean_object* v_h_485_){
_start:
{
uint8_t v_res_486_; lean_object* v_r_487_; 
v_res_486_ = l_Std_Http_instDecidableMemNameHeaders(v_name_484_, v_h_485_);
lean_dec_ref(v_h_485_);
v_r_487_ = lean_box(v_res_486_);
return v_r_487_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_get___redArg(lean_object* v_headers_488_, lean_object* v_name_489_){
_start:
{
lean_object* v_entries_490_; lean_object* v_indexes_491_; lean_object* v___f_492_; lean_object* v___f_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v_entry_496_; lean_object* v___x_497_; lean_object* v_snd_498_; 
v_entries_490_ = lean_ctor_get(v_headers_488_, 0);
v_indexes_491_ = lean_ctor_get(v_headers_488_, 1);
v___f_492_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_493_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v___x_494_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v___f_492_, v___f_493_, v_indexes_491_, v_name_489_);
v___x_495_ = lean_unsigned_to_nat(0u);
v_entry_496_ = lean_array_fget(v___x_494_, v___x_495_);
lean_dec(v___x_494_);
v___x_497_ = lean_array_fget_borrowed(v_entries_490_, v_entry_496_);
lean_dec(v_entry_496_);
v_snd_498_ = lean_ctor_get(v___x_497_, 1);
lean_inc(v_snd_498_);
return v_snd_498_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_get___redArg___boxed(lean_object* v_headers_499_, lean_object* v_name_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Std_Http_Headers_get___redArg(v_headers_499_, v_name_500_);
lean_dec_ref(v_headers_499_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_get(lean_object* v_headers_502_, lean_object* v_name_503_, lean_object* v_h_504_){
_start:
{
lean_object* v_entries_505_; lean_object* v_indexes_506_; lean_object* v___f_507_; lean_object* v___f_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v_entry_511_; lean_object* v___x_512_; lean_object* v_snd_513_; 
v_entries_505_ = lean_ctor_get(v_headers_502_, 0);
v_indexes_506_ = lean_ctor_get(v_headers_502_, 1);
v___f_507_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_508_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v___x_509_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v___f_507_, v___f_508_, v_indexes_506_, v_name_503_);
v___x_510_ = lean_unsigned_to_nat(0u);
v_entry_511_ = lean_array_fget(v___x_509_, v___x_510_);
lean_dec(v___x_509_);
v___x_512_ = lean_array_fget_borrowed(v_entries_505_, v_entry_511_);
lean_dec(v_entry_511_);
v_snd_513_ = lean_ctor_get(v___x_512_, 1);
lean_inc(v_snd_513_);
return v_snd_513_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_get___boxed(lean_object* v_headers_514_, lean_object* v_name_515_, lean_object* v_h_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_Std_Http_Headers_get(v_headers_514_, v_name_515_, v_h_516_);
lean_dec_ref(v_headers_514_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_getAll___redArg___lam__0(lean_object* v___x_518_, lean_object* v_entries_519_, lean_object* v_x1_520_, lean_object* v_x2_521_, lean_object* v_x3_522_){
_start:
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v_snd_525_; 
v___x_523_ = lean_array_fget_borrowed(v___x_518_, v_x1_520_);
v___x_524_ = lean_array_fget_borrowed(v_entries_519_, v___x_523_);
v_snd_525_ = lean_ctor_get(v___x_524_, 1);
lean_inc(v_snd_525_);
return v_snd_525_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_getAll___redArg___lam__0___boxed(lean_object* v___x_526_, lean_object* v_entries_527_, lean_object* v_x1_528_, lean_object* v_x2_529_, lean_object* v_x3_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_Std_Http_Headers_getAll___redArg___lam__0(v___x_526_, v_entries_527_, v_x1_528_, v_x2_529_, v_x3_530_);
lean_dec(v_x2_529_);
lean_dec(v_x1_528_);
lean_dec_ref(v_entries_527_);
lean_dec(v___x_526_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_getAll___redArg(lean_object* v_headers_551_, lean_object* v_name_552_){
_start:
{
lean_object* v_entries_553_; lean_object* v_indexes_554_; lean_object* v___f_555_; lean_object* v___f_556_; lean_object* v___x_557_; lean_object* v___f_558_; lean_object* v___x_559_; size_t v_sz_560_; size_t v___x_561_; lean_object* v_entries_562_; 
v_entries_553_ = lean_ctor_get(v_headers_551_, 0);
lean_inc_ref(v_entries_553_);
v_indexes_554_ = lean_ctor_get(v_headers_551_, 1);
lean_inc_ref(v_indexes_554_);
lean_dec_ref(v_headers_551_);
v___f_555_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_556_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v___x_557_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v___f_555_, v___f_556_, v_indexes_554_, v_name_552_);
lean_dec_ref(v_indexes_554_);
lean_inc_n(v___x_557_, 2);
v___f_558_ = lean_alloc_closure((void*)(l_Std_Http_Headers_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_558_, 0, v___x_557_);
lean_closure_set(v___f_558_, 1, v_entries_553_);
v___x_559_ = ((lean_object*)(l_Std_Http_Headers_getAll___redArg___closed__9));
v_sz_560_ = lean_array_size(v___x_557_);
v___x_561_ = ((size_t)0ULL);
v_entries_562_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_559_, v___x_557_, v___f_558_, v_sz_560_, v___x_561_, v___x_557_);
lean_dec(v___x_557_);
return v_entries_562_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_getAll(lean_object* v_headers_563_, lean_object* v_name_564_, lean_object* v_h_565_){
_start:
{
lean_object* v_entries_566_; lean_object* v_indexes_567_; lean_object* v___f_568_; lean_object* v___f_569_; lean_object* v___x_570_; lean_object* v___f_571_; lean_object* v___x_572_; size_t v_sz_573_; size_t v___x_574_; lean_object* v_entries_575_; 
v_entries_566_ = lean_ctor_get(v_headers_563_, 0);
lean_inc_ref(v_entries_566_);
v_indexes_567_ = lean_ctor_get(v_headers_563_, 1);
lean_inc_ref(v_indexes_567_);
lean_dec_ref(v_headers_563_);
v___f_568_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_569_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v___x_570_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v___f_568_, v___f_569_, v_indexes_567_, v_name_564_);
lean_dec_ref(v_indexes_567_);
lean_inc_n(v___x_570_, 2);
v___f_571_ = lean_alloc_closure((void*)(l_Std_Http_Headers_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_571_, 0, v___x_570_);
lean_closure_set(v___f_571_, 1, v_entries_566_);
v___x_572_ = ((lean_object*)(l_Std_Http_Headers_getAll___redArg___closed__9));
v_sz_573_ = lean_array_size(v___x_570_);
v___x_574_ = ((size_t)0ULL);
v_entries_575_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_572_, v___x_570_, v___f_571_, v_sz_573_, v___x_574_, v___x_570_);
lean_dec(v___x_570_);
return v_entries_575_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_getAll_x3f(lean_object* v_headers_576_, lean_object* v_name_577_){
_start:
{
lean_object* v_entries_578_; lean_object* v_indexes_579_; lean_object* v___f_580_; lean_object* v___f_581_; uint8_t v___x_582_; 
v_entries_578_ = lean_ctor_get(v_headers_576_, 0);
lean_inc_ref(v_entries_578_);
v_indexes_579_ = lean_ctor_get(v_headers_576_, 1);
lean_inc_ref(v_indexes_579_);
lean_dec_ref(v_headers_576_);
v___f_580_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_581_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
lean_inc_ref(v_name_577_);
v___x_582_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_580_, v___f_581_, v_indexes_579_, v_name_577_);
if (v___x_582_ == 0)
{
lean_object* v___x_583_; 
lean_dec_ref(v_indexes_579_);
lean_dec_ref(v_entries_578_);
lean_dec_ref(v_name_577_);
v___x_583_ = lean_box(0);
return v___x_583_;
}
else
{
lean_object* v___x_584_; lean_object* v___f_585_; lean_object* v___x_586_; size_t v_sz_587_; size_t v___x_588_; lean_object* v_entries_589_; lean_object* v___x_590_; 
v___x_584_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v___f_580_, v___f_581_, v_indexes_579_, v_name_577_);
lean_dec_ref(v_indexes_579_);
lean_inc_n(v___x_584_, 2);
v___f_585_ = lean_alloc_closure((void*)(l_Std_Http_Headers_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_585_, 0, v___x_584_);
lean_closure_set(v___f_585_, 1, v_entries_578_);
v___x_586_ = ((lean_object*)(l_Std_Http_Headers_getAll___redArg___closed__9));
v_sz_587_ = lean_array_size(v___x_584_);
v___x_588_ = ((size_t)0ULL);
v_entries_589_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_586_, v___x_584_, v___f_585_, v_sz_587_, v___x_588_, v___x_584_);
lean_dec(v___x_584_);
v___x_590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_590_, 0, v_entries_589_);
return v___x_590_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_get_x3f(lean_object* v_headers_591_, lean_object* v_name_592_){
_start:
{
lean_object* v_entries_593_; lean_object* v_indexes_594_; lean_object* v___f_595_; lean_object* v___f_596_; uint8_t v___x_597_; 
v_entries_593_ = lean_ctor_get(v_headers_591_, 0);
v_indexes_594_ = lean_ctor_get(v_headers_591_, 1);
v___f_595_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_596_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
lean_inc_ref(v_name_592_);
v___x_597_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_595_, v___f_596_, v_indexes_594_, v_name_592_);
if (v___x_597_ == 0)
{
lean_object* v___x_598_; 
lean_dec_ref(v_name_592_);
v___x_598_ = lean_box(0);
return v___x_598_;
}
else
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v_entry_601_; lean_object* v___x_602_; lean_object* v_snd_603_; lean_object* v___x_604_; 
v___x_599_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v___f_595_, v___f_596_, v_indexes_594_, v_name_592_);
v___x_600_ = lean_unsigned_to_nat(0u);
v_entry_601_ = lean_array_fget(v___x_599_, v___x_600_);
lean_dec(v___x_599_);
v___x_602_ = lean_array_fget_borrowed(v_entries_593_, v_entry_601_);
lean_dec(v_entry_601_);
v_snd_603_ = lean_ctor_get(v___x_602_, 1);
lean_inc(v_snd_603_);
v___x_604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_604_, 0, v_snd_603_);
return v___x_604_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_get_x3f___boxed(lean_object* v_headers_605_, lean_object* v_name_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_Std_Http_Headers_get_x3f(v_headers_605_, v_name_606_);
lean_dec_ref(v_headers_605_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_hasEntry___lam__1(lean_object* v_value_608_, lean_object* v___x_609_, lean_object* v___x_610_, lean_object* v_a_611_, lean_object* v_x_612_, lean_object* v___y_613_){
_start:
{
uint8_t v___x_614_; 
v___x_614_ = l_Std_Http_Header_instBEqValue_beq(v_a_611_, v_value_608_);
if (v___x_614_ == 0)
{
lean_object* v___x_615_; 
lean_dec_ref(v_a_611_);
v___x_615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_615_, 0, v___x_609_);
return v___x_615_;
}
else
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
lean_dec_ref(v___x_609_);
v___x_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_616_, 0, v_a_611_);
v___x_617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_617_, 0, v___x_616_);
v___x_618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_618_, 0, v___x_617_);
lean_ctor_set(v___x_618_, 1, v___x_610_);
v___x_619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_619_, 0, v___x_618_);
return v___x_619_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_hasEntry___lam__1___boxed(lean_object* v_value_620_, lean_object* v___x_621_, lean_object* v___x_622_, lean_object* v_a_623_, lean_object* v_x_624_, lean_object* v___y_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Std_Http_Headers_hasEntry___lam__1(v_value_620_, v___x_621_, v___x_622_, v_a_623_, v_x_624_, v___y_625_);
lean_dec_ref(v___y_625_);
lean_dec_ref(v_value_620_);
return v_res_626_;
}
}
uint8_t l_Std_Http_Headers_hasEntry(lean_object* v_headers_630_, lean_object* v_name_631_, lean_object* v_value_632_){
_start:
{
lean_object* v_entries_633_; lean_object* v_indexes_634_; lean_object* v___f_635_; lean_object* v___f_636_; uint8_t v___x_637_; 
v_entries_633_ = lean_ctor_get(v_headers_630_, 0);
lean_inc_ref(v_entries_633_);
v_indexes_634_ = lean_ctor_get(v_headers_630_, 1);
lean_inc_ref(v_indexes_634_);
lean_dec_ref(v_headers_630_);
v___f_635_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_636_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
lean_inc_ref(v_name_631_);
v___x_637_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_635_, v___f_636_, v_indexes_634_, v_name_631_);
if (v___x_637_ == 0)
{
lean_dec_ref(v_indexes_634_);
lean_dec_ref(v_entries_633_);
lean_dec_ref(v_value_632_);
lean_dec_ref(v_name_631_);
return v___x_637_;
}
else
{
lean_object* v___x_638_; lean_object* v___f_639_; lean_object* v___x_640_; size_t v_sz_641_; size_t v___x_642_; lean_object* v_entries_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___f_646_; size_t v_sz_647_; lean_object* v___x_648_; lean_object* v_fst_649_; 
v___x_638_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v___f_635_, v___f_636_, v_indexes_634_, v_name_631_);
lean_dec_ref(v_indexes_634_);
lean_inc_n(v___x_638_, 2);
v___f_639_ = lean_alloc_closure((void*)(l_Std_Http_Headers_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_639_, 0, v___x_638_);
lean_closure_set(v___f_639_, 1, v_entries_633_);
v___x_640_ = ((lean_object*)(l_Std_Http_Headers_getAll___redArg___closed__9));
v_sz_641_ = lean_array_size(v___x_638_);
v___x_642_ = ((size_t)0ULL);
v_entries_643_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_640_, v___x_638_, v___f_639_, v_sz_641_, v___x_642_, v___x_638_);
lean_dec(v___x_638_);
v___x_644_ = lean_box(0);
v___x_645_ = ((lean_object*)(l_Std_Http_Headers_hasEntry___closed__0));
v___f_646_ = lean_alloc_closure((void*)(l_Std_Http_Headers_hasEntry___lam__1___boxed), 6, 3);
lean_closure_set(v___f_646_, 0, v_value_632_);
lean_closure_set(v___f_646_, 1, v___x_645_);
lean_closure_set(v___f_646_, 2, v___x_644_);
v_sz_647_ = lean_array_size(v_entries_643_);
v___x_648_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_640_, v_entries_643_, v___f_646_, v_sz_647_, v___x_642_, v___x_645_);
v_fst_649_ = lean_ctor_get(v___x_648_, 0);
lean_inc(v_fst_649_);
lean_dec(v___x_648_);
if (lean_obj_tag(v_fst_649_) == 0)
{
uint8_t v___x_650_; 
v___x_650_ = 0;
return v___x_650_;
}
else
{
lean_object* v_val_651_; 
v_val_651_ = lean_ctor_get(v_fst_649_, 0);
lean_inc(v_val_651_);
lean_dec_ref_known(v_fst_649_, 1);
if (lean_obj_tag(v_val_651_) == 0)
{
uint8_t v___x_652_; 
v___x_652_ = 0;
return v___x_652_;
}
else
{
lean_dec_ref_known(v_val_651_, 1);
return v___x_637_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Headers_hasEntry_0interp(lean_interpreter_value* stack)
{
lean_object* v_headers_630_ = stack[0].m_obj;
lean_object* v_name_631_ = stack[1].m_obj;
lean_object* v_value_632_ = stack[2].m_obj;
uint8_t v_res_653_;
v_res_653_ = l_Std_Http_Headers_hasEntry(v_headers_630_, v_name_631_, v_value_632_);
stack->m_num = v_res_653_;
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_hasEntry___boxed(lean_object* v_headers_654_, lean_object* v_name_655_, lean_object* v_value_656_){
_start:
{
uint8_t v_res_657_; lean_object* v_r_658_; 
v_res_657_ = l_Std_Http_Headers_hasEntry(v_headers_654_, v_name_655_, v_value_656_);
v_r_658_ = lean_box(v_res_657_);
return v_r_658_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_getLast_x3f(lean_object* v_headers_659_, lean_object* v_name_660_){
_start:
{
lean_object* v_entries_661_; lean_object* v_indexes_662_; lean_object* v___f_663_; lean_object* v___f_664_; uint8_t v___x_665_; 
v_entries_661_ = lean_ctor_get(v_headers_659_, 0);
lean_inc_ref(v_entries_661_);
v_indexes_662_ = lean_ctor_get(v_headers_659_, 1);
lean_inc_ref(v_indexes_662_);
lean_dec_ref(v_headers_659_);
v___f_663_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_664_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
lean_inc_ref(v_name_660_);
v___x_665_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_663_, v___f_664_, v_indexes_662_, v_name_660_);
if (v___x_665_ == 0)
{
lean_object* v___x_666_; 
lean_dec_ref(v_indexes_662_);
lean_dec_ref(v_entries_661_);
lean_dec_ref(v_name_660_);
v___x_666_ = lean_box(0);
return v___x_666_;
}
else
{
lean_object* v___x_667_; lean_object* v___f_668_; lean_object* v___x_669_; size_t v_sz_670_; size_t v___x_671_; lean_object* v_entries_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; uint8_t v___x_676_; 
v___x_667_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v___f_663_, v___f_664_, v_indexes_662_, v_name_660_);
lean_dec_ref(v_indexes_662_);
lean_inc_n(v___x_667_, 2);
v___f_668_ = lean_alloc_closure((void*)(l_Std_Http_Headers_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_668_, 0, v___x_667_);
lean_closure_set(v___f_668_, 1, v_entries_661_);
v___x_669_ = ((lean_object*)(l_Std_Http_Headers_getAll___redArg___closed__9));
v_sz_670_ = lean_array_size(v___x_667_);
v___x_671_ = ((size_t)0ULL);
v_entries_672_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_669_, v___x_667_, v___f_668_, v_sz_670_, v___x_671_, v___x_667_);
lean_dec(v___x_667_);
v___x_673_ = lean_array_get_size(v_entries_672_);
v___x_674_ = lean_unsigned_to_nat(1u);
v___x_675_ = lean_nat_sub(v___x_673_, v___x_674_);
v___x_676_ = lean_nat_dec_lt(v___x_675_, v___x_673_);
if (v___x_676_ == 0)
{
lean_object* v___x_677_; 
lean_dec(v___x_675_);
lean_dec(v_entries_672_);
v___x_677_ = lean_box(0);
return v___x_677_;
}
else
{
lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_678_ = lean_array_fget(v_entries_672_, v___x_675_);
lean_dec(v___x_675_);
lean_dec(v_entries_672_);
v___x_679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_679_, 0, v___x_678_);
return v___x_679_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_getD(lean_object* v_headers_680_, lean_object* v_name_681_, lean_object* v_d_682_){
_start:
{
lean_object* v_entries_683_; lean_object* v_indexes_684_; lean_object* v___f_685_; lean_object* v___f_686_; uint8_t v___x_687_; 
v_entries_683_ = lean_ctor_get(v_headers_680_, 0);
v_indexes_684_ = lean_ctor_get(v_headers_680_, 1);
v___f_685_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_686_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
lean_inc_ref(v_name_681_);
v___x_687_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_685_, v___f_686_, v_indexes_684_, v_name_681_);
if (v___x_687_ == 0)
{
lean_dec_ref(v_name_681_);
lean_inc_ref(v_d_682_);
return v_d_682_;
}
else
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v_entry_690_; lean_object* v___x_691_; lean_object* v_snd_692_; 
v___x_688_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v___f_685_, v___f_686_, v_indexes_684_, v_name_681_);
v___x_689_ = lean_unsigned_to_nat(0u);
v_entry_690_ = lean_array_fget(v___x_688_, v___x_689_);
lean_dec(v___x_688_);
v___x_691_ = lean_array_fget_borrowed(v_entries_683_, v_entry_690_);
lean_dec(v_entry_690_);
v_snd_692_ = lean_ctor_get(v___x_691_, 1);
lean_inc(v_snd_692_);
return v_snd_692_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_getD___boxed(lean_object* v_headers_693_, lean_object* v_name_694_, lean_object* v_d_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l_Std_Http_Headers_getD(v_headers_693_, v_name_694_, v_d_695_);
lean_dec_ref(v_d_695_);
lean_dec_ref(v_headers_693_);
return v_res_696_;
}
}
static lean_object* _init_l_Std_Http_Headers_get_x21___closed__4(void){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_701_ = ((lean_object*)(l_Std_Http_Headers_get_x21___closed__3));
v___x_702_ = lean_unsigned_to_nat(14u);
v___x_703_ = lean_unsigned_to_nat(22u);
v___x_704_ = ((lean_object*)(l_Std_Http_Headers_get_x21___closed__2));
v___x_705_ = ((lean_object*)(l_Std_Http_Headers_get_x21___closed__1));
v___x_706_ = l_mkPanicMessageWithDecl(v___x_705_, v___x_704_, v___x_703_, v___x_702_, v___x_701_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_get_x21(lean_object* v_headers_707_, lean_object* v_name_708_){
_start:
{
lean_object* v_entries_709_; lean_object* v_indexes_710_; lean_object* v___f_711_; lean_object* v___f_712_; uint8_t v___x_713_; 
v_entries_709_ = lean_ctor_get(v_headers_707_, 0);
v_indexes_710_ = lean_ctor_get(v_headers_707_, 1);
v___f_711_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_712_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
lean_inc_ref(v_name_708_);
v___x_713_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_711_, v___f_712_, v_indexes_710_, v_name_708_);
if (v___x_713_ == 0)
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
lean_dec_ref(v_name_708_);
v___x_714_ = ((lean_object*)(l_Std_Http_Headers_get_x21___closed__0));
v___x_715_ = lean_obj_once(&l_Std_Http_Headers_get_x21___closed__4, &l_Std_Http_Headers_get_x21___closed__4_once, _init_l_Std_Http_Headers_get_x21___closed__4);
v___x_716_ = l_panic___redArg(v___x_714_, v___x_715_);
return v___x_716_;
}
else
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v_entry_719_; lean_object* v___x_720_; lean_object* v_snd_721_; 
v___x_717_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v___f_711_, v___f_712_, v_indexes_710_, v_name_708_);
v___x_718_ = lean_unsigned_to_nat(0u);
v_entry_719_ = lean_array_fget(v___x_717_, v___x_718_);
lean_dec(v___x_717_);
v___x_720_ = lean_array_fget_borrowed(v_entries_709_, v_entry_719_);
lean_dec(v_entry_719_);
v_snd_721_ = lean_ctor_get(v___x_720_, 1);
lean_inc(v_snd_721_);
return v_snd_721_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_get_x21___boxed(lean_object* v_headers_722_, lean_object* v_name_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Std_Http_Headers_get_x21(v_headers_722_, v_name_723_);
lean_dec_ref(v_headers_722_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_insert___lam__0(lean_object* v_i_725_, lean_object* v_x_726_){
_start:
{
if (lean_obj_tag(v_x_726_) == 0)
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_727_ = lean_unsigned_to_nat(1u);
v___x_728_ = lean_mk_empty_array_with_capacity(v___x_727_);
v___x_729_ = lean_array_push(v___x_728_, v_i_725_);
v___x_730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_730_, 0, v___x_729_);
return v___x_730_;
}
else
{
lean_object* v_val_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_739_; 
v_val_731_ = lean_ctor_get(v_x_726_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v_x_726_);
if (v_isSharedCheck_739_ == 0)
{
v___x_733_ = v_x_726_;
v_isShared_734_ = v_isSharedCheck_739_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_val_731_);
lean_dec(v_x_726_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_739_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_735_; lean_object* v___x_737_; 
v___x_735_ = lean_array_push(v_val_731_, v_i_725_);
if (v_isShared_734_ == 0)
{
lean_ctor_set(v___x_733_, 0, v___x_735_);
v___x_737_ = v___x_733_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_735_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_insert(lean_object* v_headers_740_, lean_object* v_key_741_, lean_object* v_value_742_){
_start:
{
lean_object* v_entries_743_; lean_object* v_indexes_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_758_; 
v_entries_743_ = lean_ctor_get(v_headers_740_, 0);
v_indexes_744_ = lean_ctor_get(v_headers_740_, 1);
v_isSharedCheck_758_ = !lean_is_exclusive(v_headers_740_);
if (v_isSharedCheck_758_ == 0)
{
v___x_746_ = v_headers_740_;
v_isShared_747_ = v_isSharedCheck_758_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_indexes_744_);
lean_inc(v_entries_743_);
lean_dec(v_headers_740_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_758_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___f_748_; lean_object* v___f_749_; lean_object* v_i_750_; lean_object* v_f_751_; lean_object* v___x_752_; lean_object* v_entries_753_; lean_object* v_indexes_754_; lean_object* v___x_756_; 
v___f_748_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_749_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v_i_750_ = lean_array_get_size(v_entries_743_);
v_f_751_ = lean_alloc_closure((void*)(l_Std_Http_Headers_insert___lam__0), 2, 1);
lean_closure_set(v_f_751_, 0, v_i_750_);
lean_inc_ref(v_key_741_);
v___x_752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_752_, 0, v_key_741_);
lean_ctor_set(v___x_752_, 1, v_value_742_);
v_entries_753_ = lean_array_push(v_entries_743_, v___x_752_);
v_indexes_754_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_748_, v___f_749_, v_indexes_744_, v_key_741_, v_f_751_);
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 1, v_indexes_754_);
lean_ctor_set(v___x_746_, 0, v_entries_753_);
v___x_756_ = v___x_746_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_entries_753_);
lean_ctor_set(v_reuseFailAlloc_757_, 1, v_indexes_754_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_insert_x21(lean_object* v_headers_759_, lean_object* v_name_760_, lean_object* v_value_761_){
_start:
{
lean_object* v_entries_762_; lean_object* v_indexes_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_779_; 
v_entries_762_ = lean_ctor_get(v_headers_759_, 0);
v_indexes_763_ = lean_ctor_get(v_headers_759_, 1);
v_isSharedCheck_779_ = !lean_is_exclusive(v_headers_759_);
if (v_isSharedCheck_779_ == 0)
{
v___x_765_ = v_headers_759_;
v_isShared_766_ = v_isSharedCheck_779_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_indexes_763_);
lean_inc(v_entries_762_);
lean_dec(v_headers_759_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_779_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___f_769_; lean_object* v___f_770_; lean_object* v_i_771_; lean_object* v_f_772_; lean_object* v___x_773_; lean_object* v_entries_774_; lean_object* v_indexes_775_; lean_object* v___x_777_; 
v___x_767_ = l_Std_Http_Header_Name_ofString_x21(v_name_760_);
v___x_768_ = l_Std_Http_Header_Value_ofString_x21(v_value_761_);
v___f_769_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_770_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v_i_771_ = lean_array_get_size(v_entries_762_);
v_f_772_ = lean_alloc_closure((void*)(l_Std_Http_Headers_insert___lam__0), 2, 1);
lean_closure_set(v_f_772_, 0, v_i_771_);
lean_inc_ref(v___x_767_);
v___x_773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_773_, 0, v___x_767_);
lean_ctor_set(v___x_773_, 1, v___x_768_);
v_entries_774_ = lean_array_push(v_entries_762_, v___x_773_);
v_indexes_775_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_769_, v___f_770_, v_indexes_763_, v___x_767_, v_f_772_);
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 1, v_indexes_775_);
lean_ctor_set(v___x_765_, 0, v_entries_774_);
v___x_777_ = v___x_765_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_entries_774_);
lean_ctor_set(v_reuseFailAlloc_778_, 1, v_indexes_775_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_insert_x3f(lean_object* v_headers_780_, lean_object* v_name_781_, lean_object* v_value_782_){
_start:
{
lean_object* v___x_783_; 
v___x_783_ = l_Std_Http_Header_Name_ofString_x3f(v_name_781_);
if (lean_obj_tag(v___x_783_) == 0)
{
lean_object* v___x_784_; 
lean_dec_ref(v_value_782_);
lean_dec_ref(v_headers_780_);
v___x_784_ = lean_box(0);
return v___x_784_;
}
else
{
lean_object* v_val_785_; lean_object* v___x_786_; 
v_val_785_ = lean_ctor_get(v___x_783_, 0);
lean_inc(v_val_785_);
lean_dec_ref_known(v___x_783_, 1);
v___x_786_ = l_Std_Http_Header_Value_ofString_x3f(v_value_782_);
if (lean_obj_tag(v___x_786_) == 0)
{
lean_object* v___x_787_; 
lean_dec(v_val_785_);
lean_dec_ref(v_headers_780_);
v___x_787_ = lean_box(0);
return v___x_787_;
}
else
{
lean_object* v_val_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_811_; 
v_val_788_ = lean_ctor_get(v___x_786_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_811_ == 0)
{
v___x_790_ = v___x_786_;
v_isShared_791_ = v_isSharedCheck_811_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_val_788_);
lean_dec(v___x_786_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_811_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v_entries_792_; lean_object* v_indexes_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_810_; 
v_entries_792_ = lean_ctor_get(v_headers_780_, 0);
v_indexes_793_ = lean_ctor_get(v_headers_780_, 1);
v_isSharedCheck_810_ = !lean_is_exclusive(v_headers_780_);
if (v_isSharedCheck_810_ == 0)
{
v___x_795_ = v_headers_780_;
v_isShared_796_ = v_isSharedCheck_810_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_indexes_793_);
lean_inc(v_entries_792_);
lean_dec(v_headers_780_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_810_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___f_797_; lean_object* v___f_798_; lean_object* v_i_799_; lean_object* v_f_800_; lean_object* v___x_801_; lean_object* v_entries_802_; lean_object* v_indexes_803_; lean_object* v___x_805_; 
v___f_797_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_798_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v_i_799_ = lean_array_get_size(v_entries_792_);
v_f_800_ = lean_alloc_closure((void*)(l_Std_Http_Headers_insert___lam__0), 2, 1);
lean_closure_set(v_f_800_, 0, v_i_799_);
lean_inc(v_val_785_);
v___x_801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_801_, 0, v_val_785_);
lean_ctor_set(v___x_801_, 1, v_val_788_);
v_entries_802_ = lean_array_push(v_entries_792_, v___x_801_);
v_indexes_803_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_797_, v___f_798_, v_indexes_793_, v_val_785_, v_f_800_);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 1, v_indexes_803_);
lean_ctor_set(v___x_795_, 0, v_entries_802_);
v___x_805_ = v___x_795_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_entries_802_);
lean_ctor_set(v_reuseFailAlloc_809_, 1, v_indexes_803_);
v___x_805_ = v_reuseFailAlloc_809_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
lean_object* v___x_807_; 
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 0, v___x_805_);
v___x_807_ = v___x_790_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_805_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_insertMany___lam__1(lean_object* v_key_812_, lean_object* v___f_813_, lean_object* v___f_814_, lean_object* v_x1_815_, lean_object* v_x2_816_){
_start:
{
lean_object* v_entries_817_; lean_object* v_indexes_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_830_; 
v_entries_817_ = lean_ctor_get(v_x1_815_, 0);
v_indexes_818_ = lean_ctor_get(v_x1_815_, 1);
v_isSharedCheck_830_ = !lean_is_exclusive(v_x1_815_);
if (v_isSharedCheck_830_ == 0)
{
v___x_820_ = v_x1_815_;
v_isShared_821_ = v_isSharedCheck_830_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_indexes_818_);
lean_inc(v_entries_817_);
lean_dec(v_x1_815_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_830_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v_i_822_; lean_object* v_f_823_; lean_object* v___x_824_; lean_object* v_entries_825_; lean_object* v_indexes_826_; lean_object* v___x_828_; 
v_i_822_ = lean_array_get_size(v_entries_817_);
v_f_823_ = lean_alloc_closure((void*)(l_Std_Http_Headers_insert___lam__0), 2, 1);
lean_closure_set(v_f_823_, 0, v_i_822_);
lean_inc_ref(v_key_812_);
v___x_824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_824_, 0, v_key_812_);
lean_ctor_set(v___x_824_, 1, v_x2_816_);
v_entries_825_ = lean_array_push(v_entries_817_, v___x_824_);
v_indexes_826_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_813_, v___f_814_, v_indexes_818_, v_key_812_, v_f_823_);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 1, v_indexes_826_);
lean_ctor_set(v___x_820_, 0, v_entries_825_);
v___x_828_ = v___x_820_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_entries_825_);
lean_ctor_set(v_reuseFailAlloc_829_, 1, v_indexes_826_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_insertMany(lean_object* v_headers_831_, lean_object* v_key_832_, lean_object* v_values_833_){
_start:
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; uint8_t v___x_837_; 
v___x_834_ = lean_unsigned_to_nat(0u);
v___x_835_ = lean_array_get_size(v_values_833_);
v___x_836_ = ((lean_object*)(l_Std_Http_Headers_getAll___redArg___closed__9));
v___x_837_ = lean_nat_dec_lt(v___x_834_, v___x_835_);
if (v___x_837_ == 0)
{
lean_dec_ref(v_values_833_);
lean_dec_ref(v_key_832_);
return v_headers_831_;
}
else
{
lean_object* v___f_838_; lean_object* v___f_839_; lean_object* v___f_840_; size_t v___x_841_; size_t v___x_842_; lean_object* v___x_843_; 
v___f_838_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_839_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v___f_840_ = lean_alloc_closure((void*)(l_Std_Http_Headers_insertMany___lam__1), 5, 3);
lean_closure_set(v___f_840_, 0, v_key_832_);
lean_closure_set(v___f_840_, 1, v___f_838_);
lean_closure_set(v___f_840_, 2, v___f_839_);
v___x_841_ = ((size_t)0ULL);
v___x_842_ = lean_usize_of_nat(v___x_835_);
v___x_843_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_836_, v___f_840_, v_values_833_, v___x_841_, v___x_842_, v_headers_831_);
return v___x_843_;
}
}
}
static lean_object* _init_l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_846_ = lean_obj_once(&l_Std_Http_instInhabitedHeaders_default___closed__2, &l_Std_Http_instInhabitedHeaders_default___closed__2_once, _init_l_Std_Http_instInhabitedHeaders_default___closed__2);
v___x_847_ = ((lean_object*)(l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___redArg___closed__0));
v___x_848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_848_, 0, v___x_847_);
lean_ctor_set(v___x_848_, 1, v___x_846_);
return v___x_848_;
}
}
lean_object* l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___redArg(){
_start:
{
lean_object* v___x_850_; 
v___x_850_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___redArg___closed__1, &l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___redArg___closed__1_once, _init_l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___redArg___closed__1);
return v___x_850_;
}
}
LEAN_EXPORT void l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_851_;
v_res_851_ = l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___redArg();
stack->m_obj
 = v_res_851_;
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___redArg___boxed(lean_object* v___dummy_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___redArg();
return v_res_853_;
}
}
static lean_object* _init_l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__0(void){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___redArg();
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0(lean_object* v_00_u03b2_855_){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__0, &l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__0_once, _init_l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__0);
return v___x_856_;
}
}
static lean_object* _init_l_Std_Http_Headers_empty(void){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__0, &l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__0_once, _init_l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__0);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__3(lean_object* v_i_858_, lean_object* v_a_859_, lean_object* v_x_860_){
_start:
{
if (lean_obj_tag(v_x_860_) == 0)
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v_val_863_; lean_object* v___x_864_; 
v___x_861_ = lean_box(0);
v___x_862_ = l_Std_Http_Headers_insert___lam__0(v_i_858_, v___x_861_);
v_val_863_ = lean_ctor_get(v___x_862_, 0);
lean_inc(v_val_863_);
lean_dec(v___x_862_);
v___x_864_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_864_, 0, v_a_859_);
lean_ctor_set(v___x_864_, 1, v_val_863_);
lean_ctor_set(v___x_864_, 2, v_x_860_);
return v___x_864_;
}
else
{
lean_object* v_key_865_; lean_object* v_value_866_; lean_object* v_tail_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_882_; 
v_key_865_ = lean_ctor_get(v_x_860_, 0);
v_value_866_ = lean_ctor_get(v_x_860_, 1);
v_tail_867_ = lean_ctor_get(v_x_860_, 2);
v_isSharedCheck_882_ = !lean_is_exclusive(v_x_860_);
if (v_isSharedCheck_882_ == 0)
{
v___x_869_ = v_x_860_;
v_isShared_870_ = v_isSharedCheck_882_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_tail_867_);
lean_inc(v_value_866_);
lean_inc(v_key_865_);
lean_dec(v_x_860_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_882_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
uint8_t v___x_871_; 
v___x_871_ = lean_string_dec_eq(v_key_865_, v_a_859_);
if (v___x_871_ == 0)
{
lean_object* v_tail_872_; lean_object* v___x_874_; 
v_tail_872_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__3(v_i_858_, v_a_859_, v_tail_867_);
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 2, v_tail_872_);
v___x_874_ = v___x_869_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_key_865_);
lean_ctor_set(v_reuseFailAlloc_875_, 1, v_value_866_);
lean_ctor_set(v_reuseFailAlloc_875_, 2, v_tail_872_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
else
{
lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v_val_878_; lean_object* v___x_880_; 
lean_dec(v_key_865_);
v___x_876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_876_, 0, v_value_866_);
v___x_877_ = l_Std_Http_Headers_insert___lam__0(v_i_858_, v___x_876_);
v_val_878_ = lean_ctor_get(v___x_877_, 0);
lean_inc(v_val_878_);
lean_dec(v___x_877_);
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 1, v_val_878_);
lean_ctor_set(v___x_869_, 0, v_a_859_);
v___x_880_ = v___x_869_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_a_859_);
lean_ctor_set(v_reuseFailAlloc_881_, 1, v_val_878_);
lean_ctor_set(v_reuseFailAlloc_881_, 2, v_tail_867_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_x_883_, lean_object* v_x_884_){
_start:
{
if (lean_obj_tag(v_x_884_) == 0)
{
return v_x_883_;
}
else
{
lean_object* v_key_885_; lean_object* v_value_886_; lean_object* v_tail_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_910_; 
v_key_885_ = lean_ctor_get(v_x_884_, 0);
v_value_886_ = lean_ctor_get(v_x_884_, 1);
v_tail_887_ = lean_ctor_get(v_x_884_, 2);
v_isSharedCheck_910_ = !lean_is_exclusive(v_x_884_);
if (v_isSharedCheck_910_ == 0)
{
v___x_889_ = v_x_884_;
v_isShared_890_ = v_isSharedCheck_910_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_tail_887_);
lean_inc(v_value_886_);
lean_inc(v_key_885_);
lean_dec(v_x_884_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_910_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_891_; uint64_t v___x_892_; uint64_t v___x_893_; uint64_t v___x_894_; uint64_t v_fold_895_; uint64_t v___x_896_; uint64_t v___x_897_; uint64_t v___x_898_; size_t v___x_899_; size_t v___x_900_; size_t v___x_901_; size_t v___x_902_; size_t v___x_903_; lean_object* v___x_904_; lean_object* v___x_906_; 
v___x_891_ = lean_array_get_size(v_x_883_);
v___x_892_ = lean_string_hash(v_key_885_);
v___x_893_ = 32ULL;
v___x_894_ = lean_uint64_shift_right(v___x_892_, v___x_893_);
v_fold_895_ = lean_uint64_xor(v___x_892_, v___x_894_);
v___x_896_ = 16ULL;
v___x_897_ = lean_uint64_shift_right(v_fold_895_, v___x_896_);
v___x_898_ = lean_uint64_xor(v_fold_895_, v___x_897_);
v___x_899_ = lean_uint64_to_usize(v___x_898_);
v___x_900_ = lean_usize_of_nat(v___x_891_);
v___x_901_ = ((size_t)1ULL);
v___x_902_ = lean_usize_sub(v___x_900_, v___x_901_);
v___x_903_ = lean_usize_land(v___x_899_, v___x_902_);
v___x_904_ = lean_array_uget_borrowed(v_x_883_, v___x_903_);
lean_inc(v___x_904_);
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 2, v___x_904_);
v___x_906_ = v___x_889_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_key_885_);
lean_ctor_set(v_reuseFailAlloc_909_, 1, v_value_886_);
lean_ctor_set(v_reuseFailAlloc_909_, 2, v___x_904_);
v___x_906_ = v_reuseFailAlloc_909_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
lean_object* v___x_907_; 
v___x_907_ = lean_array_uset(v_x_883_, v___x_903_, v___x_906_);
v_x_883_ = v___x_907_;
v_x_884_ = v_tail_887_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_i_911_, lean_object* v_source_912_, lean_object* v_target_913_){
_start:
{
lean_object* v___x_914_; uint8_t v___x_915_; 
v___x_914_ = lean_array_get_size(v_source_912_);
v___x_915_ = lean_nat_dec_lt(v_i_911_, v___x_914_);
if (v___x_915_ == 0)
{
lean_dec_ref(v_source_912_);
lean_dec(v_i_911_);
return v_target_913_;
}
else
{
lean_object* v_es_916_; lean_object* v___x_917_; lean_object* v_source_918_; lean_object* v_target_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v_es_916_ = lean_array_fget(v_source_912_, v_i_911_);
v___x_917_ = lean_box(0);
v_source_918_ = lean_array_fset(v_source_912_, v_i_911_, v___x_917_);
v_target_919_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_target_913_, v_es_916_);
v___x_920_ = lean_unsigned_to_nat(1u);
v___x_921_ = lean_nat_add(v_i_911_, v___x_920_);
lean_dec(v_i_911_);
v_i_911_ = v___x_921_;
v_source_912_ = v_source_918_;
v_target_913_ = v_target_919_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2___redArg(lean_object* v_data_923_){
_start:
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v_nbuckets_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_924_ = lean_array_get_size(v_data_923_);
v___x_925_ = lean_unsigned_to_nat(2u);
v_nbuckets_926_ = lean_nat_mul(v___x_924_, v___x_925_);
v___x_927_ = lean_unsigned_to_nat(0u);
v___x_928_ = lean_box(0);
v___x_929_ = lean_mk_array(v_nbuckets_926_, v___x_928_);
v___x_930_ = lean_array_propagate_mark(v_data_923_, v___x_929_);
v___x_931_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2_spec__3___redArg(v___x_927_, v_data_923_, v___x_930_);
return v___x_931_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1___redArg(lean_object* v_a_932_, lean_object* v_x_933_){
_start:
{
if (lean_obj_tag(v_x_933_) == 0)
{
uint8_t v___x_934_; 
v___x_934_ = 0;
return v___x_934_;
}
else
{
lean_object* v_key_935_; lean_object* v_tail_936_; uint8_t v___x_937_; 
v_key_935_ = lean_ctor_get(v_x_933_, 0);
v_tail_936_ = lean_ctor_get(v_x_933_, 2);
v___x_937_ = lean_string_dec_eq(v_key_935_, v_a_932_);
if (v___x_937_ == 0)
{
v_x_933_ = v_tail_936_;
goto _start;
}
else
{
return v___x_937_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_932_ = stack[0].m_obj;
lean_object* v_x_933_ = stack[1].m_obj;
uint8_t v_res_939_;
v_res_939_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1___redArg(v_a_932_, v_x_933_);
stack->m_num = v_res_939_;
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
lean_dec_ref_known(v_x_1000_, 2);
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
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0___redArg(lean_object* v_pairs_1017_){
_start:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__0, &l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__0_once, _init_l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__0);
v___x_1019_ = l_List_foldl___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1___redArg(v___x_1018_, v_pairs_1017_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_ofList(lean_object* v_pairs_1020_){
_start:
{
lean_object* v___x_1021_; 
v___x_1021_ = l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0___redArg(v_pairs_1020_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0(lean_object* v_00_u03b2_1022_, lean_object* v_inst_1023_, lean_object* v_inst_1024_, lean_object* v_pairs_1025_){
_start:
{
lean_object* v___x_1026_; 
v___x_1026_ = l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0___redArg(v_pairs_1025_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1(lean_object* v_00_u03b2_1027_, lean_object* v_x_1028_, lean_object* v_x_1029_){
_start:
{
lean_object* v___x_1030_; 
v___x_1030_ = l_List_foldl___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1___redArg(v_x_1028_, v_x_1029_);
return v___x_1030_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1031_, lean_object* v_a_1032_, lean_object* v_x_1033_){
_start:
{
uint8_t v___x_1034_; 
v___x_1034_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1___redArg(v_a_1032_, v_x_1033_);
return v___x_1034_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1032_ = stack[1].m_obj;
lean_object* v_x_1033_ = stack[2].m_obj;
uint8_t v_res_1035_;
v_res_1035_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1(lean_box(0), v_a_1032_, v_x_1033_);
stack->m_num = v_res_1035_;
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
uint8_t l_Std_Http_Headers_contains(lean_object* v_headers_1053_, lean_object* v_name_1054_){
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
LEAN_EXPORT void l_Std_Http_Headers_contains_0interp(lean_interpreter_value* stack)
{
lean_object* v_headers_1053_ = stack[0].m_obj;
lean_object* v_name_1054_ = stack[1].m_obj;
uint8_t v_res_1059_;
v_res_1059_ = l_Std_Http_Headers_contains(v_headers_1053_, v_name_1054_);
stack->m_num = v_res_1059_;
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_contains___boxed(lean_object* v_headers_1060_, lean_object* v_name_1061_){
_start:
{
uint8_t v_res_1062_; lean_object* v_r_1063_; 
v_res_1062_ = l_Std_Http_Headers_contains(v_headers_1060_, v_name_1061_);
lean_dec_ref(v_headers_1060_);
v_r_1063_ = lean_box(v_res_1062_);
return v_r_1063_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_erase___lam__1(lean_object* v_name_1064_, lean_object* v___f_1065_, lean_object* v___f_1066_, lean_object* v_x1_1067_, lean_object* v_x2_1068_){
_start:
{
lean_object* v_fst_1069_; uint8_t v___x_1070_; 
v_fst_1069_ = lean_ctor_get(v_x2_1068_, 0);
lean_inc(v_fst_1069_);
v___x_1070_ = lean_string_dec_eq(v_name_1064_, v_fst_1069_);
if (v___x_1070_ == 0)
{
lean_object* v_entries_1071_; lean_object* v_indexes_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1083_; 
v_entries_1071_ = lean_ctor_get(v_x1_1067_, 0);
v_indexes_1072_ = lean_ctor_get(v_x1_1067_, 1);
v_isSharedCheck_1083_ = !lean_is_exclusive(v_x1_1067_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1074_ = v_x1_1067_;
v_isShared_1075_ = v_isSharedCheck_1083_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_indexes_1072_);
lean_inc(v_entries_1071_);
lean_dec(v_x1_1067_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1083_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v_i_1076_; lean_object* v_f_1077_; lean_object* v_entries_1078_; lean_object* v_indexes_1079_; lean_object* v___x_1081_; 
v_i_1076_ = lean_array_get_size(v_entries_1071_);
v_f_1077_ = lean_alloc_closure((void*)(l_Std_Http_Headers_insert___lam__0), 2, 1);
lean_closure_set(v_f_1077_, 0, v_i_1076_);
v_entries_1078_ = lean_array_push(v_entries_1071_, v_x2_1068_);
v_indexes_1079_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_1065_, v___f_1066_, v_indexes_1072_, v_fst_1069_, v_f_1077_);
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 1, v_indexes_1079_);
lean_ctor_set(v___x_1074_, 0, v_entries_1078_);
v___x_1081_ = v___x_1074_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_entries_1078_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v_indexes_1079_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
else
{
lean_dec(v_fst_1069_);
lean_dec_ref(v_x2_1068_);
lean_dec_ref(v___f_1066_);
lean_dec_ref(v___f_1065_);
return v_x1_1067_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_erase___lam__1___boxed(lean_object* v_name_1084_, lean_object* v___f_1085_, lean_object* v___f_1086_, lean_object* v_x1_1087_, lean_object* v_x2_1088_){
_start:
{
lean_object* v_res_1089_; 
v_res_1089_ = l_Std_Http_Headers_erase___lam__1(v_name_1084_, v___f_1085_, v___f_1086_, v_x1_1087_, v_x2_1088_);
lean_dec_ref(v_name_1084_);
return v_res_1089_;
}
}
static lean_object* _init_l_Std_Http_Headers_erase___closed__0(void){
_start:
{
lean_object* v___x_1090_; 
v___x_1090_ = l_Std_Internal_IndexMultiMap_empty___redArg();
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_erase(lean_object* v_headers_1091_, lean_object* v_name_1092_){
_start:
{
lean_object* v___f_1093_; lean_object* v___f_1094_; uint8_t v___x_1095_; 
v___f_1093_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_1094_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
lean_inc_ref(v_name_1092_);
v___x_1095_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_1093_, v___f_1094_, v_name_1092_, v_headers_1091_);
if (v___x_1095_ == 0)
{
lean_dec_ref(v_name_1092_);
return v_headers_1091_;
}
else
{
lean_object* v_entries_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; uint8_t v___x_1101_; 
v_entries_1096_ = lean_ctor_get(v_headers_1091_, 0);
lean_inc_ref(v_entries_1096_);
lean_dec_ref(v_headers_1091_);
v___x_1097_ = lean_obj_once(&l_Std_Http_Headers_erase___closed__0, &l_Std_Http_Headers_erase___closed__0_once, _init_l_Std_Http_Headers_erase___closed__0);
v___x_1098_ = lean_unsigned_to_nat(0u);
v___x_1099_ = lean_array_get_size(v_entries_1096_);
v___x_1100_ = ((lean_object*)(l_Std_Http_Headers_getAll___redArg___closed__9));
v___x_1101_ = lean_nat_dec_lt(v___x_1098_, v___x_1099_);
if (v___x_1101_ == 0)
{
lean_dec_ref(v_entries_1096_);
lean_dec_ref(v_name_1092_);
return v___x_1097_;
}
else
{
lean_object* v___f_1102_; size_t v___x_1103_; size_t v___x_1104_; lean_object* v___x_1105_; 
v___f_1102_ = lean_alloc_closure((void*)(l_Std_Http_Headers_erase___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1102_, 0, v_name_1092_);
lean_closure_set(v___f_1102_, 1, v___f_1093_);
lean_closure_set(v___f_1102_, 2, v___f_1094_);
v___x_1103_ = ((size_t)0ULL);
v___x_1104_ = lean_usize_of_nat(v___x_1099_);
v___x_1105_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1100_, v___f_1102_, v_entries_1096_, v___x_1103_, v___x_1104_, v___x_1097_);
return v___x_1105_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_eraseMany___lam__1(lean_object* v___f_1106_, lean_object* v_names_1107_, lean_object* v___f_1108_, lean_object* v_x1_1109_, lean_object* v_x2_1110_){
_start:
{
lean_object* v_fst_1111_; uint8_t v___x_1112_; 
v_fst_1111_ = lean_ctor_get(v_x2_1110_, 0);
lean_inc_n(v_fst_1111_, 2);
lean_inc_ref(v___f_1106_);
v___x_1112_ = l_Array_contains___redArg(v___f_1106_, v_names_1107_, v_fst_1111_);
if (v___x_1112_ == 0)
{
lean_object* v_entries_1113_; lean_object* v_indexes_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1125_; 
v_entries_1113_ = lean_ctor_get(v_x1_1109_, 0);
v_indexes_1114_ = lean_ctor_get(v_x1_1109_, 1);
v_isSharedCheck_1125_ = !lean_is_exclusive(v_x1_1109_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1116_ = v_x1_1109_;
v_isShared_1117_ = v_isSharedCheck_1125_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_indexes_1114_);
lean_inc(v_entries_1113_);
lean_dec(v_x1_1109_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1125_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v_i_1118_; lean_object* v_f_1119_; lean_object* v_entries_1120_; lean_object* v_indexes_1121_; lean_object* v___x_1123_; 
v_i_1118_ = lean_array_get_size(v_entries_1113_);
v_f_1119_ = lean_alloc_closure((void*)(l_Std_Http_Headers_insert___lam__0), 2, 1);
lean_closure_set(v_f_1119_, 0, v_i_1118_);
v_entries_1120_ = lean_array_push(v_entries_1113_, v_x2_1110_);
v_indexes_1121_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_1106_, v___f_1108_, v_indexes_1114_, v_fst_1111_, v_f_1119_);
if (v_isShared_1117_ == 0)
{
lean_ctor_set(v___x_1116_, 1, v_indexes_1121_);
lean_ctor_set(v___x_1116_, 0, v_entries_1120_);
v___x_1123_ = v___x_1116_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_entries_1120_);
lean_ctor_set(v_reuseFailAlloc_1124_, 1, v_indexes_1121_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
else
{
lean_dec(v_fst_1111_);
lean_dec_ref(v_x2_1110_);
lean_dec_ref(v___f_1108_);
lean_dec_ref(v___f_1106_);
return v_x1_1109_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_eraseMany(lean_object* v_headers_1126_, lean_object* v_names_1127_){
_start:
{
lean_object* v_entries_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; uint8_t v___x_1133_; 
v_entries_1128_ = lean_ctor_get(v_headers_1126_, 0);
lean_inc_ref(v_entries_1128_);
lean_dec_ref(v_headers_1126_);
v___x_1129_ = lean_obj_once(&l_Std_Http_Headers_erase___closed__0, &l_Std_Http_Headers_erase___closed__0_once, _init_l_Std_Http_Headers_erase___closed__0);
v___x_1130_ = lean_unsigned_to_nat(0u);
v___x_1131_ = lean_array_get_size(v_entries_1128_);
v___x_1132_ = ((lean_object*)(l_Std_Http_Headers_getAll___redArg___closed__9));
v___x_1133_ = lean_nat_dec_lt(v___x_1130_, v___x_1131_);
if (v___x_1133_ == 0)
{
lean_dec_ref(v_entries_1128_);
lean_dec_ref(v_names_1127_);
return v___x_1129_;
}
else
{
lean_object* v___f_1134_; lean_object* v___f_1135_; lean_object* v___f_1136_; size_t v___x_1137_; size_t v___x_1138_; lean_object* v___x_1139_; 
v___f_1134_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_1135_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v___f_1136_ = lean_alloc_closure((void*)(l_Std_Http_Headers_eraseMany___lam__1), 5, 3);
lean_closure_set(v___f_1136_, 0, v___f_1134_);
lean_closure_set(v___f_1136_, 1, v_names_1127_);
lean_closure_set(v___f_1136_, 2, v___f_1135_);
v___x_1137_ = ((size_t)0ULL);
v___x_1138_ = lean_usize_of_nat(v___x_1131_);
v___x_1139_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1132_, v___f_1136_, v_entries_1128_, v___x_1137_, v___x_1138_, v___x_1129_);
return v___x_1139_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_size(lean_object* v_headers_1140_){
_start:
{
lean_object* v_entries_1141_; lean_object* v___x_1142_; 
v_entries_1141_ = lean_ctor_get(v_headers_1140_, 0);
v___x_1142_ = lean_array_get_size(v_entries_1141_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_size___boxed(lean_object* v_headers_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_Std_Http_Headers_size(v_headers_1143_);
lean_dec_ref(v_headers_1143_);
return v_res_1144_;
}
}
uint8_t l_Std_Http_Headers_isEmpty(lean_object* v_headers_1145_){
_start:
{
lean_object* v_entries_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; uint8_t v___x_1149_; 
v_entries_1146_ = lean_ctor_get(v_headers_1145_, 0);
v___x_1147_ = lean_array_get_size(v_entries_1146_);
v___x_1148_ = lean_unsigned_to_nat(0u);
v___x_1149_ = lean_nat_dec_eq(v___x_1147_, v___x_1148_);
return v___x_1149_;
}
}
LEAN_EXPORT void l_Std_Http_Headers_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_headers_1145_ = stack[0].m_obj;
uint8_t v_res_1150_;
v_res_1150_ = l_Std_Http_Headers_isEmpty(v_headers_1145_);
stack->m_num = v_res_1150_;
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_isEmpty___boxed(lean_object* v_headers_1151_){
_start:
{
uint8_t v_res_1152_; lean_object* v_r_1153_; 
v_res_1152_ = l_Std_Http_Headers_isEmpty(v_headers_1151_);
lean_dec_ref(v_headers_1151_);
v_r_1153_ = lean_box(v_res_1152_);
return v_r_1153_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___redArg(lean_object* v_as_1154_, size_t v_i_1155_, size_t v_stop_1156_, lean_object* v_b_1157_){
_start:
{
uint8_t v___x_1158_; 
v___x_1158_ = lean_usize_dec_eq(v_i_1155_, v_stop_1156_);
if (v___x_1158_ == 0)
{
lean_object* v___x_1159_; lean_object* v_fst_1160_; lean_object* v_entries_1161_; lean_object* v_indexes_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1175_; 
v___x_1159_ = lean_array_uget_borrowed(v_as_1154_, v_i_1155_);
v_fst_1160_ = lean_ctor_get(v___x_1159_, 0);
v_entries_1161_ = lean_ctor_get(v_b_1157_, 0);
v_indexes_1162_ = lean_ctor_get(v_b_1157_, 1);
v_isSharedCheck_1175_ = !lean_is_exclusive(v_b_1157_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1164_ = v_b_1157_;
v_isShared_1165_ = v_isSharedCheck_1175_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_indexes_1162_);
lean_inc(v_entries_1161_);
lean_dec(v_b_1157_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1175_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v_i_1166_; lean_object* v_entries_1167_; lean_object* v_indexes_1168_; lean_object* v___x_1170_; 
v_i_1166_ = lean_array_get_size(v_entries_1161_);
lean_inc(v___x_1159_);
v_entries_1167_ = lean_array_push(v_entries_1161_, v___x_1159_);
lean_inc(v_fst_1160_);
v_indexes_1168_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0(v_i_1166_, v_indexes_1162_, v_fst_1160_);
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 1, v_indexes_1168_);
lean_ctor_set(v___x_1164_, 0, v_entries_1167_);
v___x_1170_ = v___x_1164_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_entries_1167_);
lean_ctor_set(v_reuseFailAlloc_1174_, 1, v_indexes_1168_);
v___x_1170_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
size_t v___x_1171_; size_t v___x_1172_; 
v___x_1171_ = ((size_t)1ULL);
v___x_1172_ = lean_usize_add(v_i_1155_, v___x_1171_);
v_i_1155_ = v___x_1172_;
v_b_1157_ = v___x_1170_;
goto _start;
}
}
}
else
{
return v_b_1157_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1154_ = stack[0].m_obj;
size_t v_i_1155_ = stack[1].m_num;
size_t v_stop_1156_ = stack[2].m_num;
lean_object* v_b_1157_ = stack[3].m_obj;
lean_object* v_res_1176_;
v_res_1176_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___redArg(v_as_1154_, v_i_1155_, v_stop_1156_, v_b_1157_);
stack->m_obj
 = v_res_1176_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___redArg___boxed(lean_object* v_as_1177_, lean_object* v_i_1178_, lean_object* v_stop_1179_, lean_object* v_b_1180_){
_start:
{
size_t v_i_boxed_1181_; size_t v_stop_boxed_1182_; lean_object* v_res_1183_; 
v_i_boxed_1181_ = lean_unbox_usize(v_i_1178_);
lean_dec(v_i_1178_);
v_stop_boxed_1182_ = lean_unbox_usize(v_stop_1179_);
lean_dec(v_stop_1179_);
v_res_1183_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___redArg(v_as_1177_, v_i_boxed_1181_, v_stop_boxed_1182_, v_b_1180_);
lean_dec_ref(v_as_1177_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0___redArg(lean_object* v_m1_1184_, lean_object* v_m2_1185_){
_start:
{
lean_object* v_entries_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; uint8_t v___x_1189_; 
v_entries_1186_ = lean_ctor_get(v_m2_1185_, 0);
v___x_1187_ = lean_unsigned_to_nat(0u);
v___x_1188_ = lean_array_get_size(v_entries_1186_);
v___x_1189_ = lean_nat_dec_lt(v___x_1187_, v___x_1188_);
if (v___x_1189_ == 0)
{
return v_m1_1184_;
}
else
{
size_t v___x_1190_; size_t v___x_1191_; lean_object* v___x_1192_; 
v___x_1190_ = ((size_t)0ULL);
v___x_1191_ = lean_usize_of_nat(v___x_1188_);
v___x_1192_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___redArg(v_entries_1186_, v___x_1190_, v___x_1191_, v_m1_1184_);
return v___x_1192_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0___redArg___boxed(lean_object* v_m1_1193_, lean_object* v_m2_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0___redArg(v_m1_1193_, v_m2_1194_);
lean_dec_ref(v_m2_1194_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_merge(lean_object* v_headers1_1196_, lean_object* v_headers2_1197_){
_start:
{
lean_object* v___x_1198_; 
v___x_1198_ = l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0___redArg(v_headers1_1196_, v_headers2_1197_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_merge___boxed(lean_object* v_headers1_1199_, lean_object* v_headers2_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l_Std_Http_Headers_merge(v_headers1_1199_, v_headers2_1200_);
lean_dec_ref(v_headers2_1200_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0(lean_object* v_00_u03b2_1202_, lean_object* v_inst_1203_, lean_object* v_inst_1204_, lean_object* v_m1_1205_, lean_object* v_m2_1206_){
_start:
{
lean_object* v___x_1207_; 
v___x_1207_ = l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0___redArg(v_m1_1205_, v_m2_1206_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0___boxed(lean_object* v_00_u03b2_1208_, lean_object* v_inst_1209_, lean_object* v_inst_1210_, lean_object* v_m1_1211_, lean_object* v_m2_1212_){
_start:
{
lean_object* v_res_1213_; 
v_res_1213_ = l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0(v_00_u03b2_1208_, v_inst_1209_, v_inst_1210_, v_m1_1211_, v_m2_1212_);
lean_dec_ref(v_m2_1212_);
return v_res_1213_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0(lean_object* v_00_u03b2_1214_, lean_object* v_as_1215_, size_t v_i_1216_, size_t v_stop_1217_, lean_object* v_b_1218_){
_start:
{
lean_object* v___x_1219_; 
v___x_1219_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___redArg(v_as_1215_, v_i_1216_, v_stop_1217_, v_b_1218_);
return v___x_1219_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1215_ = stack[1].m_obj;
size_t v_i_1216_ = stack[2].m_num;
size_t v_stop_1217_ = stack[3].m_num;
lean_object* v_b_1218_ = stack[4].m_obj;
lean_object* v_res_1220_;
v_res_1220_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0(lean_box(0), v_as_1215_, v_i_1216_, v_stop_1217_, v_b_1218_);
stack->m_obj
 = v_res_1220_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1221_, lean_object* v_as_1222_, lean_object* v_i_1223_, lean_object* v_stop_1224_, lean_object* v_b_1225_){
_start:
{
size_t v_i_boxed_1226_; size_t v_stop_boxed_1227_; lean_object* v_res_1228_; 
v_i_boxed_1226_ = lean_unbox_usize(v_i_1223_);
lean_dec(v_i_1223_);
v_stop_boxed_1227_ = lean_unbox_usize(v_stop_1224_);
lean_dec(v_stop_1224_);
v_res_1228_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0(v_00_u03b2_1221_, v_as_1222_, v_i_boxed_1226_, v_stop_boxed_1227_, v_b_1225_);
lean_dec_ref(v_as_1222_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toList___at___00Std_Http_Headers_toList_spec__0___redArg(lean_object* v_map_1229_){
_start:
{
lean_object* v_entries_1230_; lean_object* v___x_1231_; 
v_entries_1230_ = lean_ctor_get(v_map_1229_, 0);
lean_inc_ref(v_entries_1230_);
lean_dec_ref(v_map_1229_);
v___x_1231_ = lean_array_to_list(v_entries_1230_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toList___at___00Std_Http_Headers_toList_spec__0(lean_object* v_00_u03b2_1232_, lean_object* v_map_1233_){
_start:
{
lean_object* v___x_1234_; 
v___x_1234_ = l_Std_Internal_IndexMultiMap_toList___at___00Std_Http_Headers_toList_spec__0___redArg(v_map_1233_);
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_toList(lean_object* v_headers_1235_){
_start:
{
lean_object* v___x_1236_; 
v___x_1236_ = l_Std_Internal_IndexMultiMap_toList___at___00Std_Http_Headers_toList_spec__0___redArg(v_headers_1235_);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_toArray(lean_object* v_headers_1237_){
_start:
{
lean_object* v_entries_1238_; 
v_entries_1238_ = lean_ctor_get(v_headers_1237_, 0);
lean_inc_ref(v_entries_1238_);
return v_entries_1238_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_toArray___boxed(lean_object* v_headers_1239_){
_start:
{
lean_object* v_res_1240_; 
v_res_1240_ = l_Std_Http_Headers_toArray(v_headers_1239_);
lean_dec_ref(v_headers_1239_);
return v_res_1240_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___redArg(lean_object* v_f_1241_, lean_object* v_as_1242_, size_t v_i_1243_, size_t v_stop_1244_, lean_object* v_b_1245_){
_start:
{
uint8_t v___x_1246_; 
v___x_1246_ = lean_usize_dec_eq(v_i_1243_, v_stop_1244_);
if (v___x_1246_ == 0)
{
lean_object* v___x_1247_; lean_object* v_fst_1248_; lean_object* v_snd_1249_; lean_object* v___x_1250_; size_t v___x_1251_; size_t v___x_1252_; 
v___x_1247_ = lean_array_uget_borrowed(v_as_1242_, v_i_1243_);
v_fst_1248_ = lean_ctor_get(v___x_1247_, 0);
v_snd_1249_ = lean_ctor_get(v___x_1247_, 1);
lean_inc(v_f_1241_);
lean_inc(v_snd_1249_);
lean_inc(v_fst_1248_);
v___x_1250_ = lean_apply_3(v_f_1241_, v_b_1245_, v_fst_1248_, v_snd_1249_);
v___x_1251_ = ((size_t)1ULL);
v___x_1252_ = lean_usize_add(v_i_1243_, v___x_1251_);
v_i_1243_ = v___x_1252_;
v_b_1245_ = v___x_1250_;
goto _start;
}
else
{
lean_dec(v_f_1241_);
return v_b_1245_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1241_ = stack[0].m_obj;
lean_object* v_as_1242_ = stack[1].m_obj;
size_t v_i_1243_ = stack[2].m_num;
size_t v_stop_1244_ = stack[3].m_num;
lean_object* v_b_1245_ = stack[4].m_obj;
lean_object* v_res_1254_;
v_res_1254_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___redArg(v_f_1241_, v_as_1242_, v_i_1243_, v_stop_1244_, v_b_1245_);
stack->m_obj
 = v_res_1254_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___redArg___boxed(lean_object* v_f_1255_, lean_object* v_as_1256_, lean_object* v_i_1257_, lean_object* v_stop_1258_, lean_object* v_b_1259_){
_start:
{
size_t v_i_boxed_1260_; size_t v_stop_boxed_1261_; lean_object* v_res_1262_; 
v_i_boxed_1260_ = lean_unbox_usize(v_i_1257_);
lean_dec(v_i_1257_);
v_stop_boxed_1261_ = lean_unbox_usize(v_stop_1258_);
lean_dec(v_stop_1258_);
v_res_1262_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___redArg(v_f_1255_, v_as_1256_, v_i_boxed_1260_, v_stop_boxed_1261_, v_b_1259_);
lean_dec_ref(v_as_1256_);
return v_res_1262_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_fold___redArg(lean_object* v_headers_1263_, lean_object* v_init_1264_, lean_object* v_f_1265_){
_start:
{
lean_object* v_entries_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; uint8_t v___x_1269_; 
v_entries_1266_ = lean_ctor_get(v_headers_1263_, 0);
v___x_1267_ = lean_unsigned_to_nat(0u);
v___x_1268_ = lean_array_get_size(v_entries_1266_);
v___x_1269_ = lean_nat_dec_lt(v___x_1267_, v___x_1268_);
if (v___x_1269_ == 0)
{
lean_dec(v_f_1265_);
return v_init_1264_;
}
else
{
uint8_t v___x_1270_; 
v___x_1270_ = lean_nat_dec_le(v___x_1268_, v___x_1268_);
if (v___x_1270_ == 0)
{
if (v___x_1269_ == 0)
{
lean_dec(v_f_1265_);
return v_init_1264_;
}
else
{
size_t v___x_1271_; size_t v___x_1272_; lean_object* v___x_1273_; 
v___x_1271_ = ((size_t)0ULL);
v___x_1272_ = lean_usize_of_nat(v___x_1268_);
v___x_1273_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___redArg(v_f_1265_, v_entries_1266_, v___x_1271_, v___x_1272_, v_init_1264_);
return v___x_1273_;
}
}
else
{
size_t v___x_1274_; size_t v___x_1275_; lean_object* v___x_1276_; 
v___x_1274_ = ((size_t)0ULL);
v___x_1275_ = lean_usize_of_nat(v___x_1268_);
v___x_1276_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___redArg(v_f_1265_, v_entries_1266_, v___x_1274_, v___x_1275_, v_init_1264_);
return v___x_1276_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_fold___redArg___boxed(lean_object* v_headers_1277_, lean_object* v_init_1278_, lean_object* v_f_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l_Std_Http_Headers_fold___redArg(v_headers_1277_, v_init_1278_, v_f_1279_);
lean_dec_ref(v_headers_1277_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_fold(lean_object* v_00_u03b1_1281_, lean_object* v_headers_1282_, lean_object* v_init_1283_, lean_object* v_f_1284_){
_start:
{
lean_object* v___x_1285_; 
v___x_1285_ = l_Std_Http_Headers_fold___redArg(v_headers_1282_, v_init_1283_, v_f_1284_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_fold___boxed(lean_object* v_00_u03b1_1286_, lean_object* v_headers_1287_, lean_object* v_init_1288_, lean_object* v_f_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l_Std_Http_Headers_fold(v_00_u03b1_1286_, v_headers_1287_, v_init_1288_, v_f_1289_);
lean_dec_ref(v_headers_1287_);
return v_res_1290_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0(lean_object* v_00_u03b1_1291_, lean_object* v_f_1292_, lean_object* v_as_1293_, size_t v_i_1294_, size_t v_stop_1295_, lean_object* v_b_1296_){
_start:
{
lean_object* v___x_1297_; 
v___x_1297_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___redArg(v_f_1292_, v_as_1293_, v_i_1294_, v_stop_1295_, v_b_1296_);
return v___x_1297_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1292_ = stack[1].m_obj;
lean_object* v_as_1293_ = stack[2].m_obj;
size_t v_i_1294_ = stack[3].m_num;
size_t v_stop_1295_ = stack[4].m_num;
lean_object* v_b_1296_ = stack[5].m_obj;
lean_object* v_res_1298_;
v_res_1298_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0(lean_box(0), v_f_1292_, v_as_1293_, v_i_1294_, v_stop_1295_, v_b_1296_);
stack->m_obj
 = v_res_1298_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___boxed(lean_object* v_00_u03b1_1299_, lean_object* v_f_1300_, lean_object* v_as_1301_, lean_object* v_i_1302_, lean_object* v_stop_1303_, lean_object* v_b_1304_){
_start:
{
size_t v_i_boxed_1305_; size_t v_stop_boxed_1306_; lean_object* v_res_1307_; 
v_i_boxed_1305_ = lean_unbox_usize(v_i_1302_);
lean_dec(v_i_1302_);
v_stop_boxed_1306_ = lean_unbox_usize(v_stop_1303_);
lean_dec(v_stop_1303_);
v_res_1307_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0(v_00_u03b1_1299_, v_f_1300_, v_as_1301_, v_i_boxed_1305_, v_stop_boxed_1306_, v_b_1304_);
lean_dec_ref(v_as_1301_);
return v_res_1307_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Headers_mapValues_spec__0(lean_object* v_f_1308_, size_t v_sz_1309_, size_t v_i_1310_, lean_object* v_bs_1311_){
_start:
{
uint8_t v___x_1312_; 
v___x_1312_ = lean_usize_dec_lt(v_i_1310_, v_sz_1309_);
if (v___x_1312_ == 0)
{
lean_dec_ref(v_f_1308_);
return v_bs_1311_;
}
else
{
lean_object* v_v_1313_; lean_object* v_fst_1314_; lean_object* v_snd_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1329_; 
v_v_1313_ = lean_array_uget(v_bs_1311_, v_i_1310_);
v_fst_1314_ = lean_ctor_get(v_v_1313_, 0);
v_snd_1315_ = lean_ctor_get(v_v_1313_, 1);
v_isSharedCheck_1329_ = !lean_is_exclusive(v_v_1313_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1317_ = v_v_1313_;
v_isShared_1318_ = v_isSharedCheck_1329_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_snd_1315_);
lean_inc(v_fst_1314_);
lean_dec(v_v_1313_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1329_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1319_; lean_object* v_bs_x27_1320_; lean_object* v___x_1321_; lean_object* v___x_1323_; 
v___x_1319_ = lean_unsigned_to_nat(0u);
v_bs_x27_1320_ = lean_array_uset(v_bs_1311_, v_i_1310_, v___x_1319_);
lean_inc_ref(v_f_1308_);
lean_inc(v_fst_1314_);
v___x_1321_ = lean_apply_2(v_f_1308_, v_fst_1314_, v_snd_1315_);
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 1, v___x_1321_);
v___x_1323_ = v___x_1317_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_fst_1314_);
lean_ctor_set(v_reuseFailAlloc_1328_, 1, v___x_1321_);
v___x_1323_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
size_t v___x_1324_; size_t v___x_1325_; lean_object* v___x_1326_; 
v___x_1324_ = ((size_t)1ULL);
v___x_1325_ = lean_usize_add(v_i_1310_, v___x_1324_);
v___x_1326_ = lean_array_uset(v_bs_x27_1320_, v_i_1310_, v___x_1323_);
v_i_1310_ = v___x_1325_;
v_bs_1311_ = v___x_1326_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Headers_mapValues_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1308_ = stack[0].m_obj;
size_t v_sz_1309_ = stack[1].m_num;
size_t v_i_1310_ = stack[2].m_num;
lean_object* v_bs_1311_ = stack[3].m_obj;
lean_object* v_res_1330_;
v_res_1330_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Headers_mapValues_spec__0(v_f_1308_, v_sz_1309_, v_i_1310_, v_bs_1311_);
stack->m_obj
 = v_res_1330_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Headers_mapValues_spec__0___boxed(lean_object* v_f_1331_, lean_object* v_sz_1332_, lean_object* v_i_1333_, lean_object* v_bs_1334_){
_start:
{
size_t v_sz_boxed_1335_; size_t v_i_boxed_1336_; lean_object* v_res_1337_; 
v_sz_boxed_1335_ = lean_unbox_usize(v_sz_1332_);
lean_dec(v_sz_1332_);
v_i_boxed_1336_ = lean_unbox_usize(v_i_1333_);
lean_dec(v_i_1333_);
v_res_1337_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Headers_mapValues_spec__0(v_f_1331_, v_sz_boxed_1335_, v_i_boxed_1336_, v_bs_1334_);
return v_res_1337_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_mapValues_spec__1(lean_object* v_as_1338_, size_t v_i_1339_, size_t v_stop_1340_, lean_object* v_b_1341_){
_start:
{
uint8_t v___x_1342_; 
v___x_1342_ = lean_usize_dec_eq(v_i_1339_, v_stop_1340_);
if (v___x_1342_ == 0)
{
lean_object* v___x_1343_; lean_object* v_fst_1344_; lean_object* v_entries_1345_; lean_object* v_indexes_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1359_; 
v___x_1343_ = lean_array_uget_borrowed(v_as_1338_, v_i_1339_);
v_fst_1344_ = lean_ctor_get(v___x_1343_, 0);
v_entries_1345_ = lean_ctor_get(v_b_1341_, 0);
v_indexes_1346_ = lean_ctor_get(v_b_1341_, 1);
v_isSharedCheck_1359_ = !lean_is_exclusive(v_b_1341_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1348_ = v_b_1341_;
v_isShared_1349_ = v_isSharedCheck_1359_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_indexes_1346_);
lean_inc(v_entries_1345_);
lean_dec(v_b_1341_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1359_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v_i_1350_; lean_object* v_entries_1351_; lean_object* v_indexes_1352_; lean_object* v___x_1354_; 
v_i_1350_ = lean_array_get_size(v_entries_1345_);
lean_inc(v___x_1343_);
v_entries_1351_ = lean_array_push(v_entries_1345_, v___x_1343_);
lean_inc(v_fst_1344_);
v_indexes_1352_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0(v_i_1350_, v_indexes_1346_, v_fst_1344_);
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 1, v_indexes_1352_);
lean_ctor_set(v___x_1348_, 0, v_entries_1351_);
v___x_1354_ = v___x_1348_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_entries_1351_);
lean_ctor_set(v_reuseFailAlloc_1358_, 1, v_indexes_1352_);
v___x_1354_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
size_t v___x_1355_; size_t v___x_1356_; 
v___x_1355_ = ((size_t)1ULL);
v___x_1356_ = lean_usize_add(v_i_1339_, v___x_1355_);
v_i_1339_ = v___x_1356_;
v_b_1341_ = v___x_1354_;
goto _start;
}
}
}
else
{
return v_b_1341_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_mapValues_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1338_ = stack[0].m_obj;
size_t v_i_1339_ = stack[1].m_num;
size_t v_stop_1340_ = stack[2].m_num;
lean_object* v_b_1341_ = stack[3].m_obj;
lean_object* v_res_1360_;
v_res_1360_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_mapValues_spec__1(v_as_1338_, v_i_1339_, v_stop_1340_, v_b_1341_);
stack->m_obj
 = v_res_1360_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_mapValues_spec__1___boxed(lean_object* v_as_1361_, lean_object* v_i_1362_, lean_object* v_stop_1363_, lean_object* v_b_1364_){
_start:
{
size_t v_i_boxed_1365_; size_t v_stop_boxed_1366_; lean_object* v_res_1367_; 
v_i_boxed_1365_ = lean_unbox_usize(v_i_1362_);
lean_dec(v_i_1362_);
v_stop_boxed_1366_ = lean_unbox_usize(v_stop_1363_);
lean_dec(v_stop_1363_);
v_res_1367_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_mapValues_spec__1(v_as_1361_, v_i_boxed_1365_, v_stop_boxed_1366_, v_b_1364_);
lean_dec_ref(v_as_1361_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_mapValues(lean_object* v_headers_1368_, lean_object* v_f_1369_){
_start:
{
lean_object* v_entries_1370_; size_t v_sz_1371_; size_t v___x_1372_; lean_object* v_pairs_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; uint8_t v___x_1377_; 
v_entries_1370_ = lean_ctor_get(v_headers_1368_, 0);
lean_inc_ref(v_entries_1370_);
lean_dec_ref(v_headers_1368_);
v_sz_1371_ = lean_array_size(v_entries_1370_);
v___x_1372_ = ((size_t)0ULL);
v_pairs_1373_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Headers_mapValues_spec__0(v_f_1369_, v_sz_1371_, v___x_1372_, v_entries_1370_);
v___x_1374_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__0, &l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__0_once, _init_l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__0);
v___x_1375_ = lean_unsigned_to_nat(0u);
v___x_1376_ = lean_array_get_size(v_pairs_1373_);
v___x_1377_ = lean_nat_dec_lt(v___x_1375_, v___x_1376_);
if (v___x_1377_ == 0)
{
lean_dec_ref(v_pairs_1373_);
return v___x_1374_;
}
else
{
uint8_t v___x_1378_; 
v___x_1378_ = lean_nat_dec_le(v___x_1376_, v___x_1376_);
if (v___x_1378_ == 0)
{
if (v___x_1377_ == 0)
{
lean_dec_ref(v_pairs_1373_);
return v___x_1374_;
}
else
{
size_t v___x_1379_; lean_object* v___x_1380_; 
v___x_1379_ = lean_usize_of_nat(v___x_1376_);
v___x_1380_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_mapValues_spec__1(v_pairs_1373_, v___x_1372_, v___x_1379_, v___x_1374_);
lean_dec_ref(v_pairs_1373_);
return v___x_1380_;
}
}
else
{
size_t v___x_1381_; lean_object* v___x_1382_; 
v___x_1381_ = lean_usize_of_nat(v___x_1376_);
v___x_1382_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_mapValues_spec__1(v_pairs_1373_, v___x_1372_, v___x_1381_, v___x_1374_);
lean_dec_ref(v_pairs_1373_);
return v___x_1382_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0_spec__0(lean_object* v_f_1383_, lean_object* v_as_1384_, size_t v_i_1385_, size_t v_stop_1386_, lean_object* v_b_1387_){
_start:
{
lean_object* v___y_1389_; uint8_t v___x_1393_; 
v___x_1393_ = lean_usize_dec_eq(v_i_1385_, v_stop_1386_);
if (v___x_1393_ == 0)
{
lean_object* v___x_1394_; lean_object* v_fst_1395_; lean_object* v_snd_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1406_; 
v___x_1394_ = lean_array_uget(v_as_1384_, v_i_1385_);
v_fst_1395_ = lean_ctor_get(v___x_1394_, 0);
v_snd_1396_ = lean_ctor_get(v___x_1394_, 1);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1398_ = v___x_1394_;
v_isShared_1399_ = v_isSharedCheck_1406_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_snd_1396_);
lean_inc(v_fst_1395_);
lean_dec(v___x_1394_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1406_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1400_; 
lean_inc_ref(v_f_1383_);
lean_inc(v_fst_1395_);
v___x_1400_ = lean_apply_2(v_f_1383_, v_fst_1395_, v_snd_1396_);
if (lean_obj_tag(v___x_1400_) == 0)
{
lean_del_object(v___x_1398_);
lean_dec(v_fst_1395_);
v___y_1389_ = v_b_1387_;
goto v___jp_1388_;
}
else
{
lean_object* v_val_1401_; lean_object* v___x_1403_; 
v_val_1401_ = lean_ctor_get(v___x_1400_, 0);
lean_inc(v_val_1401_);
lean_dec_ref_known(v___x_1400_, 1);
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 1, v_val_1401_);
v___x_1403_ = v___x_1398_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_fst_1395_);
lean_ctor_set(v_reuseFailAlloc_1405_, 1, v_val_1401_);
v___x_1403_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
lean_object* v___x_1404_; 
v___x_1404_ = lean_array_push(v_b_1387_, v___x_1403_);
v___y_1389_ = v___x_1404_;
goto v___jp_1388_;
}
}
}
}
else
{
lean_dec_ref(v_f_1383_);
return v_b_1387_;
}
v___jp_1388_:
{
size_t v___x_1390_; size_t v___x_1391_; 
v___x_1390_ = ((size_t)1ULL);
v___x_1391_ = lean_usize_add(v_i_1385_, v___x_1390_);
v_i_1385_ = v___x_1391_;
v_b_1387_ = v___y_1389_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1383_ = stack[0].m_obj;
lean_object* v_as_1384_ = stack[1].m_obj;
size_t v_i_1385_ = stack[2].m_num;
size_t v_stop_1386_ = stack[3].m_num;
lean_object* v_b_1387_ = stack[4].m_obj;
lean_object* v_res_1407_;
v_res_1407_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0_spec__0(v_f_1383_, v_as_1384_, v_i_1385_, v_stop_1386_, v_b_1387_);
stack->m_obj
 = v_res_1407_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0_spec__0___boxed(lean_object* v_f_1408_, lean_object* v_as_1409_, lean_object* v_i_1410_, lean_object* v_stop_1411_, lean_object* v_b_1412_){
_start:
{
size_t v_i_boxed_1413_; size_t v_stop_boxed_1414_; lean_object* v_res_1415_; 
v_i_boxed_1413_ = lean_unbox_usize(v_i_1410_);
lean_dec(v_i_1410_);
v_stop_boxed_1414_ = lean_unbox_usize(v_stop_1411_);
lean_dec(v_stop_1411_);
v_res_1415_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0_spec__0(v_f_1408_, v_as_1409_, v_i_boxed_1413_, v_stop_boxed_1414_, v_b_1412_);
lean_dec_ref(v_as_1409_);
return v_res_1415_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0(lean_object* v_f_1416_, lean_object* v_as_1417_, lean_object* v_start_1418_, lean_object* v_stop_1419_){
_start:
{
lean_object* v___x_1420_; uint8_t v___x_1421_; 
v___x_1420_ = ((lean_object*)(l_Std_Http_instInhabitedHeaders_default___closed__0));
v___x_1421_ = lean_nat_dec_lt(v_start_1418_, v_stop_1419_);
if (v___x_1421_ == 0)
{
lean_dec_ref(v_f_1416_);
return v___x_1420_;
}
else
{
lean_object* v___x_1422_; uint8_t v___x_1423_; 
v___x_1422_ = lean_array_get_size(v_as_1417_);
v___x_1423_ = lean_nat_dec_le(v_stop_1419_, v___x_1422_);
if (v___x_1423_ == 0)
{
uint8_t v___x_1424_; 
v___x_1424_ = lean_nat_dec_lt(v_start_1418_, v___x_1422_);
if (v___x_1424_ == 0)
{
lean_dec_ref(v_f_1416_);
return v___x_1420_;
}
else
{
size_t v___x_1425_; size_t v___x_1426_; lean_object* v___x_1427_; 
v___x_1425_ = lean_usize_of_nat(v_start_1418_);
v___x_1426_ = lean_usize_of_nat(v___x_1422_);
v___x_1427_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0_spec__0(v_f_1416_, v_as_1417_, v___x_1425_, v___x_1426_, v___x_1420_);
return v___x_1427_;
}
}
else
{
size_t v___x_1428_; size_t v___x_1429_; lean_object* v___x_1430_; 
v___x_1428_ = lean_usize_of_nat(v_start_1418_);
v___x_1429_ = lean_usize_of_nat(v_stop_1419_);
v___x_1430_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0_spec__0(v_f_1416_, v_as_1417_, v___x_1428_, v___x_1429_, v___x_1420_);
return v___x_1430_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0___boxed(lean_object* v_f_1431_, lean_object* v_as_1432_, lean_object* v_start_1433_, lean_object* v_stop_1434_){
_start:
{
lean_object* v_res_1435_; 
v_res_1435_ = l_Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0(v_f_1431_, v_as_1432_, v_start_1433_, v_stop_1434_);
lean_dec(v_stop_1434_);
lean_dec(v_start_1433_);
lean_dec_ref(v_as_1432_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_filterMap(lean_object* v_headers_1436_, lean_object* v_f_1437_){
_start:
{
lean_object* v_entries_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v_pairs_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; uint8_t v___x_1444_; 
v_entries_1438_ = lean_ctor_get(v_headers_1436_, 0);
v___x_1439_ = lean_unsigned_to_nat(0u);
v___x_1440_ = lean_array_get_size(v_entries_1438_);
v_pairs_1441_ = l_Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0(v_f_1437_, v_entries_1438_, v___x_1439_, v___x_1440_);
v___x_1442_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__0, &l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__0_once, _init_l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__0);
v___x_1443_ = lean_array_get_size(v_pairs_1441_);
v___x_1444_ = lean_nat_dec_lt(v___x_1439_, v___x_1443_);
if (v___x_1444_ == 0)
{
lean_dec_ref(v_pairs_1441_);
return v___x_1442_;
}
else
{
uint8_t v___x_1445_; 
v___x_1445_ = lean_nat_dec_le(v___x_1443_, v___x_1443_);
if (v___x_1445_ == 0)
{
if (v___x_1444_ == 0)
{
lean_dec_ref(v_pairs_1441_);
return v___x_1442_;
}
else
{
size_t v___x_1446_; size_t v___x_1447_; lean_object* v___x_1448_; 
v___x_1446_ = ((size_t)0ULL);
v___x_1447_ = lean_usize_of_nat(v___x_1443_);
v___x_1448_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_mapValues_spec__1(v_pairs_1441_, v___x_1446_, v___x_1447_, v___x_1442_);
lean_dec_ref(v_pairs_1441_);
return v___x_1448_;
}
}
else
{
size_t v___x_1449_; size_t v___x_1450_; lean_object* v___x_1451_; 
v___x_1449_ = ((size_t)0ULL);
v___x_1450_ = lean_usize_of_nat(v___x_1443_);
v___x_1451_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_mapValues_spec__1(v_pairs_1441_, v___x_1449_, v___x_1450_, v___x_1442_);
lean_dec_ref(v_pairs_1441_);
return v___x_1451_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_filterMap___boxed(lean_object* v_headers_1452_, lean_object* v_f_1453_){
_start:
{
lean_object* v_res_1454_; 
v_res_1454_ = l_Std_Http_Headers_filterMap(v_headers_1452_, v_f_1453_);
lean_dec_ref(v_headers_1452_);
return v_res_1454_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_filter___lam__0(lean_object* v_f_1455_, lean_object* v_k_1456_, lean_object* v_v_1457_){
_start:
{
lean_object* v___x_1458_; uint8_t v___x_1459_; 
lean_inc_ref(v_v_1457_);
v___x_1458_ = lean_apply_2(v_f_1455_, v_k_1456_, v_v_1457_);
v___x_1459_ = lean_unbox(v___x_1458_);
if (v___x_1459_ == 0)
{
lean_object* v___x_1460_; 
lean_dec_ref(v_v_1457_);
v___x_1460_ = lean_box(0);
return v___x_1460_;
}
else
{
lean_object* v___x_1461_; 
v___x_1461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1461_, 0, v_v_1457_);
return v___x_1461_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_filter(lean_object* v_headers_1462_, lean_object* v_f_1463_){
_start:
{
lean_object* v___f_1464_; lean_object* v___x_1465_; 
v___f_1464_ = lean_alloc_closure((void*)(l_Std_Http_Headers_filter___lam__0), 3, 1);
lean_closure_set(v___f_1464_, 0, v_f_1463_);
v___x_1465_ = l_Std_Http_Headers_filterMap(v_headers_1462_, v___f_1464_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_filter___boxed(lean_object* v_headers_1466_, lean_object* v_f_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l_Std_Http_Headers_filter(v_headers_1466_, v_f_1467_);
lean_dec_ref(v_headers_1466_);
return v_res_1468_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_update_spec__0(lean_object* v_name_1469_, lean_object* v_f_1470_, lean_object* v_as_1471_, size_t v_i_1472_, size_t v_stop_1473_, lean_object* v_b_1474_){
_start:
{
uint8_t v___x_1475_; 
v___x_1475_ = lean_usize_dec_eq(v_i_1472_, v_stop_1473_);
if (v___x_1475_ == 0)
{
lean_object* v___x_1476_; lean_object* v_fst_1477_; lean_object* v_snd_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1504_; 
v___x_1476_ = lean_array_uget(v_as_1471_, v_i_1472_);
v_fst_1477_ = lean_ctor_get(v___x_1476_, 0);
v_snd_1478_ = lean_ctor_get(v___x_1476_, 1);
v_isSharedCheck_1504_ = !lean_is_exclusive(v___x_1476_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1480_ = v___x_1476_;
v_isShared_1481_ = v_isSharedCheck_1504_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_snd_1478_);
lean_inc(v_fst_1477_);
lean_dec(v___x_1476_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1504_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___y_1483_; uint8_t v___x_1502_; 
v___x_1502_ = lean_string_dec_eq(v_fst_1477_, v_name_1469_);
if (v___x_1502_ == 0)
{
v___y_1483_ = v_snd_1478_;
goto v___jp_1482_;
}
else
{
lean_object* v___x_1503_; 
lean_inc_ref(v_f_1470_);
v___x_1503_ = lean_apply_1(v_f_1470_, v_snd_1478_);
v___y_1483_ = v___x_1503_;
goto v___jp_1482_;
}
v___jp_1482_:
{
lean_object* v_entries_1484_; lean_object* v_indexes_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1501_; 
v_entries_1484_ = lean_ctor_get(v_b_1474_, 0);
v_indexes_1485_ = lean_ctor_get(v_b_1474_, 1);
v_isSharedCheck_1501_ = !lean_is_exclusive(v_b_1474_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1487_ = v_b_1474_;
v_isShared_1488_ = v_isSharedCheck_1501_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_indexes_1485_);
lean_inc(v_entries_1484_);
lean_dec(v_b_1474_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1501_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v_i_1489_; lean_object* v___x_1491_; 
v_i_1489_ = lean_array_get_size(v_entries_1484_);
lean_inc(v_fst_1477_);
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 1, v___y_1483_);
v___x_1491_ = v___x_1480_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_fst_1477_);
lean_ctor_set(v_reuseFailAlloc_1500_, 1, v___y_1483_);
v___x_1491_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
lean_object* v_entries_1492_; lean_object* v_indexes_1493_; lean_object* v___x_1495_; 
v_entries_1492_ = lean_array_push(v_entries_1484_, v___x_1491_);
v_indexes_1493_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0(v_i_1489_, v_indexes_1485_, v_fst_1477_);
if (v_isShared_1488_ == 0)
{
lean_ctor_set(v___x_1487_, 1, v_indexes_1493_);
lean_ctor_set(v___x_1487_, 0, v_entries_1492_);
v___x_1495_ = v___x_1487_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v_entries_1492_);
lean_ctor_set(v_reuseFailAlloc_1499_, 1, v_indexes_1493_);
v___x_1495_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
size_t v___x_1496_; size_t v___x_1497_; 
v___x_1496_ = ((size_t)1ULL);
v___x_1497_ = lean_usize_add(v_i_1472_, v___x_1496_);
v_i_1472_ = v___x_1497_;
v_b_1474_ = v___x_1495_;
goto _start;
}
}
}
}
}
}
else
{
lean_dec_ref(v_f_1470_);
return v_b_1474_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_update_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1469_ = stack[0].m_obj;
lean_object* v_f_1470_ = stack[1].m_obj;
lean_object* v_as_1471_ = stack[2].m_obj;
size_t v_i_1472_ = stack[3].m_num;
size_t v_stop_1473_ = stack[4].m_num;
lean_object* v_b_1474_ = stack[5].m_obj;
lean_object* v_res_1505_;
v_res_1505_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_update_spec__0(v_name_1469_, v_f_1470_, v_as_1471_, v_i_1472_, v_stop_1473_, v_b_1474_);
stack->m_obj
 = v_res_1505_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_update_spec__0___boxed(lean_object* v_name_1506_, lean_object* v_f_1507_, lean_object* v_as_1508_, lean_object* v_i_1509_, lean_object* v_stop_1510_, lean_object* v_b_1511_){
_start:
{
size_t v_i_boxed_1512_; size_t v_stop_boxed_1513_; lean_object* v_res_1514_; 
v_i_boxed_1512_ = lean_unbox_usize(v_i_1509_);
lean_dec(v_i_1509_);
v_stop_boxed_1513_ = lean_unbox_usize(v_stop_1510_);
lean_dec(v_stop_1510_);
v_res_1514_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_update_spec__0(v_name_1506_, v_f_1507_, v_as_1508_, v_i_boxed_1512_, v_stop_boxed_1513_, v_b_1511_);
lean_dec_ref(v_as_1508_);
lean_dec_ref(v_name_1506_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_update(lean_object* v_headers_1515_, lean_object* v_name_1516_, lean_object* v_f_1517_){
_start:
{
lean_object* v___f_1518_; lean_object* v___f_1519_; uint8_t v___x_1520_; 
v___f_1518_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_1519_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
lean_inc_ref(v_name_1516_);
v___x_1520_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_1518_, v___f_1519_, v_name_1516_, v_headers_1515_);
if (v___x_1520_ == 0)
{
lean_dec_ref(v_f_1517_);
lean_dec_ref(v_name_1516_);
lean_inc_ref(v_headers_1515_);
return v_headers_1515_;
}
else
{
lean_object* v_entries_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; uint8_t v___x_1525_; 
v_entries_1521_ = lean_ctor_get(v_headers_1515_, 0);
v___x_1522_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__0, &l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__0_once, _init_l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__0);
v___x_1523_ = lean_unsigned_to_nat(0u);
v___x_1524_ = lean_array_get_size(v_entries_1521_);
v___x_1525_ = lean_nat_dec_lt(v___x_1523_, v___x_1524_);
if (v___x_1525_ == 0)
{
lean_dec_ref(v_f_1517_);
lean_dec_ref(v_name_1516_);
return v___x_1522_;
}
else
{
size_t v___x_1526_; size_t v___x_1527_; lean_object* v___x_1528_; 
v___x_1526_ = ((size_t)0ULL);
v___x_1527_ = lean_usize_of_nat(v___x_1524_);
v___x_1528_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_update_spec__0(v_name_1516_, v_f_1517_, v_entries_1521_, v___x_1526_, v___x_1527_, v___x_1522_);
lean_dec_ref(v_name_1516_);
return v___x_1528_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_update___boxed(lean_object* v_headers_1529_, lean_object* v_name_1530_, lean_object* v_f_1531_){
_start:
{
lean_object* v_res_1532_; 
v_res_1532_ = l_Std_Http_Headers_update(v_headers_1529_, v_name_1530_, v_f_1531_);
lean_dec_ref(v_headers_1529_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_replaceLast(lean_object* v_headers_1533_, lean_object* v_name_1534_, lean_object* v_value_1535_){
_start:
{
lean_object* v_entries_1536_; lean_object* v_indexes_1537_; lean_object* v___f_1538_; lean_object* v___f_1539_; uint8_t v___x_1540_; 
v_entries_1536_ = lean_ctor_get(v_headers_1533_, 0);
v_indexes_1537_ = lean_ctor_get(v_headers_1533_, 1);
v___f_1538_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_1539_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
lean_inc_ref(v_name_1534_);
v___x_1540_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_1538_, v___f_1539_, v_indexes_1537_, v_name_1534_);
if (v___x_1540_ == 0)
{
lean_dec_ref(v_value_1535_);
lean_dec_ref(v_name_1534_);
return v_headers_1533_;
}
else
{
lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1554_; 
lean_inc_ref(v_indexes_1537_);
lean_inc_ref(v_entries_1536_);
v_isSharedCheck_1554_ = !lean_is_exclusive(v_headers_1533_);
if (v_isSharedCheck_1554_ == 0)
{
lean_object* v_unused_1555_; lean_object* v_unused_1556_; 
v_unused_1555_ = lean_ctor_get(v_headers_1533_, 1);
lean_dec(v_unused_1555_);
v_unused_1556_ = lean_ctor_get(v_headers_1533_, 0);
lean_dec(v_unused_1556_);
v___x_1542_ = v_headers_1533_;
v_isShared_1543_ = v_isSharedCheck_1554_;
goto v_resetjp_1541_;
}
else
{
lean_dec(v_headers_1533_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1554_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v_idxs_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v_lastIdx_1548_; lean_object* v___x_1549_; lean_object* v_entries_1550_; lean_object* v___x_1552_; 
lean_inc_ref(v_name_1534_);
v_idxs_1544_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v___f_1538_, v___f_1539_, v_indexes_1537_, v_name_1534_);
v___x_1545_ = lean_array_get_size(v_idxs_1544_);
v___x_1546_ = lean_unsigned_to_nat(1u);
v___x_1547_ = lean_nat_sub(v___x_1545_, v___x_1546_);
v_lastIdx_1548_ = lean_array_fget(v_idxs_1544_, v___x_1547_);
lean_dec(v___x_1547_);
lean_dec(v_idxs_1544_);
v___x_1549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1549_, 0, v_name_1534_);
lean_ctor_set(v___x_1549_, 1, v_value_1535_);
v_entries_1550_ = lean_array_fset(v_entries_1536_, v_lastIdx_1548_, v___x_1549_);
lean_dec(v_lastIdx_1548_);
if (v_isShared_1543_ == 0)
{
lean_ctor_set(v___x_1542_, 0, v_entries_1550_);
v___x_1552_ = v___x_1542_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_entries_1550_);
lean_ctor_set(v_reuseFailAlloc_1553_, 1, v_indexes_1537_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
}
}
lean_object* l_Std_Http_Headers_instToString___lam__0(lean_object* v___x_1557_, lean_object* v___x_1558_, lean_object* v___x_1559_, lean_object* v_fst_1560_, lean_object* v___x_1561_, uint32_t v___x_1562_, lean_object* v___x_1563_, lean_object* v_it_1564_, lean_object* v_acc_1565_, lean_object* v_hP_1566_, lean_object* v_recur_1567_){
_start:
{
lean_object* v_it_1569_; lean_object* v_out_1570_; lean_object* v_it_1586_; lean_object* v_startInclusive_1587_; lean_object* v_endExclusive_1588_; 
if (lean_obj_tag(v_it_1564_) == 0)
{
lean_object* v_currPos_1600_; lean_object* v_searcher_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1623_; 
v_currPos_1600_ = lean_ctor_get(v_it_1564_, 0);
v_searcher_1601_ = lean_ctor_get(v_it_1564_, 1);
v_isSharedCheck_1623_ = !lean_is_exclusive(v_it_1564_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1603_ = v_it_1564_;
v_isShared_1604_ = v_isSharedCheck_1623_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_searcher_1601_);
lean_inc(v_currPos_1600_);
lean_dec(v_it_1564_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1623_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
uint8_t v_decide_1605_; 
v_decide_1605_ = lean_nat_dec_eq(v_searcher_1601_, v___x_1561_);
if (v_decide_1605_ == 0)
{
uint32_t v___x_1606_; uint8_t v___x_1607_; 
lean_dec(v___x_1561_);
v___x_1606_ = lean_string_utf8_get_fast(v_fst_1560_, v_searcher_1601_);
v___x_1607_ = lean_uint32_dec_eq(v___x_1606_, v___x_1562_);
if (v___x_1607_ == 0)
{
lean_object* v___x_1608_; lean_object* v___x_1610_; 
v___x_1608_ = lean_string_utf8_next_fast(v_fst_1560_, v_searcher_1601_);
lean_dec(v_searcher_1601_);
if (v_isShared_1604_ == 0)
{
lean_ctor_set(v___x_1603_, 1, v___x_1608_);
v___x_1610_ = v___x_1603_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_currPos_1600_);
lean_ctor_set(v_reuseFailAlloc_1612_, 1, v___x_1608_);
v___x_1610_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
lean_object* v___x_1611_; 
v___x_1611_ = lean_apply_4(v_recur_1567_, v___x_1610_, v_acc_1565_, lean_box(0), lean_box(0));
return v___x_1611_;
}
}
else
{
lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v_slice_1616_; lean_object* v_nextIt_1618_; 
v___x_1613_ = lean_string_utf8_next_fast(v_fst_1560_, v_searcher_1601_);
v___x_1614_ = lean_nat_sub(v___x_1613_, v_searcher_1601_);
v___x_1615_ = lean_nat_add(v_searcher_1601_, v___x_1614_);
lean_dec(v___x_1614_);
v_slice_1616_ = l_String_Slice_subslice_x21(v___x_1563_, v_currPos_1600_, v_searcher_1601_);
lean_inc(v___x_1615_);
if (v_isShared_1604_ == 0)
{
lean_ctor_set(v___x_1603_, 1, v___x_1615_);
lean_ctor_set(v___x_1603_, 0, v___x_1615_);
v_nextIt_1618_ = v___x_1603_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v___x_1615_);
lean_ctor_set(v_reuseFailAlloc_1621_, 1, v___x_1615_);
v_nextIt_1618_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
lean_object* v_startInclusive_1619_; lean_object* v_endExclusive_1620_; 
v_startInclusive_1619_ = lean_ctor_get(v_slice_1616_, 0);
lean_inc(v_startInclusive_1619_);
v_endExclusive_1620_ = lean_ctor_get(v_slice_1616_, 1);
lean_inc(v_endExclusive_1620_);
lean_dec_ref(v_slice_1616_);
v_it_1586_ = v_nextIt_1618_;
v_startInclusive_1587_ = v_startInclusive_1619_;
v_endExclusive_1588_ = v_endExclusive_1620_;
goto v___jp_1585_;
}
}
}
else
{
lean_object* v___x_1622_; 
lean_del_object(v___x_1603_);
lean_dec(v_searcher_1601_);
v___x_1622_ = lean_box(1);
v_it_1586_ = v___x_1622_;
v_startInclusive_1587_ = v_currPos_1600_;
v_endExclusive_1588_ = v___x_1561_;
goto v___jp_1585_;
}
}
}
else
{
lean_dec_ref(v_recur_1567_);
lean_dec(v___x_1561_);
return v_acc_1565_;
}
v___jp_1568_:
{
if (lean_obj_tag(v_acc_1565_) == 0)
{
lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1571_, 0, v_out_1570_);
v___x_1572_ = lean_apply_4(v_recur_1567_, v_it_1569_, v___x_1571_, lean_box(0), lean_box(0));
return v___x_1572_;
}
else
{
lean_object* v_val_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1584_; 
v_val_1573_ = lean_ctor_get(v_acc_1565_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v_acc_1565_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1575_ = v_acc_1565_;
v_isShared_1576_ = v_isSharedCheck_1584_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_val_1573_);
lean_dec(v_acc_1565_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1584_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1581_; 
v___x_1577_ = lean_string_utf8_extract_fast(v___x_1557_, v___x_1558_, v___x_1559_);
v___x_1578_ = lean_string_append(v_val_1573_, v___x_1577_);
lean_dec_ref(v___x_1577_);
v___x_1579_ = lean_string_append(v___x_1578_, v_out_1570_);
lean_dec_ref(v_out_1570_);
if (v_isShared_1576_ == 0)
{
lean_ctor_set(v___x_1575_, 0, v___x_1579_);
v___x_1581_ = v___x_1575_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v___x_1579_);
v___x_1581_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
lean_object* v___x_1582_; 
v___x_1582_ = lean_apply_4(v_recur_1567_, v_it_1569_, v___x_1581_, lean_box(0), lean_box(0));
return v___x_1582_;
}
}
}
}
v___jp_1585_:
{
lean_object* v___x_1589_; uint32_t v___x_1590_; uint32_t v___x_1591_; uint8_t v___x_1592_; 
v___x_1589_ = lean_string_utf8_extract_fast(v_fst_1560_, v_startInclusive_1587_, v_endExclusive_1588_);
lean_dec(v_endExclusive_1588_);
lean_dec(v_startInclusive_1587_);
v___x_1590_ = lean_string_utf8_get(v___x_1589_, v___x_1558_);
v___x_1591_ = 97;
v___x_1592_ = lean_uint32_dec_le(v___x_1591_, v___x_1590_);
if (v___x_1592_ == 0)
{
lean_object* v___x_1593_; 
v___x_1593_ = lean_string_utf8_set(v___x_1589_, v___x_1558_, v___x_1590_);
v_it_1569_ = v_it_1586_;
v_out_1570_ = v___x_1593_;
goto v___jp_1568_;
}
else
{
uint32_t v___x_1594_; uint8_t v___x_1595_; 
v___x_1594_ = 122;
v___x_1595_ = lean_uint32_dec_le(v___x_1590_, v___x_1594_);
if (v___x_1595_ == 0)
{
lean_object* v___x_1596_; 
v___x_1596_ = lean_string_utf8_set(v___x_1589_, v___x_1558_, v___x_1590_);
v_it_1569_ = v_it_1586_;
v_out_1570_ = v___x_1596_;
goto v___jp_1568_;
}
else
{
uint32_t v___x_1597_; uint32_t v___x_1598_; lean_object* v___x_1599_; 
v___x_1597_ = 4294967264;
v___x_1598_ = lean_uint32_add(v___x_1590_, v___x_1597_);
v___x_1599_ = lean_string_utf8_set(v___x_1589_, v___x_1558_, v___x_1598_);
v_it_1569_ = v_it_1586_;
v_out_1570_ = v___x_1599_;
goto v___jp_1568_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Headers_instToString___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1557_ = stack[0].m_obj;
lean_object* v___x_1558_ = stack[1].m_obj;
lean_object* v___x_1559_ = stack[2].m_obj;
lean_object* v_fst_1560_ = stack[3].m_obj;
lean_object* v___x_1561_ = stack[4].m_obj;
uint32_t v___x_1562_ = stack[5].m_num;
lean_object* v___x_1563_ = stack[6].m_obj;
lean_object* v_it_1564_ = stack[7].m_obj;
lean_object* v_acc_1565_ = stack[8].m_obj;
lean_object* v_recur_1567_ = stack[10].m_obj;
lean_object* v_res_1624_;
v_res_1624_ = l_Std_Http_Headers_instToString___lam__0(v___x_1557_, v___x_1558_, v___x_1559_, v_fst_1560_, v___x_1561_, v___x_1562_, v___x_1563_, v_it_1564_, v_acc_1565_, lean_box(0), v_recur_1567_);
stack->m_obj
 = v_res_1624_;
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instToString___lam__0___boxed(lean_object* v___x_1625_, lean_object* v___x_1626_, lean_object* v___x_1627_, lean_object* v_fst_1628_, lean_object* v___x_1629_, lean_object* v___x_1630_, lean_object* v___x_1631_, lean_object* v_it_1632_, lean_object* v_acc_1633_, lean_object* v_hP_1634_, lean_object* v_recur_1635_){
_start:
{
uint32_t v___x_1801__boxed_1636_; lean_object* v_res_1637_; 
v___x_1801__boxed_1636_ = lean_unbox_uint32(v___x_1630_);
lean_dec(v___x_1630_);
v_res_1637_ = l_Std_Http_Headers_instToString___lam__0(v___x_1625_, v___x_1626_, v___x_1627_, v_fst_1628_, v___x_1629_, v___x_1801__boxed_1636_, v___x_1631_, v_it_1632_, v_acc_1633_, v_hP_1634_, v_recur_1635_);
lean_dec_ref(v___x_1631_);
lean_dec_ref(v_fst_1628_);
lean_dec(v___x_1627_);
lean_dec(v___x_1626_);
lean_dec_ref(v___x_1625_);
return v_res_1637_;
}
}
static lean_object* _init_l_Std_Http_Headers_instToString___lam__1___boxed__const__1(void){
_start:
{
uint32_t v___x_1641_; lean_object* v___x_1642_; 
v___x_1641_ = 45;
v___x_1642_ = lean_box_uint32(v___x_1641_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instToString___lam__1(lean_object* v_x_1643_){
_start:
{
lean_object* v_fst_1644_; lean_object* v_snd_1645_; lean_object* v___y_1647_; lean_object* v___f_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v_it_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___f_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
v_fst_1644_ = lean_ctor_get(v_x_1643_, 0);
lean_inc_n(v_fst_1644_, 2);
v_snd_1645_ = lean_ctor_get(v_x_1643_, 1);
lean_inc(v_snd_1645_);
lean_dec_ref(v_x_1643_);
v___f_1651_ = ((lean_object*)(l_Std_Http_Headers_instToString___lam__1___closed__1));
v___x_1652_ = lean_unsigned_to_nat(0u);
v___x_1653_ = lean_string_utf8_byte_size(v_fst_1644_);
v___x_1654_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1654_, 0, v_fst_1644_);
lean_ctor_set(v___x_1654_, 1, v___x_1652_);
lean_ctor_set(v___x_1654_, 2, v___x_1653_);
lean_inc_ref(v___x_1654_);
v_it_1655_ = l_String_Slice_splitToSubslice___redArg(v___x_1654_, v___f_1651_);
v___x_1656_ = ((lean_object*)(l_Std_Http_Headers_instToString___lam__1___closed__2));
v___x_1657_ = lean_unsigned_to_nat(1u);
v___x_1658_ = l_Std_Http_Headers_instToString___lam__1___boxed__const__1;
v___f_1659_ = lean_alloc_closure((void*)(l_Std_Http_Headers_instToString___lam__0___boxed), 11, 7);
lean_closure_set(v___f_1659_, 0, v___x_1656_);
lean_closure_set(v___f_1659_, 1, v___x_1652_);
lean_closure_set(v___f_1659_, 2, v___x_1657_);
lean_closure_set(v___f_1659_, 3, v_fst_1644_);
lean_closure_set(v___f_1659_, 4, v___x_1653_);
lean_closure_set(v___f_1659_, 5, v___x_1658_);
lean_closure_set(v___f_1659_, 6, v___x_1654_);
v___x_1660_ = lean_box(0);
v___x_1661_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1659_, v_it_1655_, v___x_1660_, lean_box(0));
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v___x_1662_; 
v___x_1662_ = ((lean_object*)(l_Std_Http_Headers_get_x21___closed__0));
v___y_1647_ = v___x_1662_;
goto v___jp_1646_;
}
else
{
lean_object* v_val_1663_; 
v_val_1663_ = lean_ctor_get(v___x_1661_, 0);
lean_inc(v_val_1663_);
lean_dec_ref_known(v___x_1661_, 1);
v___y_1647_ = v_val_1663_;
goto v___jp_1646_;
}
v___jp_1646_:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1648_ = ((lean_object*)(l_Std_Http_Headers_instToString___lam__1___closed__0));
v___x_1649_ = lean_string_append(v___y_1647_, v___x_1648_);
v___x_1650_ = lean_string_append(v___x_1649_, v_snd_1645_);
lean_dec(v_snd_1645_);
return v___x_1650_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instToString___lam__2(lean_object* v___f_1665_, lean_object* v_headers_1666_){
_start:
{
lean_object* v_entries_1667_; lean_object* v___x_1668_; size_t v_sz_1669_; size_t v___x_1670_; lean_object* v_pairs_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; 
v_entries_1667_ = lean_ctor_get(v_headers_1666_, 0);
lean_inc_ref(v_entries_1667_);
lean_dec_ref(v_headers_1666_);
v___x_1668_ = ((lean_object*)(l_Std_Http_Headers_getAll___redArg___closed__9));
v_sz_1669_ = lean_array_size(v_entries_1667_);
v___x_1670_ = ((size_t)0ULL);
v_pairs_1671_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1668_, v___f_1665_, v_sz_1669_, v___x_1670_, v_entries_1667_);
v___x_1672_ = ((lean_object*)(l_Std_Http_Headers_instToString___lam__2___closed__0));
v___x_1673_ = lean_array_to_list(v_pairs_1671_);
v___x_1674_ = l_String_intercalate(v___x_1672_, v___x_1673_);
return v___x_1674_;
}
}
lean_object* l_Std_Http_Headers_instEncodeV11___lam__0(lean_object* v___x_1679_, lean_object* v___x_1680_, lean_object* v___x_1681_, lean_object* v_name_1682_, lean_object* v___x_1683_, uint32_t v___x_1684_, lean_object* v___x_1685_, lean_object* v_it_1686_, lean_object* v_acc_1687_, lean_object* v_hP_1688_, lean_object* v_recur_1689_){
_start:
{
lean_object* v_it_1691_; lean_object* v_out_1692_; lean_object* v_it_1708_; lean_object* v_startInclusive_1709_; lean_object* v_endExclusive_1710_; 
if (lean_obj_tag(v_it_1686_) == 0)
{
lean_object* v_currPos_1722_; lean_object* v_searcher_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1745_; 
v_currPos_1722_ = lean_ctor_get(v_it_1686_, 0);
v_searcher_1723_ = lean_ctor_get(v_it_1686_, 1);
v_isSharedCheck_1745_ = !lean_is_exclusive(v_it_1686_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1725_ = v_it_1686_;
v_isShared_1726_ = v_isSharedCheck_1745_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_searcher_1723_);
lean_inc(v_currPos_1722_);
lean_dec(v_it_1686_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1745_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
uint8_t v_decide_1727_; 
v_decide_1727_ = lean_nat_dec_eq(v_searcher_1723_, v___x_1683_);
if (v_decide_1727_ == 0)
{
uint32_t v___x_1728_; uint8_t v___x_1729_; 
lean_dec(v___x_1683_);
v___x_1728_ = lean_string_utf8_get_fast(v_name_1682_, v_searcher_1723_);
v___x_1729_ = lean_uint32_dec_eq(v___x_1728_, v___x_1684_);
if (v___x_1729_ == 0)
{
lean_object* v___x_1730_; lean_object* v___x_1732_; 
v___x_1730_ = lean_string_utf8_next_fast(v_name_1682_, v_searcher_1723_);
lean_dec(v_searcher_1723_);
if (v_isShared_1726_ == 0)
{
lean_ctor_set(v___x_1725_, 1, v___x_1730_);
v___x_1732_ = v___x_1725_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_currPos_1722_);
lean_ctor_set(v_reuseFailAlloc_1734_, 1, v___x_1730_);
v___x_1732_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
lean_object* v___x_1733_; 
v___x_1733_ = lean_apply_4(v_recur_1689_, v___x_1732_, v_acc_1687_, lean_box(0), lean_box(0));
return v___x_1733_;
}
}
else
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v_slice_1738_; lean_object* v_nextIt_1740_; 
v___x_1735_ = lean_string_utf8_next_fast(v_name_1682_, v_searcher_1723_);
v___x_1736_ = lean_nat_sub(v___x_1735_, v_searcher_1723_);
v___x_1737_ = lean_nat_add(v_searcher_1723_, v___x_1736_);
lean_dec(v___x_1736_);
v_slice_1738_ = l_String_Slice_subslice_x21(v___x_1685_, v_currPos_1722_, v_searcher_1723_);
lean_inc(v___x_1737_);
if (v_isShared_1726_ == 0)
{
lean_ctor_set(v___x_1725_, 1, v___x_1737_);
lean_ctor_set(v___x_1725_, 0, v___x_1737_);
v_nextIt_1740_ = v___x_1725_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v___x_1737_);
lean_ctor_set(v_reuseFailAlloc_1743_, 1, v___x_1737_);
v_nextIt_1740_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
lean_object* v_startInclusive_1741_; lean_object* v_endExclusive_1742_; 
v_startInclusive_1741_ = lean_ctor_get(v_slice_1738_, 0);
lean_inc(v_startInclusive_1741_);
v_endExclusive_1742_ = lean_ctor_get(v_slice_1738_, 1);
lean_inc(v_endExclusive_1742_);
lean_dec_ref(v_slice_1738_);
v_it_1708_ = v_nextIt_1740_;
v_startInclusive_1709_ = v_startInclusive_1741_;
v_endExclusive_1710_ = v_endExclusive_1742_;
goto v___jp_1707_;
}
}
}
else
{
lean_object* v___x_1744_; 
lean_del_object(v___x_1725_);
lean_dec(v_searcher_1723_);
v___x_1744_ = lean_box(1);
v_it_1708_ = v___x_1744_;
v_startInclusive_1709_ = v_currPos_1722_;
v_endExclusive_1710_ = v___x_1683_;
goto v___jp_1707_;
}
}
}
else
{
lean_dec_ref(v_recur_1689_);
lean_dec(v___x_1683_);
return v_acc_1687_;
}
v___jp_1690_:
{
if (lean_obj_tag(v_acc_1687_) == 0)
{
lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1693_, 0, v_out_1692_);
v___x_1694_ = lean_apply_4(v_recur_1689_, v_it_1691_, v___x_1693_, lean_box(0), lean_box(0));
return v___x_1694_;
}
else
{
lean_object* v_val_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1706_; 
v_val_1695_ = lean_ctor_get(v_acc_1687_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v_acc_1687_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1697_ = v_acc_1687_;
v_isShared_1698_ = v_isSharedCheck_1706_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_val_1695_);
lean_dec(v_acc_1687_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1706_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1703_; 
v___x_1699_ = lean_string_utf8_extract_fast(v___x_1679_, v___x_1680_, v___x_1681_);
v___x_1700_ = lean_string_append(v_val_1695_, v___x_1699_);
lean_dec_ref(v___x_1699_);
v___x_1701_ = lean_string_append(v___x_1700_, v_out_1692_);
lean_dec_ref(v_out_1692_);
if (v_isShared_1698_ == 0)
{
lean_ctor_set(v___x_1697_, 0, v___x_1701_);
v___x_1703_ = v___x_1697_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v___x_1701_);
v___x_1703_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
lean_object* v___x_1704_; 
v___x_1704_ = lean_apply_4(v_recur_1689_, v_it_1691_, v___x_1703_, lean_box(0), lean_box(0));
return v___x_1704_;
}
}
}
}
v___jp_1707_:
{
lean_object* v___x_1711_; uint32_t v___x_1712_; uint32_t v___x_1713_; uint8_t v___x_1714_; 
v___x_1711_ = lean_string_utf8_extract_fast(v_name_1682_, v_startInclusive_1709_, v_endExclusive_1710_);
lean_dec(v_endExclusive_1710_);
lean_dec(v_startInclusive_1709_);
v___x_1712_ = lean_string_utf8_get(v___x_1711_, v___x_1680_);
v___x_1713_ = 97;
v___x_1714_ = lean_uint32_dec_le(v___x_1713_, v___x_1712_);
if (v___x_1714_ == 0)
{
lean_object* v___x_1715_; 
v___x_1715_ = lean_string_utf8_set(v___x_1711_, v___x_1680_, v___x_1712_);
v_it_1691_ = v_it_1708_;
v_out_1692_ = v___x_1715_;
goto v___jp_1690_;
}
else
{
uint32_t v___x_1716_; uint8_t v___x_1717_; 
v___x_1716_ = 122;
v___x_1717_ = lean_uint32_dec_le(v___x_1712_, v___x_1716_);
if (v___x_1717_ == 0)
{
lean_object* v___x_1718_; 
v___x_1718_ = lean_string_utf8_set(v___x_1711_, v___x_1680_, v___x_1712_);
v_it_1691_ = v_it_1708_;
v_out_1692_ = v___x_1718_;
goto v___jp_1690_;
}
else
{
uint32_t v___x_1719_; uint32_t v___x_1720_; lean_object* v___x_1721_; 
v___x_1719_ = 4294967264;
v___x_1720_ = lean_uint32_add(v___x_1712_, v___x_1719_);
v___x_1721_ = lean_string_utf8_set(v___x_1711_, v___x_1680_, v___x_1720_);
v_it_1691_ = v_it_1708_;
v_out_1692_ = v___x_1721_;
goto v___jp_1690_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Headers_instEncodeV11___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1679_ = stack[0].m_obj;
lean_object* v___x_1680_ = stack[1].m_obj;
lean_object* v___x_1681_ = stack[2].m_obj;
lean_object* v_name_1682_ = stack[3].m_obj;
lean_object* v___x_1683_ = stack[4].m_obj;
uint32_t v___x_1684_ = stack[5].m_num;
lean_object* v___x_1685_ = stack[6].m_obj;
lean_object* v_it_1686_ = stack[7].m_obj;
lean_object* v_acc_1687_ = stack[8].m_obj;
lean_object* v_recur_1689_ = stack[10].m_obj;
lean_object* v_res_1746_;
v_res_1746_ = l_Std_Http_Headers_instEncodeV11___lam__0(v___x_1679_, v___x_1680_, v___x_1681_, v_name_1682_, v___x_1683_, v___x_1684_, v___x_1685_, v_it_1686_, v_acc_1687_, lean_box(0), v_recur_1689_);
stack->m_obj
 = v_res_1746_;
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instEncodeV11___lam__0___boxed(lean_object* v___x_1747_, lean_object* v___x_1748_, lean_object* v___x_1749_, lean_object* v_name_1750_, lean_object* v___x_1751_, lean_object* v___x_1752_, lean_object* v___x_1753_, lean_object* v_it_1754_, lean_object* v_acc_1755_, lean_object* v_hP_1756_, lean_object* v_recur_1757_){
_start:
{
uint32_t v___x_950__boxed_1758_; lean_object* v_res_1759_; 
v___x_950__boxed_1758_ = lean_unbox_uint32(v___x_1752_);
lean_dec(v___x_1752_);
v_res_1759_ = l_Std_Http_Headers_instEncodeV11___lam__0(v___x_1747_, v___x_1748_, v___x_1749_, v_name_1750_, v___x_1751_, v___x_950__boxed_1758_, v___x_1753_, v_it_1754_, v_acc_1755_, v_hP_1756_, v_recur_1757_);
lean_dec_ref(v___x_1753_);
lean_dec_ref(v_name_1750_);
lean_dec(v___x_1749_);
lean_dec(v___x_1748_);
lean_dec_ref(v___x_1747_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instEncodeV11___lam__1(lean_object* v_buf_1760_, lean_object* v_name_1761_, lean_object* v_value_1762_){
_start:
{
lean_object* v___y_1764_; lean_object* v___f_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v_it_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___f_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; 
v___f_1783_ = ((lean_object*)(l_Std_Http_Headers_instToString___lam__1___closed__1));
v___x_1784_ = lean_unsigned_to_nat(0u);
v___x_1785_ = lean_string_utf8_byte_size(v_name_1761_);
lean_inc_ref(v_name_1761_);
v___x_1786_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1786_, 0, v_name_1761_);
lean_ctor_set(v___x_1786_, 1, v___x_1784_);
lean_ctor_set(v___x_1786_, 2, v___x_1785_);
lean_inc_ref(v___x_1786_);
v_it_1787_ = l_String_Slice_splitToSubslice___redArg(v___x_1786_, v___f_1783_);
v___x_1788_ = ((lean_object*)(l_Std_Http_Headers_instToString___lam__1___closed__2));
v___x_1789_ = lean_unsigned_to_nat(1u);
v___x_1790_ = l_Std_Http_Headers_instToString___lam__1___boxed__const__1;
v___f_1791_ = lean_alloc_closure((void*)(l_Std_Http_Headers_instEncodeV11___lam__0___boxed), 11, 7);
lean_closure_set(v___f_1791_, 0, v___x_1788_);
lean_closure_set(v___f_1791_, 1, v___x_1784_);
lean_closure_set(v___f_1791_, 2, v___x_1789_);
lean_closure_set(v___f_1791_, 3, v_name_1761_);
lean_closure_set(v___f_1791_, 4, v___x_1785_);
lean_closure_set(v___f_1791_, 5, v___x_1790_);
lean_closure_set(v___f_1791_, 6, v___x_1786_);
v___x_1792_ = lean_box(0);
v___x_1793_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1791_, v_it_1787_, v___x_1792_, lean_box(0));
if (lean_obj_tag(v___x_1793_) == 0)
{
lean_object* v___x_1794_; 
v___x_1794_ = ((lean_object*)(l_Std_Http_Headers_get_x21___closed__0));
v___y_1764_ = v___x_1794_;
goto v___jp_1763_;
}
else
{
lean_object* v_val_1795_; 
v_val_1795_ = lean_ctor_get(v___x_1793_, 0);
lean_inc(v_val_1795_);
lean_dec_ref_known(v___x_1793_, 1);
v___y_1764_ = v_val_1795_;
goto v___jp_1763_;
}
v___jp_1763_:
{
lean_object* v_data_1765_; lean_object* v_size_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1782_; 
v_data_1765_ = lean_ctor_get(v_buf_1760_, 0);
v_size_1766_ = lean_ctor_get(v_buf_1760_, 1);
v_isSharedCheck_1782_ = !lean_is_exclusive(v_buf_1760_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1768_ = v_buf_1760_;
v_isShared_1769_ = v_isSharedCheck_1782_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_size_1766_);
lean_inc(v_data_1765_);
lean_dec(v_buf_1760_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1782_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1780_; 
v___x_1770_ = ((lean_object*)(l_Std_Http_Headers_instToString___lam__1___closed__0));
v___x_1771_ = lean_string_append(v___y_1764_, v___x_1770_);
v___x_1772_ = lean_string_append(v___x_1771_, v_value_1762_);
v___x_1773_ = ((lean_object*)(l_Std_Http_Headers_instToString___lam__2___closed__0));
v___x_1774_ = lean_string_append(v___x_1772_, v___x_1773_);
v___x_1775_ = lean_string_to_utf8(v___x_1774_);
lean_dec_ref(v___x_1774_);
lean_inc_ref(v___x_1775_);
v___x_1776_ = lean_array_push(v_data_1765_, v___x_1775_);
v___x_1777_ = lean_byte_array_size(v___x_1775_);
lean_dec_ref(v___x_1775_);
v___x_1778_ = lean_nat_add(v_size_1766_, v___x_1777_);
lean_dec(v_size_1766_);
if (v_isShared_1769_ == 0)
{
lean_ctor_set(v___x_1768_, 1, v___x_1778_);
lean_ctor_set(v___x_1768_, 0, v___x_1776_);
v___x_1780_ = v___x_1768_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v___x_1776_);
lean_ctor_set(v_reuseFailAlloc_1781_, 1, v___x_1778_);
v___x_1780_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
return v___x_1780_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instEncodeV11___lam__1___boxed(lean_object* v_buf_1796_, lean_object* v_name_1797_, lean_object* v_value_1798_){
_start:
{
lean_object* v_res_1799_; 
v_res_1799_ = l_Std_Http_Headers_instEncodeV11___lam__1(v_buf_1796_, v_name_1797_, v_value_1798_);
lean_dec_ref(v_value_1798_);
return v_res_1799_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instEncodeV11___lam__2(lean_object* v___f_1800_, lean_object* v_buffer_1801_, lean_object* v_headers_1802_){
_start:
{
lean_object* v___x_1803_; 
v___x_1803_ = l_Std_Http_Headers_fold___redArg(v_headers_1802_, v_buffer_1801_, v___f_1800_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instEncodeV11___lam__2___boxed(lean_object* v___f_1804_, lean_object* v_buffer_1805_, lean_object* v_headers_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l_Std_Http_Headers_instEncodeV11___lam__2(v___f_1804_, v_buffer_1805_, v_headers_1806_);
lean_dec_ref(v_headers_1806_);
return v_res_1807_;
}
}
static lean_object* _init_l_Std_Http_Headers_instEmptyCollection(void){
_start:
{
lean_object* v___x_1812_; 
v___x_1812_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__0, &l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__0_once, _init_l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__0);
return v___x_1812_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instSingletonProdNameValue___lam__1(lean_object* v_x_1813_){
_start:
{
lean_object* v_fst_1814_; lean_object* v___x_1815_; lean_object* v_entries_1816_; lean_object* v_indexes_1817_; lean_object* v___f_1818_; lean_object* v___f_1819_; lean_object* v_i_1820_; lean_object* v_f_1821_; lean_object* v_entries_1822_; lean_object* v_indexes_1823_; lean_object* v___x_1824_; 
v_fst_1814_ = lean_ctor_get(v_x_1813_, 0);
lean_inc(v_fst_1814_);
v___x_1815_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__0, &l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__0_once, _init_l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__0);
v_entries_1816_ = lean_ctor_get(v___x_1815_, 0);
v_indexes_1817_ = lean_ctor_get(v___x_1815_, 1);
v___f_1818_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_1819_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v_i_1820_ = lean_array_get_size(v_entries_1816_);
v_f_1821_ = lean_alloc_closure((void*)(l_Std_Http_Headers_insert___lam__0), 2, 1);
lean_closure_set(v_f_1821_, 0, v_i_1820_);
lean_inc_ref(v_entries_1816_);
v_entries_1822_ = lean_array_push(v_entries_1816_, v_x_1813_);
lean_inc_ref(v_indexes_1817_);
v_indexes_1823_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_1818_, v___f_1819_, v_indexes_1817_, v_fst_1814_, v_f_1821_);
v___x_1824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1824_, 0, v_entries_1822_);
lean_ctor_set(v___x_1824_, 1, v_indexes_1823_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instInsertProdNameValue___lam__1(lean_object* v_x_1827_, lean_object* v_s_1828_){
_start:
{
lean_object* v_fst_1829_; lean_object* v_entries_1830_; lean_object* v_indexes_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1844_; 
v_fst_1829_ = lean_ctor_get(v_x_1827_, 0);
lean_inc(v_fst_1829_);
v_entries_1830_ = lean_ctor_get(v_s_1828_, 0);
v_indexes_1831_ = lean_ctor_get(v_s_1828_, 1);
v_isSharedCheck_1844_ = !lean_is_exclusive(v_s_1828_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1833_ = v_s_1828_;
v_isShared_1834_ = v_isSharedCheck_1844_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_indexes_1831_);
lean_inc(v_entries_1830_);
lean_dec(v_s_1828_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1844_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v___f_1835_; lean_object* v___f_1836_; lean_object* v_i_1837_; lean_object* v_f_1838_; lean_object* v_entries_1839_; lean_object* v_indexes_1840_; lean_object* v___x_1842_; 
v___f_1835_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_1836_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v_i_1837_ = lean_array_get_size(v_entries_1830_);
v_f_1838_ = lean_alloc_closure((void*)(l_Std_Http_Headers_insert___lam__0), 2, 1);
lean_closure_set(v_f_1838_, 0, v_i_1837_);
v_entries_1839_ = lean_array_push(v_entries_1830_, v_x_1827_);
v_indexes_1840_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_1835_, v___f_1836_, v_indexes_1831_, v_fst_1829_, v_f_1838_);
if (v_isShared_1834_ == 0)
{
lean_ctor_set(v___x_1833_, 1, v_indexes_1840_);
lean_ctor_set(v___x_1833_, 0, v_entries_1839_);
v___x_1842_ = v___x_1833_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_entries_1839_);
lean_ctor_set(v_reuseFailAlloc_1843_, 1, v_indexes_1840_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instForInProdNameValueOfMonad___redArg___lam__0(lean_object* v_f_1849_, lean_object* v_a_1850_, lean_object* v_x_1851_, lean_object* v___y_1852_){
_start:
{
lean_object* v___x_1853_; 
v___x_1853_ = lean_apply_2(v_f_1849_, v_a_1850_, v___y_1852_);
return v___x_1853_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instForInProdNameValueOfMonad___redArg___lam__1(lean_object* v_inst_1854_, lean_object* v_00_u03b2_1855_, lean_object* v_headers_1856_, lean_object* v_b_1857_, lean_object* v_f_1858_){
_start:
{
lean_object* v_entries_1859_; lean_object* v___f_1860_; size_t v_sz_1861_; size_t v___x_1862_; lean_object* v___x_1863_; 
v_entries_1859_ = lean_ctor_get(v_headers_1856_, 0);
lean_inc_ref(v_entries_1859_);
lean_dec_ref(v_headers_1856_);
v___f_1860_ = lean_alloc_closure((void*)(l_Std_Http_Headers_instForInProdNameValueOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1860_, 0, v_f_1858_);
v_sz_1861_ = lean_array_size(v_entries_1859_);
v___x_1862_ = ((size_t)0ULL);
v___x_1863_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1854_, v_entries_1859_, v___f_1860_, v_sz_1861_, v___x_1862_, v_b_1857_);
return v___x_1863_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instForInProdNameValueOfMonad___redArg(lean_object* v_inst_1864_){
_start:
{
lean_object* v___f_1865_; 
v___f_1865_ = lean_alloc_closure((void*)(l_Std_Http_Headers_instForInProdNameValueOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_1865_, 0, v_inst_1864_);
return v___f_1865_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instForInProdNameValueOfMonad(lean_object* v_m_1866_, lean_object* v_inst_1867_){
_start:
{
lean_object* v___f_1868_; 
v___f_1868_ = lean_alloc_closure((void*)(l_Std_Http_Headers_instForInProdNameValueOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_1868_, 0, v_inst_1867_);
return v___f_1868_;
}
}
lean_object* runtime_initialize_Std_Http_Data_Headers_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_Headers_Name(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_Headers_Value(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Data_Headers(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
