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
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_String_decEq___boxed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Std_Internal_MultiMap_findLastIdxBelow___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Std_Http_Header_instReprName_repr___redArg(lean_object*);
lean_object* l_Std_Http_Header_instReprValue_repr___redArg(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_Internal_MultiMap_empty___redArg();
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t l_Std_Http_Header_instBEqValue_beq(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* l_Std_Internal_MultiMap_findIdxFrom___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___redArg___lam__0___boxed(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l_Std_Http_Internal_appendFieldLine___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_splitToSubslice___redArg(lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Std_Http_Header_Name_ofString_x21(lean_object*);
lean_object* l_Std_Http_Header_Value_ofString_x21(lean_object*);
lean_object* l_Std_Internal_instInhabitedMultiMap_default___redArg();
lean_object* l_Std_Http_Header_Name_ofString_x3f(lean_object*);
lean_object* l_Std_Http_Header_Value_ofString_x3f(lean_object*);
uint8_t l_Std_Internal_MultiMap_instDecidableMem___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
static lean_once_cell_t l_Std_Http_instInhabitedHeaders_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_instInhabitedHeaders_default___closed__0;
LEAN_EXPORT lean_object* l_Std_Http_instInhabitedHeaders_default;
LEAN_EXPORT lean_object* l_Std_Http_instInhabitedHeaders;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Http_instReprHeaders_repr_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*);
static const lean_string_object l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg___closed__0 = (const lean_object*)&l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg___closed__0_value;
static const lean_string_object l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg___closed__1 = (const lean_object*)&l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg___closed__1_value;
static const lean_ctor_object l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg___closed__1_value)}};
static const lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg___closed__2 = (const lean_object*)&l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg___closed__2_value;
static const lean_ctor_object l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg___closed__3 = (const lean_object*)&l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg___closed__3_value;
static const lean_string_object l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg___closed__4 = (const lean_object*)&l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg___closed__4_value;
static lean_once_cell_t l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg___closed__5;
static lean_once_cell_t l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg___closed__6;
static const lean_ctor_object l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg___closed__0_value)}};
static const lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg___closed__7 = (const lean_object*)&l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg___closed__7_value;
static const lean_ctor_object l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg___closed__4_value)}};
static const lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg___closed__8 = (const lean_object*)&l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg___closed__8_value;
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__3_spec__5_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__3(lean_object*, lean_object*);
static const lean_string_object l_Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0___closed__0 = (const lean_object*)&l_Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0___closed__0_value;
static const lean_string_object l_Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0___closed__1 = (const lean_object*)&l_Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0___closed__1_value;
static lean_once_cell_t l_Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0___closed__2;
static lean_once_cell_t l_Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0___closed__3;
static const lean_ctor_object l_Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0___closed__0_value)}};
static const lean_object* l_Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0___closed__4 = (const lean_object*)&l_Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0___closed__4_value;
static const lean_ctor_object l_Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0___closed__1_value)}};
static const lean_object* l_Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0___closed__5 = (const lean_object*)&l_Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0___closed__5_value;
static const lean_string_object l_Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "#[]"};
static const lean_object* l_Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0___closed__6 = (const lean_object*)&l_Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0___closed__6_value;
static const lean_ctor_object l_Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0___closed__6_value)}};
static const lean_object* l_Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0___closed__7 = (const lean_object*)&l_Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0___closed__7_value;
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0(lean_object*);
static const lean_string_object l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__0 = (const lean_object*)&l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__0_value;
static const lean_string_object l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "entries"};
static const lean_object* l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__1 = (const lean_object*)&l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__1_value;
static const lean_ctor_object l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__1_value)}};
static const lean_object* l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__2 = (const lean_object*)&l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__2_value;
static const lean_ctor_object l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__2_value)}};
static const lean_object* l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__3 = (const lean_object*)&l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__3_value;
static const lean_string_object l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__4 = (const lean_object*)&l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__4_value;
static const lean_ctor_object l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__4_value)}};
static const lean_object* l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__5 = (const lean_object*)&l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__5_value;
static const lean_ctor_object l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__3_value),((lean_object*)&l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__5_value)}};
static const lean_object* l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__6 = (const lean_object*)&l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__6_value;
static lean_once_cell_t l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__7;
static const lean_string_object l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__8 = (const lean_object*)&l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__8_value;
static lean_once_cell_t l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__9;
static lean_once_cell_t l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__10;
static const lean_ctor_object l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__0_value)}};
static const lean_object* l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__11 = (const lean_object*)&l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__11_value;
static const lean_ctor_object l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__8_value)}};
static const lean_object* l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__12 = (const lean_object*)&l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__12_value;
LEAN_EXPORT lean_object* l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg(lean_object*);
static const lean_string_object l_Std_Http_instReprHeaders_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "map"};
static const lean_object* l_Std_Http_instReprHeaders_repr___redArg___closed__0 = (const lean_object*)&l_Std_Http_instReprHeaders_repr___redArg___closed__0_value;
static const lean_ctor_object l_Std_Http_instReprHeaders_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_instReprHeaders_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Http_instReprHeaders_repr___redArg___closed__1 = (const lean_object*)&l_Std_Http_instReprHeaders_repr___redArg___closed__1_value;
static const lean_ctor_object l_Std_Http_instReprHeaders_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_instReprHeaders_repr___redArg___closed__1_value)}};
static const lean_object* l_Std_Http_instReprHeaders_repr___redArg___closed__2 = (const lean_object*)&l_Std_Http_instReprHeaders_repr___redArg___closed__2_value;
static const lean_ctor_object l_Std_Http_instReprHeaders_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Http_instReprHeaders_repr___redArg___closed__2_value),((lean_object*)&l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__5_value)}};
static const lean_object* l_Std_Http_instReprHeaders_repr___redArg___closed__3 = (const lean_object*)&l_Std_Http_instReprHeaders_repr___redArg___closed__3_value;
static lean_once_cell_t l_Std_Http_instReprHeaders_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_instReprHeaders_repr___redArg___closed__4;
LEAN_EXPORT lean_object* l_Std_Http_instReprHeaders_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instReprHeaders_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instReprHeaders_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_instReprHeaders___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_instReprHeaders_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_instReprHeaders___closed__0 = (const lean_object*)&l_Std_Http_instReprHeaders___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_instReprHeaders = (const lean_object*)&l_Std_Http_instReprHeaders___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_instMembershipNameHeaders;
static const lean_closure_object l_Std_Http_instDecidableMemNameHeaders___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_decEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_instDecidableMemNameHeaders___closed__0 = (const lean_object*)&l_Std_Http_instDecidableMemNameHeaders___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Http_instDecidableMemNameHeaders(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instDecidableMemNameHeaders___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_get___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_get___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_get___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_getAll___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_getAll___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Std_Http_Headers_getAll___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Http_Headers_getAll___redArg___closed__0 = (const lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__0_value;
static const lean_closure_object l_Std_Http_Headers_getAll___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Headers_getAll___redArg___closed__1 = (const lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__1_value;
static const lean_closure_object l_Std_Http_Headers_getAll___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Headers_getAll___redArg___closed__2 = (const lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__2_value;
static const lean_closure_object l_Std_Http_Headers_getAll___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Headers_getAll___redArg___closed__3 = (const lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__3_value;
static const lean_closure_object l_Std_Http_Headers_getAll___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Headers_getAll___redArg___closed__4 = (const lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__4_value;
static const lean_closure_object l_Std_Http_Headers_getAll___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Headers_getAll___redArg___closed__5 = (const lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__5_value;
static const lean_closure_object l_Std_Http_Headers_getAll___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Headers_getAll___redArg___closed__6 = (const lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__6_value;
static const lean_closure_object l_Std_Http_Headers_getAll___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Headers_getAll___redArg___closed__7 = (const lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__7_value;
static const lean_ctor_object l_Std_Http_Headers_getAll___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__1_value),((lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__2_value)}};
static const lean_object* l_Std_Http_Headers_getAll___redArg___closed__8 = (const lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__8_value;
static const lean_ctor_object l_Std_Http_Headers_getAll___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__8_value),((lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__3_value),((lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__4_value),((lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__5_value),((lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__6_value)}};
static const lean_object* l_Std_Http_Headers_getAll___redArg___closed__9 = (const lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__9_value;
static const lean_ctor_object l_Std_Http_Headers_getAll___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__9_value),((lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__7_value)}};
static const lean_object* l_Std_Http_Headers_getAll___redArg___closed__10 = (const lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__10_value;
LEAN_EXPORT lean_object* l_Std_Http_Headers_getAll___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_getAll(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_getAll_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_get_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_get_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Headers_hasEntry___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_hasEntry___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Headers_hasEntry(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_hasEntry___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_getLast_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_getLast_x3f___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_Headers_insert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_insert_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_insert_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_insertMany___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_insertMany(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Http_Headers_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Headers_empty___closed__0;
LEAN_EXPORT lean_object* l_Std_Http_Headers_empty;
LEAN_EXPORT lean_object* l_Std_Http_Headers_ofList(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Headers_contains___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_contains___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Headers_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_contains___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_erase___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_erase___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Std_Http_Headers_erase___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Http_Headers_erase___closed__0 = (const lean_object*)&l_Std_Http_Headers_erase___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Headers_erase(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Headers_eraseMany___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_eraseMany___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_eraseMany___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_eraseMany(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_size___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Headers_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_isEmpty___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_merge(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_merge___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Headers_update_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Headers_update_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Headers_update_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Headers_update_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Std_Http_Headers_instEncodeV11___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Internal_appendFieldLine___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Headers_instEncodeV11___lam__0___closed__0 = (const lean_object*)&l_Std_Http_Headers_instEncodeV11___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Headers_instEncodeV11___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_instEncodeV11___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Headers_instEncodeV11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Headers_instEncodeV11___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Headers_instEncodeV11___closed__0 = (const lean_object*)&l_Std_Http_Headers_instEncodeV11___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Headers_instEncodeV11 = (const lean_object*)&l_Std_Http_Headers_instEncodeV11___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Headers_instEmptyCollection;
LEAN_EXPORT lean_object* l_Std_Http_Headers_instSingletonProdNameValue___lam__0(lean_object*);
static const lean_closure_object l_Std_Http_Headers_instSingletonProdNameValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Headers_instSingletonProdNameValue___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Headers_instSingletonProdNameValue___closed__0 = (const lean_object*)&l_Std_Http_Headers_instSingletonProdNameValue___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Headers_instSingletonProdNameValue = (const lean_object*)&l_Std_Http_Headers_instSingletonProdNameValue___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Headers_instInsertProdNameValue___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Headers_instInsertProdNameValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Headers_instInsertProdNameValue___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Headers_instInsertProdNameValue___closed__0 = (const lean_object*)&l_Std_Http_Headers_instInsertProdNameValue___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Headers_instInsertProdNameValue = (const lean_object*)&l_Std_Http_Headers_instInsertProdNameValue___closed__0_value;
static const lean_closure_object l_Std_Http_Headers_instUnion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Headers_merge___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Headers_instUnion___closed__0 = (const lean_object*)&l_Std_Http_Headers_instUnion___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Headers_instUnion = (const lean_object*)&l_Std_Http_Headers_instUnion___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Headers_instForInProdNameValueOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_instForInProdNameValueOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_instForInProdNameValueOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_instForInProdNameValueOfMonad(lean_object*, lean_object*);
static lean_object* _init_l_Std_Http_instInhabitedHeaders_default___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_Std_Internal_instInhabitedMultiMap_default___redArg();
return v___x_1_;
}
}
static lean_object* _init_l_Std_Http_instInhabitedHeaders_default(void){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_once(&l_Std_Http_instInhabitedHeaders_default___closed__0, &l_Std_Http_instInhabitedHeaders_default___closed__0_once, _init_l_Std_Http_instInhabitedHeaders_default___closed__0);
return v___x_2_;
}
}
static lean_object* _init_l_Std_Http_instInhabitedHeaders(void){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_obj_once(&l_Std_Http_instInhabitedHeaders_default___closed__0, &l_Std_Http_instInhabitedHeaders_default___closed__0_once, _init_l_Std_Http_instInhabitedHeaders_default___closed__0);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Http_instReprHeaders_repr_spec__1(lean_object* v_a_4_){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = lean_nat_to_int(v_a_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object* v_x_6_, lean_object* v_x_7_, lean_object* v_x_8_){
_start:
{
if (lean_obj_tag(v_x_8_) == 0)
{
lean_dec(v_x_6_);
return v_x_7_;
}
else
{
lean_object* v_head_9_; lean_object* v_tail_10_; lean_object* v___x_12_; uint8_t v_isShared_13_; uint8_t v_isSharedCheck_19_; 
v_head_9_ = lean_ctor_get(v_x_8_, 0);
v_tail_10_ = lean_ctor_get(v_x_8_, 1);
v_isSharedCheck_19_ = !lean_is_exclusive(v_x_8_);
if (v_isSharedCheck_19_ == 0)
{
v___x_12_ = v_x_8_;
v_isShared_13_ = v_isSharedCheck_19_;
goto v_resetjp_11_;
}
else
{
lean_inc(v_tail_10_);
lean_inc(v_head_9_);
lean_dec(v_x_8_);
v___x_12_ = lean_box(0);
v_isShared_13_ = v_isSharedCheck_19_;
goto v_resetjp_11_;
}
v_resetjp_11_:
{
lean_object* v___x_15_; 
lean_inc(v_x_6_);
if (v_isShared_13_ == 0)
{
lean_ctor_set_tag(v___x_12_, 5);
lean_ctor_set(v___x_12_, 1, v_x_6_);
lean_ctor_set(v___x_12_, 0, v_x_7_);
v___x_15_ = v___x_12_;
goto v_reusejp_14_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v_x_7_);
lean_ctor_set(v_reuseFailAlloc_18_, 1, v_x_6_);
v___x_15_ = v_reuseFailAlloc_18_;
goto v_reusejp_14_;
}
v_reusejp_14_:
{
lean_object* v___x_16_; 
v___x_16_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
lean_ctor_set(v___x_16_, 1, v_head_9_);
v_x_7_ = v___x_16_;
v_x_8_ = v_tail_10_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2_spec__3(lean_object* v_x_20_, lean_object* v_x_21_){
_start:
{
if (lean_obj_tag(v_x_20_) == 0)
{
lean_object* v___x_22_; 
lean_dec(v_x_21_);
v___x_22_ = lean_box(0);
return v___x_22_;
}
else
{
lean_object* v_tail_23_; 
v_tail_23_ = lean_ctor_get(v_x_20_, 1);
if (lean_obj_tag(v_tail_23_) == 0)
{
lean_object* v_head_24_; 
lean_dec(v_x_21_);
v_head_24_ = lean_ctor_get(v_x_20_, 0);
lean_inc(v_head_24_);
lean_dec_ref_known(v_x_20_, 2);
return v_head_24_;
}
else
{
lean_object* v_head_25_; lean_object* v___x_26_; 
lean_inc(v_tail_23_);
v_head_25_ = lean_ctor_get(v_x_20_, 0);
lean_inc(v_head_25_);
lean_dec_ref_known(v_x_20_, 2);
v___x_26_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2_spec__3_spec__4(v_x_21_, v_head_25_, v_tail_23_);
return v___x_26_;
}
}
}
}
static lean_object* _init_l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_35_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_36_ = lean_string_length(v___x_35_);
return v___x_36_;
}
}
static lean_object* _init_l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg___closed__6(void){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_37_ = lean_obj_once(&l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg___closed__5, &l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg___closed__5_once, _init_l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg___closed__5);
v___x_38_ = lean_nat_to_int(v___x_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg(lean_object* v_x_43_){
_start:
{
lean_object* v_fst_44_; lean_object* v_snd_45_; lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_67_; 
v_fst_44_ = lean_ctor_get(v_x_43_, 0);
v_snd_45_ = lean_ctor_get(v_x_43_, 1);
v_isSharedCheck_67_ = !lean_is_exclusive(v_x_43_);
if (v_isSharedCheck_67_ == 0)
{
v___x_47_ = v_x_43_;
v_isShared_48_ = v_isSharedCheck_67_;
goto v_resetjp_46_;
}
else
{
lean_inc(v_snd_45_);
lean_inc(v_fst_44_);
lean_dec(v_x_43_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_67_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_52_; 
v___x_49_ = l_Std_Http_Header_instReprName_repr___redArg(v_fst_44_);
v___x_50_ = lean_box(0);
if (v_isShared_48_ == 0)
{
lean_ctor_set_tag(v___x_47_, 1);
lean_ctor_set(v___x_47_, 1, v___x_50_);
lean_ctor_set(v___x_47_, 0, v___x_49_);
v___x_52_ = v___x_47_;
goto v_reusejp_51_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v___x_49_);
lean_ctor_set(v_reuseFailAlloc_66_, 1, v___x_50_);
v___x_52_ = v_reuseFailAlloc_66_;
goto v_reusejp_51_;
}
v_reusejp_51_:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; uint8_t v___x_64_; lean_object* v___x_65_; 
v___x_53_ = l_Std_Http_Header_instReprValue_repr___redArg(v_snd_45_);
v___x_54_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_54_, 0, v___x_53_);
lean_ctor_set(v___x_54_, 1, v___x_52_);
v___x_55_ = l_List_reverse___redArg(v___x_54_);
v___x_56_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg___closed__3));
v___x_57_ = l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2_spec__3(v___x_55_, v___x_56_);
v___x_58_ = lean_obj_once(&l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg___closed__6, &l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg___closed__6_once, _init_l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg___closed__6);
v___x_59_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg___closed__7));
v___x_60_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_60_, 0, v___x_59_);
lean_ctor_set(v___x_60_, 1, v___x_57_);
v___x_61_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg___closed__8));
v___x_62_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_62_, 0, v___x_60_);
lean_ctor_set(v___x_62_, 1, v___x_61_);
v___x_63_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_63_, 0, v___x_58_);
lean_ctor_set(v___x_63_, 1, v___x_62_);
v___x_64_ = 0;
v___x_65_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_65_, 0, v___x_63_);
lean_ctor_set_uint8(v___x_65_, sizeof(void*)*1, v___x_64_);
return v___x_65_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__3_spec__5_spec__7(lean_object* v_x_68_, lean_object* v_x_69_, lean_object* v_x_70_){
_start:
{
if (lean_obj_tag(v_x_70_) == 0)
{
lean_dec(v_x_68_);
return v_x_69_;
}
else
{
lean_object* v_head_71_; lean_object* v_tail_72_; lean_object* v___x_74_; uint8_t v_isShared_75_; uint8_t v_isSharedCheck_82_; 
v_head_71_ = lean_ctor_get(v_x_70_, 0);
v_tail_72_ = lean_ctor_get(v_x_70_, 1);
v_isSharedCheck_82_ = !lean_is_exclusive(v_x_70_);
if (v_isSharedCheck_82_ == 0)
{
v___x_74_ = v_x_70_;
v_isShared_75_ = v_isSharedCheck_82_;
goto v_resetjp_73_;
}
else
{
lean_inc(v_tail_72_);
lean_inc(v_head_71_);
lean_dec(v_x_70_);
v___x_74_ = lean_box(0);
v_isShared_75_ = v_isSharedCheck_82_;
goto v_resetjp_73_;
}
v_resetjp_73_:
{
lean_object* v___x_77_; 
lean_inc(v_x_68_);
if (v_isShared_75_ == 0)
{
lean_ctor_set_tag(v___x_74_, 5);
lean_ctor_set(v___x_74_, 1, v_x_68_);
lean_ctor_set(v___x_74_, 0, v_x_69_);
v___x_77_ = v___x_74_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v_x_69_);
lean_ctor_set(v_reuseFailAlloc_81_, 1, v_x_68_);
v___x_77_ = v_reuseFailAlloc_81_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_78_ = l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg(v_head_71_);
v___x_79_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_79_, 0, v___x_77_);
lean_ctor_set(v___x_79_, 1, v___x_78_);
v_x_69_ = v___x_79_;
v_x_70_ = v_tail_72_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__3_spec__5(lean_object* v_x_83_, lean_object* v_x_84_, lean_object* v_x_85_){
_start:
{
if (lean_obj_tag(v_x_85_) == 0)
{
lean_dec(v_x_83_);
return v_x_84_;
}
else
{
lean_object* v_head_86_; lean_object* v_tail_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_97_; 
v_head_86_ = lean_ctor_get(v_x_85_, 0);
v_tail_87_ = lean_ctor_get(v_x_85_, 1);
v_isSharedCheck_97_ = !lean_is_exclusive(v_x_85_);
if (v_isSharedCheck_97_ == 0)
{
v___x_89_ = v_x_85_;
v_isShared_90_ = v_isSharedCheck_97_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_tail_87_);
lean_inc(v_head_86_);
lean_dec(v_x_85_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_97_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_92_; 
lean_inc(v_x_83_);
if (v_isShared_90_ == 0)
{
lean_ctor_set_tag(v___x_89_, 5);
lean_ctor_set(v___x_89_, 1, v_x_83_);
lean_ctor_set(v___x_89_, 0, v_x_84_);
v___x_92_ = v___x_89_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v_x_84_);
lean_ctor_set(v_reuseFailAlloc_96_, 1, v_x_83_);
v___x_92_ = v_reuseFailAlloc_96_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_93_ = l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg(v_head_86_);
v___x_94_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_94_, 0, v___x_92_);
lean_ctor_set(v___x_94_, 1, v___x_93_);
v___x_95_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__3_spec__5_spec__7(v_x_83_, v___x_94_, v_tail_87_);
return v___x_95_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__3(lean_object* v_x_98_, lean_object* v_x_99_){
_start:
{
if (lean_obj_tag(v_x_98_) == 0)
{
lean_object* v___x_100_; 
lean_dec(v_x_99_);
v___x_100_ = lean_box(0);
return v___x_100_;
}
else
{
lean_object* v_tail_101_; 
v_tail_101_ = lean_ctor_get(v_x_98_, 1);
if (lean_obj_tag(v_tail_101_) == 0)
{
lean_object* v_head_102_; lean_object* v___x_103_; 
lean_dec(v_x_99_);
v_head_102_ = lean_ctor_get(v_x_98_, 0);
lean_inc(v_head_102_);
lean_dec_ref_known(v_x_98_, 2);
v___x_103_ = l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg(v_head_102_);
return v___x_103_;
}
else
{
lean_object* v_head_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
lean_inc(v_tail_101_);
v_head_104_ = lean_ctor_get(v_x_98_, 0);
lean_inc(v_head_104_);
lean_dec_ref_known(v_x_98_, 2);
v___x_105_ = l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg(v_head_104_);
v___x_106_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__3_spec__5(v_x_99_, v___x_105_, v_tail_101_);
return v___x_106_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_109_ = ((lean_object*)(l_Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0___closed__0));
v___x_110_ = lean_string_length(v___x_109_);
return v___x_110_;
}
}
static lean_object* _init_l_Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_111_ = lean_obj_once(&l_Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0___closed__2, &l_Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0___closed__2_once, _init_l_Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0___closed__2);
v___x_112_ = lean_nat_to_int(v___x_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0(lean_object* v_xs_120_){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; uint8_t v___x_123_; 
v___x_121_ = lean_array_get_size(v_xs_120_);
v___x_122_ = lean_unsigned_to_nat(0u);
v___x_123_ = lean_nat_dec_eq(v___x_121_, v___x_122_);
if (v___x_123_ == 0)
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_124_ = lean_array_to_list(v_xs_120_);
v___x_125_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg___closed__3));
v___x_126_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__3(v___x_124_, v___x_125_);
v___x_127_ = lean_obj_once(&l_Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0___closed__3, &l_Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0___closed__3_once, _init_l_Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0___closed__3);
v___x_128_ = ((lean_object*)(l_Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0___closed__4));
v___x_129_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_129_, 0, v___x_128_);
lean_ctor_set(v___x_129_, 1, v___x_126_);
v___x_130_ = ((lean_object*)(l_Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0___closed__5));
v___x_131_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_131_, 0, v___x_129_);
lean_ctor_set(v___x_131_, 1, v___x_130_);
v___x_132_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_132_, 0, v___x_127_);
lean_ctor_set(v___x_132_, 1, v___x_131_);
v___x_133_ = l_Std_Format_fill(v___x_132_);
return v___x_133_;
}
else
{
lean_object* v___x_134_; 
lean_dec_ref(v_xs_120_);
v___x_134_ = ((lean_object*)(l_Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0___closed__7));
return v___x_134_;
}
}
}
static lean_object* _init_l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_148_ = lean_unsigned_to_nat(11u);
v___x_149_ = lean_nat_to_int(v___x_148_);
return v___x_149_;
}
}
static lean_object* _init_l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__9(void){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_151_ = ((lean_object*)(l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__0));
v___x_152_ = lean_string_length(v___x_151_);
return v___x_152_;
}
}
static lean_object* _init_l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__10(void){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = lean_obj_once(&l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__9, &l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__9_once, _init_l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__9);
v___x_154_ = lean_nat_to_int(v___x_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg(lean_object* v_x_159_){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; uint8_t v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_160_ = ((lean_object*)(l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__6));
v___x_161_ = lean_obj_once(&l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__7, &l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__7_once, _init_l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__7);
v___x_162_ = l_Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0(v_x_159_);
v___x_163_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_163_, 0, v___x_161_);
lean_ctor_set(v___x_163_, 1, v___x_162_);
v___x_164_ = 0;
v___x_165_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_165_, 0, v___x_163_);
lean_ctor_set_uint8(v___x_165_, sizeof(void*)*1, v___x_164_);
v___x_166_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_166_, 0, v___x_160_);
lean_ctor_set(v___x_166_, 1, v___x_165_);
v___x_167_ = lean_obj_once(&l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__10, &l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__10_once, _init_l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__10);
v___x_168_ = ((lean_object*)(l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__11));
v___x_169_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_169_, 0, v___x_168_);
lean_ctor_set(v___x_169_, 1, v___x_166_);
v___x_170_ = ((lean_object*)(l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__12));
v___x_171_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_171_, 0, v___x_169_);
lean_ctor_set(v___x_171_, 1, v___x_170_);
v___x_172_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_172_, 0, v___x_167_);
lean_ctor_set(v___x_172_, 1, v___x_171_);
v___x_173_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_173_, 0, v___x_172_);
lean_ctor_set_uint8(v___x_173_, sizeof(void*)*1, v___x_164_);
return v___x_173_;
}
}
static lean_object* _init_l_Std_Http_instReprHeaders_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_183_ = lean_unsigned_to_nat(7u);
v___x_184_ = lean_nat_to_int(v___x_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprHeaders_repr___redArg(lean_object* v_x_185_){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; uint8_t v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_186_ = ((lean_object*)(l_Std_Http_instReprHeaders_repr___redArg___closed__3));
v___x_187_ = lean_obj_once(&l_Std_Http_instReprHeaders_repr___redArg___closed__4, &l_Std_Http_instReprHeaders_repr___redArg___closed__4_once, _init_l_Std_Http_instReprHeaders_repr___redArg___closed__4);
v___x_188_ = l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg(v_x_185_);
v___x_189_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_189_, 0, v___x_187_);
lean_ctor_set(v___x_189_, 1, v___x_188_);
v___x_190_ = 0;
v___x_191_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_191_, 0, v___x_189_);
lean_ctor_set_uint8(v___x_191_, sizeof(void*)*1, v___x_190_);
v___x_192_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_186_);
lean_ctor_set(v___x_192_, 1, v___x_191_);
v___x_193_ = lean_obj_once(&l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__10, &l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__10_once, _init_l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__10);
v___x_194_ = ((lean_object*)(l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__11));
v___x_195_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
lean_ctor_set(v___x_195_, 1, v___x_192_);
v___x_196_ = ((lean_object*)(l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__12));
v___x_197_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_197_, 0, v___x_195_);
lean_ctor_set(v___x_197_, 1, v___x_196_);
v___x_198_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_198_, 0, v___x_193_);
lean_ctor_set(v___x_198_, 1, v___x_197_);
v___x_199_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_199_, 0, v___x_198_);
lean_ctor_set_uint8(v___x_199_, sizeof(void*)*1, v___x_190_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprHeaders_repr(lean_object* v_x_200_, lean_object* v_prec_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l_Std_Http_instReprHeaders_repr___redArg(v_x_200_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprHeaders_repr___boxed(lean_object* v_x_203_, lean_object* v_prec_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Std_Http_instReprHeaders_repr(v_x_203_, v_prec_204_);
lean_dec(v_prec_204_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0(lean_object* v_x_206_, lean_object* v_prec_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg(v_x_206_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___boxed(lean_object* v_x_209_, lean_object* v_prec_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0(v_x_209_, v_prec_210_);
lean_dec(v_prec_210_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2(lean_object* v_x_212_, lean_object* v_x_213_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg(v_x_212_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___boxed(lean_object* v_x_215_, lean_object* v_x_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2(v_x_215_, v_x_216_);
lean_dec(v_x_216_);
return v_res_217_;
}
}
static lean_object* _init_l_Std_Http_instMembershipNameHeaders(void){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = lean_box(0);
return v___x_220_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_instDecidableMemNameHeaders(lean_object* v_name_222_, lean_object* v_h_223_){
_start:
{
lean_object* v___f_224_; uint8_t v___x_225_; 
v___f_224_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___x_225_ = l_Std_Internal_MultiMap_instDecidableMem___redArg(v___f_224_, v_name_222_, v_h_223_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instDecidableMemNameHeaders___boxed(lean_object* v_name_226_, lean_object* v_h_227_){
_start:
{
uint8_t v_res_228_; lean_object* v_r_229_; 
v_res_228_ = l_Std_Http_instDecidableMemNameHeaders(v_name_226_, v_h_227_);
v_r_229_ = lean_box(v_res_228_);
return v_r_229_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_get___redArg(lean_object* v_headers_230_, lean_object* v_name_231_){
_start:
{
lean_object* v___f_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v_snd_236_; 
v___f_232_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___x_233_ = lean_unsigned_to_nat(0u);
v___x_234_ = l_Std_Internal_MultiMap_findIdxFrom___redArg(v___f_232_, v_headers_230_, v_name_231_, v___x_233_);
v___x_235_ = lean_array_fget_borrowed(v_headers_230_, v___x_234_);
lean_dec(v___x_234_);
v_snd_236_ = lean_ctor_get(v___x_235_, 1);
lean_inc(v_snd_236_);
return v_snd_236_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_get___redArg___boxed(lean_object* v_headers_237_, lean_object* v_name_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Std_Http_Headers_get___redArg(v_headers_237_, v_name_238_);
lean_dec_ref(v_headers_237_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_get(lean_object* v_headers_240_, lean_object* v_name_241_, lean_object* v_h_242_){
_start:
{
lean_object* v___f_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v_snd_247_; 
v___f_243_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___x_244_ = lean_unsigned_to_nat(0u);
v___x_245_ = l_Std_Internal_MultiMap_findIdxFrom___redArg(v___f_243_, v_headers_240_, v_name_241_, v___x_244_);
v___x_246_ = lean_array_fget_borrowed(v_headers_240_, v___x_245_);
lean_dec(v___x_245_);
v_snd_247_ = lean_ctor_get(v___x_246_, 1);
lean_inc(v_snd_247_);
return v_snd_247_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_get___boxed(lean_object* v_headers_248_, lean_object* v_name_249_, lean_object* v_h_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Std_Http_Headers_get(v_headers_248_, v_name_249_, v_h_250_);
lean_dec_ref(v_headers_248_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_getAll___redArg___lam__0(lean_object* v_name_252_, lean_object* v_x1_253_, lean_object* v_x2_254_){
_start:
{
lean_object* v_fst_255_; lean_object* v_snd_256_; uint8_t v___x_257_; 
v_fst_255_ = lean_ctor_get(v_x2_254_, 0);
lean_inc(v_fst_255_);
v_snd_256_ = lean_ctor_get(v_x2_254_, 1);
lean_inc(v_snd_256_);
lean_dec_ref(v_x2_254_);
v___x_257_ = lean_string_dec_eq(v_fst_255_, v_name_252_);
lean_dec(v_fst_255_);
if (v___x_257_ == 0)
{
lean_dec(v_snd_256_);
return v_x1_253_;
}
else
{
lean_object* v___x_258_; 
v___x_258_ = lean_array_push(v_x1_253_, v_snd_256_);
return v___x_258_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_getAll___redArg___lam__0___boxed(lean_object* v_name_259_, lean_object* v_x1_260_, lean_object* v_x2_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Std_Http_Headers_getAll___redArg___lam__0(v_name_259_, v_x1_260_, v_x2_261_);
lean_dec_ref(v_name_259_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_getAll___redArg(lean_object* v_headers_284_, lean_object* v_name_285_){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; uint8_t v___x_290_; 
v___x_286_ = lean_unsigned_to_nat(0u);
v___x_287_ = ((lean_object*)(l_Std_Http_Headers_getAll___redArg___closed__0));
v___x_288_ = lean_array_get_size(v_headers_284_);
v___x_289_ = ((lean_object*)(l_Std_Http_Headers_getAll___redArg___closed__10));
v___x_290_ = lean_nat_dec_lt(v___x_286_, v___x_288_);
if (v___x_290_ == 0)
{
lean_dec_ref(v_name_285_);
lean_dec_ref(v_headers_284_);
return v___x_287_;
}
else
{
lean_object* v___f_291_; size_t v___x_292_; size_t v___x_293_; lean_object* v___x_294_; 
v___f_291_ = lean_alloc_closure((void*)(l_Std_Http_Headers_getAll___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_291_, 0, v_name_285_);
v___x_292_ = ((size_t)0ULL);
v___x_293_ = lean_usize_of_nat(v___x_288_);
v___x_294_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_289_, v___f_291_, v_headers_284_, v___x_292_, v___x_293_, v___x_287_);
return v___x_294_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_getAll(lean_object* v_headers_295_, lean_object* v_name_296_, lean_object* v_h_297_){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; uint8_t v___x_302_; 
v___x_298_ = lean_unsigned_to_nat(0u);
v___x_299_ = ((lean_object*)(l_Std_Http_Headers_getAll___redArg___closed__0));
v___x_300_ = lean_array_get_size(v_headers_295_);
v___x_301_ = ((lean_object*)(l_Std_Http_Headers_getAll___redArg___closed__10));
v___x_302_ = lean_nat_dec_lt(v___x_298_, v___x_300_);
if (v___x_302_ == 0)
{
lean_dec_ref(v_name_296_);
lean_dec_ref(v_headers_295_);
return v___x_299_;
}
else
{
lean_object* v___f_303_; size_t v___x_304_; size_t v___x_305_; lean_object* v___x_306_; 
v___f_303_ = lean_alloc_closure((void*)(l_Std_Http_Headers_getAll___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_303_, 0, v_name_296_);
v___x_304_ = ((size_t)0ULL);
v___x_305_ = lean_usize_of_nat(v___x_300_);
v___x_306_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_301_, v___f_303_, v_headers_295_, v___x_304_, v___x_305_, v___x_299_);
return v___x_306_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_getAll_x3f(lean_object* v_headers_307_, lean_object* v_name_308_){
_start:
{
lean_object* v___y_310_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; uint8_t v___x_320_; 
v___x_316_ = lean_unsigned_to_nat(0u);
v___x_317_ = ((lean_object*)(l_Std_Http_Headers_getAll___redArg___closed__0));
v___x_318_ = lean_array_get_size(v_headers_307_);
v___x_319_ = ((lean_object*)(l_Std_Http_Headers_getAll___redArg___closed__10));
v___x_320_ = lean_nat_dec_lt(v___x_316_, v___x_318_);
if (v___x_320_ == 0)
{
lean_dec_ref(v_name_308_);
lean_dec_ref(v_headers_307_);
v___y_310_ = v___x_317_;
goto v___jp_309_;
}
else
{
lean_object* v___f_321_; size_t v___x_322_; size_t v___x_323_; lean_object* v___x_324_; 
v___f_321_ = lean_alloc_closure((void*)(l_Std_Http_Headers_getAll___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_321_, 0, v_name_308_);
v___x_322_ = ((size_t)0ULL);
v___x_323_ = lean_usize_of_nat(v___x_318_);
v___x_324_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_319_, v___f_321_, v_headers_307_, v___x_322_, v___x_323_, v___x_317_);
v___y_310_ = v___x_324_;
goto v___jp_309_;
}
v___jp_309_:
{
lean_object* v___x_311_; lean_object* v___x_312_; uint8_t v___x_313_; 
v___x_311_ = lean_array_get_size(v___y_310_);
v___x_312_ = lean_unsigned_to_nat(0u);
v___x_313_ = lean_nat_dec_eq(v___x_311_, v___x_312_);
if (v___x_313_ == 0)
{
lean_object* v___x_314_; 
v___x_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_314_, 0, v___y_310_);
return v___x_314_;
}
else
{
lean_object* v___x_315_; 
lean_dec_ref(v___y_310_);
v___x_315_ = lean_box(0);
return v___x_315_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_get_x3f(lean_object* v_headers_325_, lean_object* v_name_326_){
_start:
{
lean_object* v___f_327_; lean_object* v___x_328_; lean_object* v_i_329_; lean_object* v___x_330_; uint8_t v___x_331_; 
v___f_327_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___x_328_ = lean_unsigned_to_nat(0u);
v_i_329_ = l_Std_Internal_MultiMap_findIdxFrom___redArg(v___f_327_, v_headers_325_, v_name_326_, v___x_328_);
v___x_330_ = lean_array_get_size(v_headers_325_);
v___x_331_ = lean_nat_dec_lt(v_i_329_, v___x_330_);
if (v___x_331_ == 0)
{
lean_object* v___x_332_; 
lean_dec(v_i_329_);
v___x_332_ = lean_box(0);
return v___x_332_;
}
else
{
lean_object* v___x_333_; lean_object* v_snd_334_; lean_object* v___x_335_; 
v___x_333_ = lean_array_fget_borrowed(v_headers_325_, v_i_329_);
lean_dec(v_i_329_);
v_snd_334_ = lean_ctor_get(v___x_333_, 1);
lean_inc(v_snd_334_);
v___x_335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_335_, 0, v_snd_334_);
return v___x_335_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_get_x3f___boxed(lean_object* v_headers_336_, lean_object* v_name_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Std_Http_Headers_get_x3f(v_headers_336_, v_name_337_);
lean_dec_ref(v_headers_336_);
return v_res_338_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Headers_hasEntry___lam__0(lean_object* v_name_339_, lean_object* v_value_340_, lean_object* v_x_341_){
_start:
{
lean_object* v_fst_342_; lean_object* v_snd_343_; uint8_t v___x_344_; 
v_fst_342_ = lean_ctor_get(v_x_341_, 0);
v_snd_343_ = lean_ctor_get(v_x_341_, 1);
v___x_344_ = lean_string_dec_eq(v_fst_342_, v_name_339_);
if (v___x_344_ == 0)
{
return v___x_344_;
}
else
{
uint8_t v___x_345_; 
v___x_345_ = l_Std_Http_Header_instBEqValue_beq(v_snd_343_, v_value_340_);
return v___x_345_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_hasEntry___lam__0___boxed(lean_object* v_name_346_, lean_object* v_value_347_, lean_object* v_x_348_){
_start:
{
uint8_t v_res_349_; lean_object* v_r_350_; 
v_res_349_ = l_Std_Http_Headers_hasEntry___lam__0(v_name_346_, v_value_347_, v_x_348_);
lean_dec_ref(v_x_348_);
lean_dec_ref(v_value_347_);
lean_dec_ref(v_name_346_);
v_r_350_ = lean_box(v_res_349_);
return v_r_350_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Headers_hasEntry(lean_object* v_headers_351_, lean_object* v_name_352_, lean_object* v_value_353_){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; uint8_t v___x_357_; 
v___x_354_ = lean_unsigned_to_nat(0u);
v___x_355_ = lean_array_get_size(v_headers_351_);
v___x_356_ = ((lean_object*)(l_Std_Http_Headers_getAll___redArg___closed__10));
v___x_357_ = lean_nat_dec_lt(v___x_354_, v___x_355_);
if (v___x_357_ == 0)
{
lean_dec_ref(v_value_353_);
lean_dec_ref(v_name_352_);
lean_dec_ref(v_headers_351_);
return v___x_357_;
}
else
{
lean_object* v___f_358_; size_t v___x_359_; size_t v___x_360_; lean_object* v___x_361_; uint8_t v___x_362_; 
v___f_358_ = lean_alloc_closure((void*)(l_Std_Http_Headers_hasEntry___lam__0___boxed), 3, 2);
lean_closure_set(v___f_358_, 0, v_name_352_);
lean_closure_set(v___f_358_, 1, v_value_353_);
v___x_359_ = ((size_t)0ULL);
v___x_360_ = lean_usize_of_nat(v___x_355_);
v___x_361_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_356_, v___f_358_, v_headers_351_, v___x_359_, v___x_360_);
v___x_362_ = lean_unbox(v___x_361_);
lean_dec(v___x_361_);
return v___x_362_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_hasEntry___boxed(lean_object* v_headers_363_, lean_object* v_name_364_, lean_object* v_value_365_){
_start:
{
uint8_t v_res_366_; lean_object* v_r_367_; 
v_res_366_ = l_Std_Http_Headers_hasEntry(v_headers_363_, v_name_364_, v_value_365_);
v_r_367_ = lean_box(v_res_366_);
return v_r_367_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_getLast_x3f(lean_object* v_headers_368_, lean_object* v_name_369_){
_start:
{
lean_object* v___f_370_; lean_object* v___x_371_; lean_object* v_i_372_; uint8_t v___x_373_; 
v___f_370_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___x_371_ = lean_array_get_size(v_headers_368_);
v_i_372_ = l_Std_Internal_MultiMap_findLastIdxBelow___redArg(v___f_370_, v_headers_368_, v_name_369_, v___x_371_);
v___x_373_ = lean_nat_dec_lt(v_i_372_, v___x_371_);
if (v___x_373_ == 0)
{
lean_object* v___x_374_; 
lean_dec(v_i_372_);
v___x_374_ = lean_box(0);
return v___x_374_;
}
else
{
lean_object* v___x_375_; lean_object* v_snd_376_; lean_object* v___x_377_; 
v___x_375_ = lean_array_fget_borrowed(v_headers_368_, v_i_372_);
lean_dec(v_i_372_);
v_snd_376_ = lean_ctor_get(v___x_375_, 1);
lean_inc(v_snd_376_);
v___x_377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_377_, 0, v_snd_376_);
return v___x_377_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_getLast_x3f___boxed(lean_object* v_headers_378_, lean_object* v_name_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Std_Http_Headers_getLast_x3f(v_headers_378_, v_name_379_);
lean_dec_ref(v_headers_378_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_getD(lean_object* v_headers_381_, lean_object* v_name_382_, lean_object* v_d_383_){
_start:
{
lean_object* v___f_384_; lean_object* v___x_385_; lean_object* v_i_386_; lean_object* v___x_387_; uint8_t v___x_388_; 
v___f_384_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___x_385_ = lean_unsigned_to_nat(0u);
v_i_386_ = l_Std_Internal_MultiMap_findIdxFrom___redArg(v___f_384_, v_headers_381_, v_name_382_, v___x_385_);
v___x_387_ = lean_array_get_size(v_headers_381_);
v___x_388_ = lean_nat_dec_lt(v_i_386_, v___x_387_);
if (v___x_388_ == 0)
{
lean_dec(v_i_386_);
lean_inc_ref(v_d_383_);
return v_d_383_;
}
else
{
lean_object* v___x_389_; lean_object* v_snd_390_; 
v___x_389_ = lean_array_fget_borrowed(v_headers_381_, v_i_386_);
lean_dec(v_i_386_);
v_snd_390_ = lean_ctor_get(v___x_389_, 1);
lean_inc(v_snd_390_);
return v_snd_390_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_getD___boxed(lean_object* v_headers_391_, lean_object* v_name_392_, lean_object* v_d_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Std_Http_Headers_getD(v_headers_391_, v_name_392_, v_d_393_);
lean_dec_ref(v_d_393_);
lean_dec_ref(v_headers_391_);
return v_res_394_;
}
}
static lean_object* _init_l_Std_Http_Headers_get_x21___closed__4(void){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_399_ = ((lean_object*)(l_Std_Http_Headers_get_x21___closed__3));
v___x_400_ = lean_unsigned_to_nat(14u);
v___x_401_ = lean_unsigned_to_nat(22u);
v___x_402_ = ((lean_object*)(l_Std_Http_Headers_get_x21___closed__2));
v___x_403_ = ((lean_object*)(l_Std_Http_Headers_get_x21___closed__1));
v___x_404_ = l_mkPanicMessageWithDecl(v___x_403_, v___x_402_, v___x_401_, v___x_400_, v___x_399_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_get_x21(lean_object* v_headers_405_, lean_object* v_name_406_){
_start:
{
lean_object* v___f_407_; lean_object* v___x_408_; lean_object* v_i_409_; lean_object* v___x_410_; uint8_t v___x_411_; 
v___f_407_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___x_408_ = lean_unsigned_to_nat(0u);
v_i_409_ = l_Std_Internal_MultiMap_findIdxFrom___redArg(v___f_407_, v_headers_405_, v_name_406_, v___x_408_);
v___x_410_ = lean_array_get_size(v_headers_405_);
v___x_411_ = lean_nat_dec_lt(v_i_409_, v___x_410_);
if (v___x_411_ == 0)
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
lean_dec(v_i_409_);
v___x_412_ = ((lean_object*)(l_Std_Http_Headers_get_x21___closed__0));
v___x_413_ = lean_obj_once(&l_Std_Http_Headers_get_x21___closed__4, &l_Std_Http_Headers_get_x21___closed__4_once, _init_l_Std_Http_Headers_get_x21___closed__4);
v___x_414_ = l_panic___redArg(v___x_412_, v___x_413_);
return v___x_414_;
}
else
{
lean_object* v___x_415_; lean_object* v_snd_416_; 
v___x_415_ = lean_array_fget_borrowed(v_headers_405_, v_i_409_);
lean_dec(v_i_409_);
v_snd_416_ = lean_ctor_get(v___x_415_, 1);
lean_inc(v_snd_416_);
return v_snd_416_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_get_x21___boxed(lean_object* v_headers_417_, lean_object* v_name_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Std_Http_Headers_get_x21(v_headers_417_, v_name_418_);
lean_dec_ref(v_headers_417_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_insert(lean_object* v_headers_420_, lean_object* v_key_421_, lean_object* v_value_422_){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_423_, 0, v_key_421_);
lean_ctor_set(v___x_423_, 1, v_value_422_);
v___x_424_ = lean_array_push(v_headers_420_, v___x_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_insert_x21(lean_object* v_headers_425_, lean_object* v_name_426_, lean_object* v_value_427_){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_428_ = l_Std_Http_Header_Name_ofString_x21(v_name_426_);
v___x_429_ = l_Std_Http_Header_Value_ofString_x21(v_value_427_);
v___x_430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_430_, 0, v___x_428_);
lean_ctor_set(v___x_430_, 1, v___x_429_);
v___x_431_ = lean_array_push(v_headers_425_, v___x_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_insert_x3f(lean_object* v_headers_432_, lean_object* v_name_433_, lean_object* v_value_434_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l_Std_Http_Header_Name_ofString_x3f(v_name_433_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v___x_436_; 
lean_dec_ref(v_value_434_);
lean_dec_ref(v_headers_432_);
v___x_436_ = lean_box(0);
return v___x_436_;
}
else
{
lean_object* v_val_437_; lean_object* v___x_438_; 
v_val_437_ = lean_ctor_get(v___x_435_, 0);
lean_inc(v_val_437_);
lean_dec_ref_known(v___x_435_, 1);
v___x_438_ = l_Std_Http_Header_Value_ofString_x3f(v_value_434_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v___x_439_; 
lean_dec(v_val_437_);
lean_dec_ref(v_headers_432_);
v___x_439_ = lean_box(0);
return v___x_439_;
}
else
{
lean_object* v_val_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_449_; 
v_val_440_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_449_ == 0)
{
v___x_442_ = v___x_438_;
v_isShared_443_ = v_isSharedCheck_449_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_val_440_);
lean_dec(v___x_438_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_449_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_447_; 
v___x_444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_444_, 0, v_val_437_);
lean_ctor_set(v___x_444_, 1, v_val_440_);
v___x_445_ = lean_array_push(v_headers_432_, v___x_444_);
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 0, v___x_445_);
v___x_447_ = v___x_442_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v___x_445_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_insertMany___lam__0(lean_object* v_key_450_, lean_object* v_x1_451_, lean_object* v_x2_452_){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_453_, 0, v_key_450_);
lean_ctor_set(v___x_453_, 1, v_x2_452_);
v___x_454_ = lean_array_push(v_x1_451_, v___x_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_insertMany(lean_object* v_headers_455_, lean_object* v_key_456_, lean_object* v_values_457_){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; uint8_t v___x_461_; 
v___x_458_ = lean_unsigned_to_nat(0u);
v___x_459_ = lean_array_get_size(v_values_457_);
v___x_460_ = ((lean_object*)(l_Std_Http_Headers_getAll___redArg___closed__10));
v___x_461_ = lean_nat_dec_lt(v___x_458_, v___x_459_);
if (v___x_461_ == 0)
{
lean_dec_ref(v_values_457_);
lean_dec_ref(v_key_456_);
return v_headers_455_;
}
else
{
lean_object* v___f_462_; size_t v___x_463_; size_t v___x_464_; lean_object* v___x_465_; 
v___f_462_ = lean_alloc_closure((void*)(l_Std_Http_Headers_insertMany___lam__0), 3, 1);
lean_closure_set(v___f_462_, 0, v_key_456_);
v___x_463_ = ((size_t)0ULL);
v___x_464_ = lean_usize_of_nat(v___x_459_);
v___x_465_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_460_, v___f_462_, v_values_457_, v___x_463_, v___x_464_, v_headers_455_);
return v___x_465_;
}
}
}
static lean_object* _init_l_Std_Http_Headers_empty___closed__0(void){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = l_Std_Internal_MultiMap_empty___redArg();
return v___x_466_;
}
}
static lean_object* _init_l_Std_Http_Headers_empty(void){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = lean_obj_once(&l_Std_Http_Headers_empty___closed__0, &l_Std_Http_Headers_empty___closed__0_once, _init_l_Std_Http_Headers_empty___closed__0);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_ofList(lean_object* v_pairs_468_){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = lean_array_mk(v_pairs_468_);
return v___x_469_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Headers_contains___lam__0(lean_object* v_name_470_, lean_object* v_x_471_){
_start:
{
lean_object* v_fst_472_; uint8_t v___x_473_; 
v_fst_472_ = lean_ctor_get(v_x_471_, 0);
v___x_473_ = lean_string_dec_eq(v_fst_472_, v_name_470_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_contains___lam__0___boxed(lean_object* v_name_474_, lean_object* v_x_475_){
_start:
{
uint8_t v_res_476_; lean_object* v_r_477_; 
v_res_476_ = l_Std_Http_Headers_contains___lam__0(v_name_474_, v_x_475_);
lean_dec_ref(v_x_475_);
lean_dec_ref(v_name_474_);
v_r_477_ = lean_box(v_res_476_);
return v_r_477_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Headers_contains(lean_object* v_headers_478_, lean_object* v_name_479_){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; uint8_t v___x_483_; 
v___x_480_ = lean_unsigned_to_nat(0u);
v___x_481_ = lean_array_get_size(v_headers_478_);
v___x_482_ = ((lean_object*)(l_Std_Http_Headers_getAll___redArg___closed__10));
v___x_483_ = lean_nat_dec_lt(v___x_480_, v___x_481_);
if (v___x_483_ == 0)
{
lean_dec_ref(v_name_479_);
lean_dec_ref(v_headers_478_);
return v___x_483_;
}
else
{
lean_object* v___f_484_; size_t v___x_485_; size_t v___x_486_; lean_object* v___x_487_; uint8_t v___x_488_; 
v___f_484_ = lean_alloc_closure((void*)(l_Std_Http_Headers_contains___lam__0___boxed), 2, 1);
lean_closure_set(v___f_484_, 0, v_name_479_);
v___x_485_ = ((size_t)0ULL);
v___x_486_ = lean_usize_of_nat(v___x_481_);
v___x_487_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_482_, v___f_484_, v_headers_478_, v___x_485_, v___x_486_);
v___x_488_ = lean_unbox(v___x_487_);
lean_dec(v___x_487_);
return v___x_488_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_contains___boxed(lean_object* v_headers_489_, lean_object* v_name_490_){
_start:
{
uint8_t v_res_491_; lean_object* v_r_492_; 
v_res_491_ = l_Std_Http_Headers_contains(v_headers_489_, v_name_490_);
v_r_492_ = lean_box(v_res_491_);
return v_r_492_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_erase___lam__1(lean_object* v_name_493_, lean_object* v_x1_494_, lean_object* v_x2_495_){
_start:
{
lean_object* v_fst_496_; uint8_t v___x_497_; 
v_fst_496_ = lean_ctor_get(v_x2_495_, 0);
v___x_497_ = lean_string_dec_eq(v_fst_496_, v_name_493_);
if (v___x_497_ == 0)
{
lean_object* v___x_498_; 
v___x_498_ = lean_array_push(v_x1_494_, v_x2_495_);
return v___x_498_;
}
else
{
lean_dec_ref(v_x2_495_);
return v_x1_494_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_erase___lam__1___boxed(lean_object* v_name_499_, lean_object* v_x1_500_, lean_object* v_x2_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_Std_Http_Headers_erase___lam__1(v_name_499_, v_x1_500_, v_x2_501_);
lean_dec_ref(v_name_499_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_erase(lean_object* v_headers_505_, lean_object* v_name_506_){
_start:
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; uint8_t v___x_510_; 
v___x_507_ = lean_unsigned_to_nat(0u);
v___x_508_ = lean_array_get_size(v_headers_505_);
v___x_509_ = ((lean_object*)(l_Std_Http_Headers_getAll___redArg___closed__10));
v___x_510_ = lean_nat_dec_lt(v___x_507_, v___x_508_);
if (v___x_510_ == 0)
{
lean_dec_ref(v_name_506_);
return v_headers_505_;
}
else
{
lean_object* v___f_511_; size_t v___x_512_; size_t v___x_513_; lean_object* v___x_514_; uint8_t v___x_515_; 
lean_inc_ref(v_name_506_);
v___f_511_ = lean_alloc_closure((void*)(l_Std_Http_Headers_contains___lam__0___boxed), 2, 1);
lean_closure_set(v___f_511_, 0, v_name_506_);
v___x_512_ = ((size_t)0ULL);
v___x_513_ = lean_usize_of_nat(v___x_508_);
lean_inc_ref(v_headers_505_);
v___x_514_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_509_, v___f_511_, v_headers_505_, v___x_512_, v___x_513_);
v___x_515_ = lean_unbox(v___x_514_);
lean_dec(v___x_514_);
if (v___x_515_ == 0)
{
lean_dec_ref(v_name_506_);
return v_headers_505_;
}
else
{
lean_object* v___f_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v___f_516_ = lean_alloc_closure((void*)(l_Std_Http_Headers_erase___lam__1___boxed), 3, 1);
lean_closure_set(v___f_516_, 0, v_name_506_);
v___x_517_ = ((lean_object*)(l_Std_Http_Headers_erase___closed__0));
v___x_518_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_509_, v___f_516_, v_headers_505_, v___x_512_, v___x_513_, v___x_517_);
return v___x_518_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_Http_Headers_eraseMany___lam__0(lean_object* v___f_519_, lean_object* v_names_520_, lean_object* v_x_521_){
_start:
{
lean_object* v_fst_522_; uint8_t v___x_523_; 
v_fst_522_ = lean_ctor_get(v_x_521_, 0);
lean_inc(v_fst_522_);
lean_dec_ref(v_x_521_);
v___x_523_ = l_Array_contains___redArg(v___f_519_, v_names_520_, v_fst_522_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_eraseMany___lam__0___boxed(lean_object* v___f_524_, lean_object* v_names_525_, lean_object* v_x_526_){
_start:
{
uint8_t v_res_527_; lean_object* v_r_528_; 
v_res_527_ = l_Std_Http_Headers_eraseMany___lam__0(v___f_524_, v_names_525_, v_x_526_);
v_r_528_ = lean_box(v_res_527_);
return v_r_528_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_eraseMany___lam__1(lean_object* v___f_529_, lean_object* v_names_530_, lean_object* v_x1_531_, lean_object* v_x2_532_){
_start:
{
lean_object* v_fst_533_; uint8_t v___x_534_; 
v_fst_533_ = lean_ctor_get(v_x2_532_, 0);
lean_inc(v_fst_533_);
v___x_534_ = l_Array_contains___redArg(v___f_529_, v_names_530_, v_fst_533_);
if (v___x_534_ == 0)
{
lean_object* v___x_535_; 
v___x_535_ = lean_array_push(v_x1_531_, v_x2_532_);
return v___x_535_;
}
else
{
lean_dec_ref(v_x2_532_);
return v_x1_531_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_eraseMany(lean_object* v_headers_536_, lean_object* v_names_537_){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; uint8_t v___x_541_; 
v___x_538_ = lean_unsigned_to_nat(0u);
v___x_539_ = lean_array_get_size(v_headers_536_);
v___x_540_ = ((lean_object*)(l_Std_Http_Headers_getAll___redArg___closed__10));
v___x_541_ = lean_nat_dec_lt(v___x_538_, v___x_539_);
if (v___x_541_ == 0)
{
lean_dec_ref(v_names_537_);
return v_headers_536_;
}
else
{
lean_object* v___f_542_; lean_object* v___f_543_; size_t v___x_544_; size_t v___x_545_; lean_object* v___x_546_; uint8_t v___x_547_; 
v___f_542_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
lean_inc_ref(v_names_537_);
v___f_543_ = lean_alloc_closure((void*)(l_Std_Http_Headers_eraseMany___lam__0___boxed), 3, 2);
lean_closure_set(v___f_543_, 0, v___f_542_);
lean_closure_set(v___f_543_, 1, v_names_537_);
v___x_544_ = ((size_t)0ULL);
v___x_545_ = lean_usize_of_nat(v___x_539_);
lean_inc_ref(v_headers_536_);
v___x_546_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_540_, v___f_543_, v_headers_536_, v___x_544_, v___x_545_);
v___x_547_ = lean_unbox(v___x_546_);
lean_dec(v___x_546_);
if (v___x_547_ == 0)
{
lean_dec_ref(v_names_537_);
return v_headers_536_;
}
else
{
lean_object* v___f_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v___f_548_ = lean_alloc_closure((void*)(l_Std_Http_Headers_eraseMany___lam__1), 4, 2);
lean_closure_set(v___f_548_, 0, v___f_542_);
lean_closure_set(v___f_548_, 1, v_names_537_);
v___x_549_ = ((lean_object*)(l_Std_Http_Headers_erase___closed__0));
v___x_550_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_540_, v___f_548_, v_headers_536_, v___x_544_, v___x_545_, v___x_549_);
return v___x_550_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_size(lean_object* v_headers_551_){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = lean_array_get_size(v_headers_551_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_size___boxed(lean_object* v_headers_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Std_Http_Headers_size(v_headers_553_);
lean_dec_ref(v_headers_553_);
return v_res_554_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Headers_isEmpty(lean_object* v_headers_555_){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; uint8_t v___x_558_; 
v___x_556_ = lean_array_get_size(v_headers_555_);
v___x_557_ = lean_unsigned_to_nat(0u);
v___x_558_ = lean_nat_dec_eq(v___x_556_, v___x_557_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_isEmpty___boxed(lean_object* v_headers_559_){
_start:
{
uint8_t v_res_560_; lean_object* v_r_561_; 
v_res_560_ = l_Std_Http_Headers_isEmpty(v_headers_559_);
lean_dec_ref(v_headers_559_);
v_r_561_ = lean_box(v_res_560_);
return v_r_561_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_merge(lean_object* v_headers1_562_, lean_object* v_headers2_563_){
_start:
{
lean_object* v___x_564_; 
v___x_564_ = l_Array_append___redArg(v_headers1_562_, v_headers2_563_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_merge___boxed(lean_object* v_headers1_565_, lean_object* v_headers2_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Std_Http_Headers_merge(v_headers1_565_, v_headers2_566_);
lean_dec_ref(v_headers2_566_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_toList(lean_object* v_headers_568_){
_start:
{
lean_object* v___x_569_; 
v___x_569_ = lean_array_to_list(v_headers_568_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_toArray(lean_object* v_headers_570_){
_start:
{
lean_inc_ref(v_headers_570_);
return v_headers_570_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_toArray___boxed(lean_object* v_headers_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Std_Http_Headers_toArray(v_headers_571_);
lean_dec_ref(v_headers_571_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___redArg(lean_object* v_f_573_, lean_object* v_as_574_, size_t v_i_575_, size_t v_stop_576_, lean_object* v_b_577_){
_start:
{
uint8_t v___x_578_; 
v___x_578_ = lean_usize_dec_eq(v_i_575_, v_stop_576_);
if (v___x_578_ == 0)
{
lean_object* v___x_579_; lean_object* v_fst_580_; lean_object* v_snd_581_; lean_object* v___x_582_; size_t v___x_583_; size_t v___x_584_; 
v___x_579_ = lean_array_uget_borrowed(v_as_574_, v_i_575_);
v_fst_580_ = lean_ctor_get(v___x_579_, 0);
v_snd_581_ = lean_ctor_get(v___x_579_, 1);
lean_inc(v_f_573_);
lean_inc(v_snd_581_);
lean_inc(v_fst_580_);
v___x_582_ = lean_apply_3(v_f_573_, v_b_577_, v_fst_580_, v_snd_581_);
v___x_583_ = ((size_t)1ULL);
v___x_584_ = lean_usize_add(v_i_575_, v___x_583_);
v_i_575_ = v___x_584_;
v_b_577_ = v___x_582_;
goto _start;
}
else
{
lean_dec(v_f_573_);
return v_b_577_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___redArg___boxed(lean_object* v_f_586_, lean_object* v_as_587_, lean_object* v_i_588_, lean_object* v_stop_589_, lean_object* v_b_590_){
_start:
{
size_t v_i_boxed_591_; size_t v_stop_boxed_592_; lean_object* v_res_593_; 
v_i_boxed_591_ = lean_unbox_usize(v_i_588_);
lean_dec(v_i_588_);
v_stop_boxed_592_ = lean_unbox_usize(v_stop_589_);
lean_dec(v_stop_589_);
v_res_593_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___redArg(v_f_586_, v_as_587_, v_i_boxed_591_, v_stop_boxed_592_, v_b_590_);
lean_dec_ref(v_as_587_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_fold___redArg(lean_object* v_headers_594_, lean_object* v_init_595_, lean_object* v_f_596_){
_start:
{
lean_object* v___x_597_; lean_object* v___x_598_; uint8_t v___x_599_; 
v___x_597_ = lean_unsigned_to_nat(0u);
v___x_598_ = lean_array_get_size(v_headers_594_);
v___x_599_ = lean_nat_dec_lt(v___x_597_, v___x_598_);
if (v___x_599_ == 0)
{
lean_dec(v_f_596_);
return v_init_595_;
}
else
{
size_t v___x_600_; size_t v___x_601_; lean_object* v___x_602_; 
v___x_600_ = ((size_t)0ULL);
v___x_601_ = lean_usize_of_nat(v___x_598_);
v___x_602_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___redArg(v_f_596_, v_headers_594_, v___x_600_, v___x_601_, v_init_595_);
return v___x_602_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_fold___redArg___boxed(lean_object* v_headers_603_, lean_object* v_init_604_, lean_object* v_f_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l_Std_Http_Headers_fold___redArg(v_headers_603_, v_init_604_, v_f_605_);
lean_dec_ref(v_headers_603_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_fold(lean_object* v_00_u03b1_607_, lean_object* v_headers_608_, lean_object* v_init_609_, lean_object* v_f_610_){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = l_Std_Http_Headers_fold___redArg(v_headers_608_, v_init_609_, v_f_610_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_fold___boxed(lean_object* v_00_u03b1_612_, lean_object* v_headers_613_, lean_object* v_init_614_, lean_object* v_f_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Std_Http_Headers_fold(v_00_u03b1_612_, v_headers_613_, v_init_614_, v_f_615_);
lean_dec_ref(v_headers_613_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0(lean_object* v_00_u03b1_617_, lean_object* v_f_618_, lean_object* v_as_619_, size_t v_i_620_, size_t v_stop_621_, lean_object* v_b_622_){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___redArg(v_f_618_, v_as_619_, v_i_620_, v_stop_621_, v_b_622_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___boxed(lean_object* v_00_u03b1_624_, lean_object* v_f_625_, lean_object* v_as_626_, lean_object* v_i_627_, lean_object* v_stop_628_, lean_object* v_b_629_){
_start:
{
size_t v_i_boxed_630_; size_t v_stop_boxed_631_; lean_object* v_res_632_; 
v_i_boxed_630_ = lean_unbox_usize(v_i_627_);
lean_dec(v_i_627_);
v_stop_boxed_631_ = lean_unbox_usize(v_stop_628_);
lean_dec(v_stop_628_);
v_res_632_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0(v_00_u03b1_624_, v_f_625_, v_as_626_, v_i_boxed_630_, v_stop_boxed_631_, v_b_629_);
lean_dec_ref(v_as_626_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Headers_mapValues_spec__0(lean_object* v_f_633_, size_t v_sz_634_, size_t v_i_635_, lean_object* v_bs_636_){
_start:
{
uint8_t v___x_637_; 
v___x_637_ = lean_usize_dec_lt(v_i_635_, v_sz_634_);
if (v___x_637_ == 0)
{
lean_dec_ref(v_f_633_);
return v_bs_636_;
}
else
{
lean_object* v_v_638_; lean_object* v_fst_639_; lean_object* v_snd_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_654_; 
v_v_638_ = lean_array_uget(v_bs_636_, v_i_635_);
v_fst_639_ = lean_ctor_get(v_v_638_, 0);
v_snd_640_ = lean_ctor_get(v_v_638_, 1);
v_isSharedCheck_654_ = !lean_is_exclusive(v_v_638_);
if (v_isSharedCheck_654_ == 0)
{
v___x_642_ = v_v_638_;
v_isShared_643_ = v_isSharedCheck_654_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_snd_640_);
lean_inc(v_fst_639_);
lean_dec(v_v_638_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_654_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_644_; lean_object* v_bs_x27_645_; lean_object* v___x_646_; lean_object* v___x_648_; 
v___x_644_ = lean_unsigned_to_nat(0u);
v_bs_x27_645_ = lean_array_uset(v_bs_636_, v_i_635_, v___x_644_);
lean_inc_ref(v_f_633_);
lean_inc(v_fst_639_);
v___x_646_ = lean_apply_2(v_f_633_, v_fst_639_, v_snd_640_);
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 1, v___x_646_);
v___x_648_ = v___x_642_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_fst_639_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v___x_646_);
v___x_648_ = v_reuseFailAlloc_653_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
size_t v___x_649_; size_t v___x_650_; lean_object* v___x_651_; 
v___x_649_ = ((size_t)1ULL);
v___x_650_ = lean_usize_add(v_i_635_, v___x_649_);
v___x_651_ = lean_array_uset(v_bs_x27_645_, v_i_635_, v___x_648_);
v_i_635_ = v___x_650_;
v_bs_636_ = v___x_651_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Headers_mapValues_spec__0___boxed(lean_object* v_f_655_, lean_object* v_sz_656_, lean_object* v_i_657_, lean_object* v_bs_658_){
_start:
{
size_t v_sz_boxed_659_; size_t v_i_boxed_660_; lean_object* v_res_661_; 
v_sz_boxed_659_ = lean_unbox_usize(v_sz_656_);
lean_dec(v_sz_656_);
v_i_boxed_660_ = lean_unbox_usize(v_i_657_);
lean_dec(v_i_657_);
v_res_661_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Headers_mapValues_spec__0(v_f_655_, v_sz_boxed_659_, v_i_boxed_660_, v_bs_658_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_mapValues_spec__1(lean_object* v_as_662_, size_t v_i_663_, size_t v_stop_664_, lean_object* v_b_665_){
_start:
{
uint8_t v___x_666_; 
v___x_666_ = lean_usize_dec_eq(v_i_663_, v_stop_664_);
if (v___x_666_ == 0)
{
lean_object* v___x_667_; lean_object* v___x_668_; size_t v___x_669_; size_t v___x_670_; 
v___x_667_ = lean_array_uget_borrowed(v_as_662_, v_i_663_);
lean_inc(v___x_667_);
v___x_668_ = lean_array_push(v_b_665_, v___x_667_);
v___x_669_ = ((size_t)1ULL);
v___x_670_ = lean_usize_add(v_i_663_, v___x_669_);
v_i_663_ = v___x_670_;
v_b_665_ = v___x_668_;
goto _start;
}
else
{
return v_b_665_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_mapValues_spec__1___boxed(lean_object* v_as_672_, lean_object* v_i_673_, lean_object* v_stop_674_, lean_object* v_b_675_){
_start:
{
size_t v_i_boxed_676_; size_t v_stop_boxed_677_; lean_object* v_res_678_; 
v_i_boxed_676_ = lean_unbox_usize(v_i_673_);
lean_dec(v_i_673_);
v_stop_boxed_677_ = lean_unbox_usize(v_stop_674_);
lean_dec(v_stop_674_);
v_res_678_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_mapValues_spec__1(v_as_672_, v_i_boxed_676_, v_stop_boxed_677_, v_b_675_);
lean_dec_ref(v_as_672_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_mapValues(lean_object* v_headers_679_, lean_object* v_f_680_){
_start:
{
size_t v_sz_681_; size_t v___x_682_; lean_object* v_pairs_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; uint8_t v___x_687_; 
v_sz_681_ = lean_array_size(v_headers_679_);
v___x_682_ = ((size_t)0ULL);
v_pairs_683_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Headers_mapValues_spec__0(v_f_680_, v_sz_681_, v___x_682_, v_headers_679_);
v___x_684_ = lean_obj_once(&l_Std_Http_Headers_empty___closed__0, &l_Std_Http_Headers_empty___closed__0_once, _init_l_Std_Http_Headers_empty___closed__0);
v___x_685_ = lean_unsigned_to_nat(0u);
v___x_686_ = lean_array_get_size(v_pairs_683_);
v___x_687_ = lean_nat_dec_lt(v___x_685_, v___x_686_);
if (v___x_687_ == 0)
{
lean_dec_ref(v_pairs_683_);
return v___x_684_;
}
else
{
size_t v___x_688_; lean_object* v___x_689_; 
v___x_688_ = lean_usize_of_nat(v___x_686_);
v___x_689_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_mapValues_spec__1(v_pairs_683_, v___x_682_, v___x_688_, v___x_684_);
lean_dec_ref(v_pairs_683_);
return v___x_689_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0_spec__0(lean_object* v_f_690_, lean_object* v_as_691_, size_t v_i_692_, size_t v_stop_693_, lean_object* v_b_694_){
_start:
{
lean_object* v___y_696_; uint8_t v___x_700_; 
v___x_700_ = lean_usize_dec_eq(v_i_692_, v_stop_693_);
if (v___x_700_ == 0)
{
lean_object* v___x_701_; lean_object* v_fst_702_; lean_object* v_snd_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_713_; 
v___x_701_ = lean_array_uget(v_as_691_, v_i_692_);
v_fst_702_ = lean_ctor_get(v___x_701_, 0);
v_snd_703_ = lean_ctor_get(v___x_701_, 1);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_713_ == 0)
{
v___x_705_ = v___x_701_;
v_isShared_706_ = v_isSharedCheck_713_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_snd_703_);
lean_inc(v_fst_702_);
lean_dec(v___x_701_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_713_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_707_; 
lean_inc_ref(v_f_690_);
lean_inc(v_fst_702_);
v___x_707_ = lean_apply_2(v_f_690_, v_fst_702_, v_snd_703_);
if (lean_obj_tag(v___x_707_) == 0)
{
lean_del_object(v___x_705_);
lean_dec(v_fst_702_);
v___y_696_ = v_b_694_;
goto v___jp_695_;
}
else
{
lean_object* v_val_708_; lean_object* v___x_710_; 
v_val_708_ = lean_ctor_get(v___x_707_, 0);
lean_inc(v_val_708_);
lean_dec_ref_known(v___x_707_, 1);
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 1, v_val_708_);
v___x_710_ = v___x_705_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_fst_702_);
lean_ctor_set(v_reuseFailAlloc_712_, 1, v_val_708_);
v___x_710_ = v_reuseFailAlloc_712_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
lean_object* v___x_711_; 
v___x_711_ = lean_array_push(v_b_694_, v___x_710_);
v___y_696_ = v___x_711_;
goto v___jp_695_;
}
}
}
}
else
{
lean_dec_ref(v_f_690_);
return v_b_694_;
}
v___jp_695_:
{
size_t v___x_697_; size_t v___x_698_; 
v___x_697_ = ((size_t)1ULL);
v___x_698_ = lean_usize_add(v_i_692_, v___x_697_);
v_i_692_ = v___x_698_;
v_b_694_ = v___y_696_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0_spec__0___boxed(lean_object* v_f_714_, lean_object* v_as_715_, lean_object* v_i_716_, lean_object* v_stop_717_, lean_object* v_b_718_){
_start:
{
size_t v_i_boxed_719_; size_t v_stop_boxed_720_; lean_object* v_res_721_; 
v_i_boxed_719_ = lean_unbox_usize(v_i_716_);
lean_dec(v_i_716_);
v_stop_boxed_720_ = lean_unbox_usize(v_stop_717_);
lean_dec(v_stop_717_);
v_res_721_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0_spec__0(v_f_714_, v_as_715_, v_i_boxed_719_, v_stop_boxed_720_, v_b_718_);
lean_dec_ref(v_as_715_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0(lean_object* v_f_722_, lean_object* v_as_723_, lean_object* v_start_724_, lean_object* v_stop_725_){
_start:
{
lean_object* v___x_726_; uint8_t v___x_727_; 
v___x_726_ = ((lean_object*)(l_Std_Http_Headers_erase___closed__0));
v___x_727_ = lean_nat_dec_lt(v_start_724_, v_stop_725_);
if (v___x_727_ == 0)
{
lean_dec_ref(v_f_722_);
return v___x_726_;
}
else
{
lean_object* v___x_728_; uint8_t v___x_729_; 
v___x_728_ = lean_array_get_size(v_as_723_);
v___x_729_ = lean_nat_dec_le(v_stop_725_, v___x_728_);
if (v___x_729_ == 0)
{
uint8_t v___x_730_; 
v___x_730_ = lean_nat_dec_lt(v_start_724_, v___x_728_);
if (v___x_730_ == 0)
{
lean_dec_ref(v_f_722_);
return v___x_726_;
}
else
{
size_t v___x_731_; size_t v___x_732_; lean_object* v___x_733_; 
v___x_731_ = lean_usize_of_nat(v_start_724_);
v___x_732_ = lean_usize_of_nat(v___x_728_);
v___x_733_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0_spec__0(v_f_722_, v_as_723_, v___x_731_, v___x_732_, v___x_726_);
return v___x_733_;
}
}
else
{
size_t v___x_734_; size_t v___x_735_; lean_object* v___x_736_; 
v___x_734_ = lean_usize_of_nat(v_start_724_);
v___x_735_ = lean_usize_of_nat(v_stop_725_);
v___x_736_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0_spec__0(v_f_722_, v_as_723_, v___x_734_, v___x_735_, v___x_726_);
return v___x_736_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0___boxed(lean_object* v_f_737_, lean_object* v_as_738_, lean_object* v_start_739_, lean_object* v_stop_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0(v_f_737_, v_as_738_, v_start_739_, v_stop_740_);
lean_dec(v_stop_740_);
lean_dec(v_start_739_);
lean_dec_ref(v_as_738_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_filterMap(lean_object* v_headers_742_, lean_object* v_f_743_){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v_pairs_746_; lean_object* v___x_747_; lean_object* v___x_748_; uint8_t v___x_749_; 
v___x_744_ = lean_unsigned_to_nat(0u);
v___x_745_ = lean_array_get_size(v_headers_742_);
v_pairs_746_ = l_Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0(v_f_743_, v_headers_742_, v___x_744_, v___x_745_);
v___x_747_ = lean_obj_once(&l_Std_Http_Headers_empty___closed__0, &l_Std_Http_Headers_empty___closed__0_once, _init_l_Std_Http_Headers_empty___closed__0);
v___x_748_ = lean_array_get_size(v_pairs_746_);
v___x_749_ = lean_nat_dec_lt(v___x_744_, v___x_748_);
if (v___x_749_ == 0)
{
lean_dec_ref(v_pairs_746_);
return v___x_747_;
}
else
{
size_t v___x_750_; size_t v___x_751_; lean_object* v___x_752_; 
v___x_750_ = ((size_t)0ULL);
v___x_751_ = lean_usize_of_nat(v___x_748_);
v___x_752_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_mapValues_spec__1(v_pairs_746_, v___x_750_, v___x_751_, v___x_747_);
lean_dec_ref(v_pairs_746_);
return v___x_752_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_filterMap___boxed(lean_object* v_headers_753_, lean_object* v_f_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_Std_Http_Headers_filterMap(v_headers_753_, v_f_754_);
lean_dec_ref(v_headers_753_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_filter___lam__0(lean_object* v_f_756_, lean_object* v_k_757_, lean_object* v_v_758_){
_start:
{
lean_object* v___x_759_; uint8_t v___x_760_; 
lean_inc_ref(v_v_758_);
v___x_759_ = lean_apply_2(v_f_756_, v_k_757_, v_v_758_);
v___x_760_ = lean_unbox(v___x_759_);
if (v___x_760_ == 0)
{
lean_object* v___x_761_; 
lean_dec_ref(v_v_758_);
v___x_761_ = lean_box(0);
return v___x_761_;
}
else
{
lean_object* v___x_762_; 
v___x_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_762_, 0, v_v_758_);
return v___x_762_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_filter(lean_object* v_headers_763_, lean_object* v_f_764_){
_start:
{
lean_object* v___f_765_; lean_object* v___x_766_; 
v___f_765_ = lean_alloc_closure((void*)(l_Std_Http_Headers_filter___lam__0), 3, 1);
lean_closure_set(v___f_765_, 0, v_f_764_);
v___x_766_ = l_Std_Http_Headers_filterMap(v_headers_763_, v___f_765_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_filter___boxed(lean_object* v_headers_767_, lean_object* v_f_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_Std_Http_Headers_filter(v_headers_767_, v_f_768_);
lean_dec_ref(v_headers_767_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Headers_update_spec__1(lean_object* v_name_770_, lean_object* v_f_771_, size_t v_sz_772_, size_t v_i_773_, lean_object* v_bs_774_){
_start:
{
uint8_t v___x_775_; 
v___x_775_ = lean_usize_dec_lt(v_i_773_, v_sz_772_);
if (v___x_775_ == 0)
{
lean_dec_ref(v_f_771_);
return v_bs_774_;
}
else
{
lean_object* v_v_776_; lean_object* v_fst_777_; lean_object* v_snd_778_; lean_object* v___x_779_; lean_object* v_bs_x27_780_; lean_object* v___y_782_; uint8_t v___x_787_; 
v_v_776_ = lean_array_uget(v_bs_774_, v_i_773_);
v_fst_777_ = lean_ctor_get(v_v_776_, 0);
v_snd_778_ = lean_ctor_get(v_v_776_, 1);
v___x_779_ = lean_unsigned_to_nat(0u);
v_bs_x27_780_ = lean_array_uset(v_bs_774_, v_i_773_, v___x_779_);
v___x_787_ = lean_string_dec_eq(v_fst_777_, v_name_770_);
if (v___x_787_ == 0)
{
v___y_782_ = v_v_776_;
goto v___jp_781_;
}
else
{
lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_795_; 
lean_inc(v_snd_778_);
lean_inc(v_fst_777_);
v_isSharedCheck_795_ = !lean_is_exclusive(v_v_776_);
if (v_isSharedCheck_795_ == 0)
{
lean_object* v_unused_796_; lean_object* v_unused_797_; 
v_unused_796_ = lean_ctor_get(v_v_776_, 1);
lean_dec(v_unused_796_);
v_unused_797_ = lean_ctor_get(v_v_776_, 0);
lean_dec(v_unused_797_);
v___x_789_ = v_v_776_;
v_isShared_790_ = v_isSharedCheck_795_;
goto v_resetjp_788_;
}
else
{
lean_dec(v_v_776_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_795_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_791_; lean_object* v___x_793_; 
lean_inc_ref(v_f_771_);
v___x_791_ = lean_apply_1(v_f_771_, v_snd_778_);
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 1, v___x_791_);
v___x_793_ = v___x_789_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_fst_777_);
lean_ctor_set(v_reuseFailAlloc_794_, 1, v___x_791_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
v___y_782_ = v___x_793_;
goto v___jp_781_;
}
}
}
v___jp_781_:
{
size_t v___x_783_; size_t v___x_784_; lean_object* v___x_785_; 
v___x_783_ = ((size_t)1ULL);
v___x_784_ = lean_usize_add(v_i_773_, v___x_783_);
v___x_785_ = lean_array_uset(v_bs_x27_780_, v_i_773_, v___y_782_);
v_i_773_ = v___x_784_;
v_bs_774_ = v___x_785_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Headers_update_spec__1___boxed(lean_object* v_name_798_, lean_object* v_f_799_, lean_object* v_sz_800_, lean_object* v_i_801_, lean_object* v_bs_802_){
_start:
{
size_t v_sz_boxed_803_; size_t v_i_boxed_804_; lean_object* v_res_805_; 
v_sz_boxed_803_ = lean_unbox_usize(v_sz_800_);
lean_dec(v_sz_800_);
v_i_boxed_804_ = lean_unbox_usize(v_i_801_);
lean_dec(v_i_801_);
v_res_805_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Headers_update_spec__1(v_name_798_, v_f_799_, v_sz_boxed_803_, v_i_boxed_804_, v_bs_802_);
lean_dec_ref(v_name_798_);
return v_res_805_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Headers_update_spec__0(lean_object* v_name_806_, lean_object* v_as_807_, size_t v_i_808_, size_t v_stop_809_){
_start:
{
uint8_t v___x_810_; 
v___x_810_ = lean_usize_dec_eq(v_i_808_, v_stop_809_);
if (v___x_810_ == 0)
{
lean_object* v___x_811_; lean_object* v_fst_812_; uint8_t v___x_813_; 
v___x_811_ = lean_array_uget_borrowed(v_as_807_, v_i_808_);
v_fst_812_ = lean_ctor_get(v___x_811_, 0);
v___x_813_ = lean_string_dec_eq(v_fst_812_, v_name_806_);
if (v___x_813_ == 0)
{
size_t v___x_814_; size_t v___x_815_; 
v___x_814_ = ((size_t)1ULL);
v___x_815_ = lean_usize_add(v_i_808_, v___x_814_);
v_i_808_ = v___x_815_;
goto _start;
}
else
{
return v___x_813_;
}
}
else
{
uint8_t v___x_817_; 
v___x_817_ = 0;
return v___x_817_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Headers_update_spec__0___boxed(lean_object* v_name_818_, lean_object* v_as_819_, lean_object* v_i_820_, lean_object* v_stop_821_){
_start:
{
size_t v_i_boxed_822_; size_t v_stop_boxed_823_; uint8_t v_res_824_; lean_object* v_r_825_; 
v_i_boxed_822_ = lean_unbox_usize(v_i_820_);
lean_dec(v_i_820_);
v_stop_boxed_823_ = lean_unbox_usize(v_stop_821_);
lean_dec(v_stop_821_);
v_res_824_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Headers_update_spec__0(v_name_818_, v_as_819_, v_i_boxed_822_, v_stop_boxed_823_);
lean_dec_ref(v_as_819_);
lean_dec_ref(v_name_818_);
v_r_825_ = lean_box(v_res_824_);
return v_r_825_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_update(lean_object* v_headers_826_, lean_object* v_name_827_, lean_object* v_f_828_){
_start:
{
lean_object* v___x_829_; lean_object* v___x_830_; uint8_t v___x_831_; 
v___x_829_ = lean_unsigned_to_nat(0u);
v___x_830_ = lean_array_get_size(v_headers_826_);
v___x_831_ = lean_nat_dec_lt(v___x_829_, v___x_830_);
if (v___x_831_ == 0)
{
lean_dec_ref(v_f_828_);
return v_headers_826_;
}
else
{
size_t v___x_832_; size_t v___x_833_; uint8_t v___x_834_; 
v___x_832_ = ((size_t)0ULL);
v___x_833_ = lean_usize_of_nat(v___x_830_);
v___x_834_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Headers_update_spec__0(v_name_827_, v_headers_826_, v___x_832_, v___x_833_);
if (v___x_834_ == 0)
{
lean_dec_ref(v_f_828_);
return v_headers_826_;
}
else
{
size_t v_sz_835_; lean_object* v___x_836_; 
v_sz_835_ = lean_array_size(v_headers_826_);
v___x_836_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Headers_update_spec__1(v_name_827_, v_f_828_, v_sz_835_, v___x_832_, v_headers_826_);
return v___x_836_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_update___boxed(lean_object* v_headers_837_, lean_object* v_name_838_, lean_object* v_f_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_Std_Http_Headers_update(v_headers_837_, v_name_838_, v_f_839_);
lean_dec_ref(v_name_838_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_replaceLast(lean_object* v_headers_841_, lean_object* v_name_842_, lean_object* v_value_843_){
_start:
{
lean_object* v___f_844_; lean_object* v___x_845_; lean_object* v_i_846_; uint8_t v___x_847_; 
v___f_844_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___x_845_ = lean_array_get_size(v_headers_841_);
lean_inc_ref(v_name_842_);
v_i_846_ = l_Std_Internal_MultiMap_findLastIdxBelow___redArg(v___f_844_, v_headers_841_, v_name_842_, v___x_845_);
v___x_847_ = lean_nat_dec_lt(v_i_846_, v___x_845_);
if (v___x_847_ == 0)
{
lean_dec(v_i_846_);
lean_dec_ref(v_value_843_);
lean_dec_ref(v_name_842_);
return v_headers_841_;
}
else
{
lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_848_, 0, v_name_842_);
lean_ctor_set(v___x_848_, 1, v_value_843_);
v___x_849_ = lean_array_fset(v_headers_841_, v_i_846_, v___x_848_);
lean_dec(v_i_846_);
return v___x_849_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instToString___lam__0(lean_object* v___x_850_, lean_object* v___x_851_, lean_object* v___x_852_, lean_object* v_fst_853_, lean_object* v___x_854_, uint32_t v___x_855_, lean_object* v___x_856_, lean_object* v_it_857_, lean_object* v_acc_858_, lean_object* v_hP_859_, lean_object* v_recur_860_){
_start:
{
lean_object* v_it_862_; lean_object* v_out_863_; lean_object* v_it_879_; lean_object* v_startInclusive_880_; lean_object* v_endExclusive_881_; 
if (lean_obj_tag(v_it_857_) == 0)
{
lean_object* v_currPos_893_; lean_object* v_searcher_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_916_; 
v_currPos_893_ = lean_ctor_get(v_it_857_, 0);
v_searcher_894_ = lean_ctor_get(v_it_857_, 1);
v_isSharedCheck_916_ = !lean_is_exclusive(v_it_857_);
if (v_isSharedCheck_916_ == 0)
{
v___x_896_ = v_it_857_;
v_isShared_897_ = v_isSharedCheck_916_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_searcher_894_);
lean_inc(v_currPos_893_);
lean_dec(v_it_857_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_916_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
uint8_t v_decide_898_; 
v_decide_898_ = lean_nat_dec_eq(v_searcher_894_, v___x_854_);
if (v_decide_898_ == 0)
{
uint32_t v___x_899_; uint8_t v___x_900_; 
lean_dec(v___x_854_);
v___x_899_ = lean_string_utf8_get_fast(v_fst_853_, v_searcher_894_);
v___x_900_ = lean_uint32_dec_eq(v___x_899_, v___x_855_);
if (v___x_900_ == 0)
{
lean_object* v___x_901_; lean_object* v___x_903_; 
v___x_901_ = lean_string_utf8_next_fast(v_fst_853_, v_searcher_894_);
lean_dec(v_searcher_894_);
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 1, v___x_901_);
v___x_903_ = v___x_896_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_currPos_893_);
lean_ctor_set(v_reuseFailAlloc_905_, 1, v___x_901_);
v___x_903_ = v_reuseFailAlloc_905_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
lean_object* v___x_904_; 
v___x_904_ = lean_apply_4(v_recur_860_, v___x_903_, v_acc_858_, lean_box(0), lean_box(0));
return v___x_904_;
}
}
else
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v_slice_909_; lean_object* v_nextIt_911_; 
v___x_906_ = lean_string_utf8_next_fast(v_fst_853_, v_searcher_894_);
v___x_907_ = lean_nat_sub(v___x_906_, v_searcher_894_);
v___x_908_ = lean_nat_add(v_searcher_894_, v___x_907_);
lean_dec(v___x_907_);
v_slice_909_ = l_String_Slice_subslice_x21(v___x_856_, v_currPos_893_, v_searcher_894_);
lean_inc(v___x_908_);
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 1, v___x_908_);
lean_ctor_set(v___x_896_, 0, v___x_908_);
v_nextIt_911_ = v___x_896_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v___x_908_);
lean_ctor_set(v_reuseFailAlloc_914_, 1, v___x_908_);
v_nextIt_911_ = v_reuseFailAlloc_914_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
lean_object* v_startInclusive_912_; lean_object* v_endExclusive_913_; 
v_startInclusive_912_ = lean_ctor_get(v_slice_909_, 0);
lean_inc(v_startInclusive_912_);
v_endExclusive_913_ = lean_ctor_get(v_slice_909_, 1);
lean_inc(v_endExclusive_913_);
lean_dec_ref(v_slice_909_);
v_it_879_ = v_nextIt_911_;
v_startInclusive_880_ = v_startInclusive_912_;
v_endExclusive_881_ = v_endExclusive_913_;
goto v___jp_878_;
}
}
}
else
{
lean_object* v___x_915_; 
lean_del_object(v___x_896_);
lean_dec(v_searcher_894_);
v___x_915_ = lean_box(1);
v_it_879_ = v___x_915_;
v_startInclusive_880_ = v_currPos_893_;
v_endExclusive_881_ = v___x_854_;
goto v___jp_878_;
}
}
}
else
{
lean_dec_ref(v_recur_860_);
lean_dec(v___x_854_);
return v_acc_858_;
}
v___jp_861_:
{
if (lean_obj_tag(v_acc_858_) == 0)
{
lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_864_, 0, v_out_863_);
v___x_865_ = lean_apply_4(v_recur_860_, v_it_862_, v___x_864_, lean_box(0), lean_box(0));
return v___x_865_;
}
else
{
lean_object* v_val_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_877_; 
v_val_866_ = lean_ctor_get(v_acc_858_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v_acc_858_);
if (v_isSharedCheck_877_ == 0)
{
v___x_868_ = v_acc_858_;
v_isShared_869_ = v_isSharedCheck_877_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_val_866_);
lean_dec(v_acc_858_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_877_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_874_; 
v___x_870_ = lean_string_utf8_extract_fast(v___x_850_, v___x_851_, v___x_852_);
v___x_871_ = lean_string_append(v_val_866_, v___x_870_);
lean_dec_ref(v___x_870_);
v___x_872_ = lean_string_append(v___x_871_, v_out_863_);
lean_dec_ref(v_out_863_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 0, v___x_872_);
v___x_874_ = v___x_868_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_872_);
v___x_874_ = v_reuseFailAlloc_876_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
lean_object* v___x_875_; 
v___x_875_ = lean_apply_4(v_recur_860_, v_it_862_, v___x_874_, lean_box(0), lean_box(0));
return v___x_875_;
}
}
}
}
v___jp_878_:
{
lean_object* v___x_882_; uint32_t v___x_883_; uint32_t v___x_884_; uint8_t v___x_885_; 
v___x_882_ = lean_string_utf8_extract_fast(v_fst_853_, v_startInclusive_880_, v_endExclusive_881_);
lean_dec(v_endExclusive_881_);
lean_dec(v_startInclusive_880_);
v___x_883_ = lean_string_utf8_get(v___x_882_, v___x_851_);
v___x_884_ = 97;
v___x_885_ = lean_uint32_dec_le(v___x_884_, v___x_883_);
if (v___x_885_ == 0)
{
lean_object* v___x_886_; 
v___x_886_ = lean_string_utf8_set(v___x_882_, v___x_851_, v___x_883_);
v_it_862_ = v_it_879_;
v_out_863_ = v___x_886_;
goto v___jp_861_;
}
else
{
uint32_t v___x_887_; uint8_t v___x_888_; 
v___x_887_ = 122;
v___x_888_ = lean_uint32_dec_le(v___x_883_, v___x_887_);
if (v___x_888_ == 0)
{
lean_object* v___x_889_; 
v___x_889_ = lean_string_utf8_set(v___x_882_, v___x_851_, v___x_883_);
v_it_862_ = v_it_879_;
v_out_863_ = v___x_889_;
goto v___jp_861_;
}
else
{
uint32_t v___x_890_; uint32_t v___x_891_; lean_object* v___x_892_; 
v___x_890_ = 4294967264;
v___x_891_ = lean_uint32_add(v___x_883_, v___x_890_);
v___x_892_ = lean_string_utf8_set(v___x_882_, v___x_851_, v___x_891_);
v_it_862_ = v_it_879_;
v_out_863_ = v___x_892_;
goto v___jp_861_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instToString___lam__0___boxed(lean_object* v___x_917_, lean_object* v___x_918_, lean_object* v___x_919_, lean_object* v_fst_920_, lean_object* v___x_921_, lean_object* v___x_922_, lean_object* v___x_923_, lean_object* v_it_924_, lean_object* v_acc_925_, lean_object* v_hP_926_, lean_object* v_recur_927_){
_start:
{
uint32_t v___x_1798__boxed_928_; lean_object* v_res_929_; 
v___x_1798__boxed_928_ = lean_unbox_uint32(v___x_922_);
lean_dec(v___x_922_);
v_res_929_ = l_Std_Http_Headers_instToString___lam__0(v___x_917_, v___x_918_, v___x_919_, v_fst_920_, v___x_921_, v___x_1798__boxed_928_, v___x_923_, v_it_924_, v_acc_925_, v_hP_926_, v_recur_927_);
lean_dec_ref(v___x_923_);
lean_dec_ref(v_fst_920_);
lean_dec(v___x_919_);
lean_dec(v___x_918_);
lean_dec_ref(v___x_917_);
return v_res_929_;
}
}
static lean_object* _init_l_Std_Http_Headers_instToString___lam__1___boxed__const__1(void){
_start:
{
uint32_t v___x_933_; lean_object* v___x_934_; 
v___x_933_ = 45;
v___x_934_ = lean_box_uint32(v___x_933_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instToString___lam__1(lean_object* v_x_935_){
_start:
{
lean_object* v_fst_936_; lean_object* v_snd_937_; lean_object* v___y_939_; lean_object* v___f_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v_it_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___f_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
v_fst_936_ = lean_ctor_get(v_x_935_, 0);
lean_inc_n(v_fst_936_, 2);
v_snd_937_ = lean_ctor_get(v_x_935_, 1);
lean_inc(v_snd_937_);
lean_dec_ref(v_x_935_);
v___f_943_ = ((lean_object*)(l_Std_Http_Headers_instToString___lam__1___closed__1));
v___x_944_ = lean_unsigned_to_nat(0u);
v___x_945_ = lean_string_utf8_byte_size(v_fst_936_);
v___x_946_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_946_, 0, v_fst_936_);
lean_ctor_set(v___x_946_, 1, v___x_944_);
lean_ctor_set(v___x_946_, 2, v___x_945_);
lean_inc_ref(v___x_946_);
v_it_947_ = l_String_Slice_splitToSubslice___redArg(v___x_946_, v___f_943_);
v___x_948_ = ((lean_object*)(l_Std_Http_Headers_instToString___lam__1___closed__2));
v___x_949_ = lean_unsigned_to_nat(1u);
v___x_950_ = l_Std_Http_Headers_instToString___lam__1___boxed__const__1;
v___f_951_ = lean_alloc_closure((void*)(l_Std_Http_Headers_instToString___lam__0___boxed), 11, 7);
lean_closure_set(v___f_951_, 0, v___x_948_);
lean_closure_set(v___f_951_, 1, v___x_944_);
lean_closure_set(v___f_951_, 2, v___x_949_);
lean_closure_set(v___f_951_, 3, v_fst_936_);
lean_closure_set(v___f_951_, 4, v___x_945_);
lean_closure_set(v___f_951_, 5, v___x_950_);
lean_closure_set(v___f_951_, 6, v___x_946_);
v___x_952_ = lean_box(0);
v___x_953_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_951_, v_it_947_, v___x_952_, lean_box(0));
if (lean_obj_tag(v___x_953_) == 0)
{
lean_object* v___x_954_; 
v___x_954_ = ((lean_object*)(l_Std_Http_Headers_get_x21___closed__0));
v___y_939_ = v___x_954_;
goto v___jp_938_;
}
else
{
lean_object* v_val_955_; 
v_val_955_ = lean_ctor_get(v___x_953_, 0);
lean_inc(v_val_955_);
lean_dec_ref_known(v___x_953_, 1);
v___y_939_ = v_val_955_;
goto v___jp_938_;
}
v___jp_938_:
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_940_ = ((lean_object*)(l_Std_Http_Headers_instToString___lam__1___closed__0));
v___x_941_ = lean_string_append(v___y_939_, v___x_940_);
v___x_942_ = lean_string_append(v___x_941_, v_snd_937_);
lean_dec(v_snd_937_);
return v___x_942_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instToString___lam__2(lean_object* v___f_957_, lean_object* v_headers_958_){
_start:
{
lean_object* v___x_959_; size_t v_sz_960_; size_t v___x_961_; lean_object* v_pairs_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_959_ = ((lean_object*)(l_Std_Http_Headers_getAll___redArg___closed__10));
v_sz_960_ = lean_array_size(v_headers_958_);
v___x_961_ = ((size_t)0ULL);
v_pairs_962_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_959_, v___f_957_, v_sz_960_, v___x_961_, v_headers_958_);
v___x_963_ = ((lean_object*)(l_Std_Http_Headers_instToString___lam__2___closed__0));
v___x_964_ = lean_array_to_list(v_pairs_962_);
v___x_965_ = l_String_intercalate(v___x_963_, v___x_964_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instEncodeV11___lam__0(lean_object* v_out_971_, lean_object* v_headers_972_){
_start:
{
lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_973_ = ((lean_object*)(l_Std_Http_Headers_instEncodeV11___lam__0___closed__0));
v___x_974_ = l_Std_Http_Headers_fold___redArg(v_headers_972_, v_out_971_, v___x_973_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instEncodeV11___lam__0___boxed(lean_object* v_out_975_, lean_object* v_headers_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_Std_Http_Headers_instEncodeV11___lam__0(v_out_975_, v_headers_976_);
lean_dec_ref(v_headers_976_);
return v_res_977_;
}
}
static lean_object* _init_l_Std_Http_Headers_instEmptyCollection(void){
_start:
{
lean_object* v___x_980_; 
v___x_980_ = lean_obj_once(&l_Std_Http_Headers_empty___closed__0, &l_Std_Http_Headers_empty___closed__0_once, _init_l_Std_Http_Headers_empty___closed__0);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instSingletonProdNameValue___lam__0(lean_object* v_x_981_){
_start:
{
lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_982_ = lean_obj_once(&l_Std_Http_Headers_empty___closed__0, &l_Std_Http_Headers_empty___closed__0_once, _init_l_Std_Http_Headers_empty___closed__0);
v___x_983_ = lean_array_push(v___x_982_, v_x_981_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instInsertProdNameValue___lam__0(lean_object* v_x_986_, lean_object* v_s_987_){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = lean_array_push(v_s_987_, v_x_986_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instForInProdNameValueOfMonad___redArg___lam__0(lean_object* v_f_993_, lean_object* v_a_994_, lean_object* v_x_995_, lean_object* v___y_996_){
_start:
{
lean_object* v___x_997_; 
v___x_997_ = lean_apply_2(v_f_993_, v_a_994_, v___y_996_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instForInProdNameValueOfMonad___redArg___lam__1(lean_object* v_inst_998_, lean_object* v_00_u03b2_999_, lean_object* v_headers_1000_, lean_object* v_b_1001_, lean_object* v_f_1002_){
_start:
{
lean_object* v___f_1003_; size_t v_sz_1004_; size_t v___x_1005_; lean_object* v___x_1006_; 
v___f_1003_ = lean_alloc_closure((void*)(l_Std_Http_Headers_instForInProdNameValueOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1003_, 0, v_f_1002_);
v_sz_1004_ = lean_array_size(v_headers_1000_);
v___x_1005_ = ((size_t)0ULL);
v___x_1006_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_998_, v_headers_1000_, v___f_1003_, v_sz_1004_, v___x_1005_, v_b_1001_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instForInProdNameValueOfMonad___redArg(lean_object* v_inst_1007_){
_start:
{
lean_object* v___f_1008_; 
v___f_1008_ = lean_alloc_closure((void*)(l_Std_Http_Headers_instForInProdNameValueOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_1008_, 0, v_inst_1007_);
return v___f_1008_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instForInProdNameValueOfMonad(lean_object* v_m_1009_, lean_object* v_inst_1010_){
_start:
{
lean_object* v___f_1011_; 
v___f_1011_ = lean_alloc_closure((void*)(l_Std_Http_Headers_instForInProdNameValueOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_1011_, 0, v_inst_1010_);
return v___f_1011_;
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
