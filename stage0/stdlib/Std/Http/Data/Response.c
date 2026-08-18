// Lean compiler output
// Module: Std.Http.Data.Response
// Imports: public import Std.Http.Data.Extensions public import Std.Http.Data.Status public import Std.Http.Data.Version public import Std.Http.Data.Headers
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_noption_get(lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
extern lean_object* l_Std_Http_Headers_empty;
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___lam__0___boxed(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_splitToSubslice___redArg(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint16_t l_Std_Http_Status_toCode(lean_object*);
lean_object* lean_uint16_to_nat(uint16_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Std_Http_Status_reasonPhrase(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
extern lean_object* l_Std_Http_Extensions_empty;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Std_Http_Extensions_compareName___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Dynamic_0__Dynamic_typeNameImpl(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_instReprStatus_repr(lean_object*, lean_object*);
lean_object* l_Std_Http_instReprVersion_repr(uint8_t, lean_object*);
lean_object* l_Std_Http_instReprHeaders_repr___redArg(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_byte_array_size(lean_object*);
uint8_t lean_uint32_to_uint8(uint32_t);
lean_object* lean_byte_array_mk(lean_object*);
lean_object* l_Std_Http_Headers_fold___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_Header_Name_ofString_x21(lean_object*);
lean_object* l_Std_Http_Header_Value_ofString_x21(lean_object*);
lean_object* l_Std_Http_Header_Name_ofString_x3f(lean_object*);
lean_object* l_Std_Http_Header_Value_ofString_x3f(lean_object*);
static lean_once_cell_t l_Std_Http_Response_instInhabitedHead_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_instInhabitedHead_default___closed__0;
LEAN_EXPORT lean_object* l_Std_Http_Response_instInhabitedHead_default;
LEAN_EXPORT lean_object* l_Std_Http_Response_instInhabitedHead;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Http_Response_instReprHead_repr_spec__0(lean_object*);
static const lean_string_object l_Std_Http_Response_instReprHead_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Std_Http_Response_instReprHead_repr___redArg___closed__0 = (const lean_object*)&l_Std_Http_Response_instReprHead_repr___redArg___closed__0_value;
static const lean_string_object l_Std_Http_Response_instReprHead_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "status"};
static const lean_object* l_Std_Http_Response_instReprHead_repr___redArg___closed__1 = (const lean_object*)&l_Std_Http_Response_instReprHead_repr___redArg___closed__1_value;
static const lean_ctor_object l_Std_Http_Response_instReprHead_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Response_instReprHead_repr___redArg___closed__1_value)}};
static const lean_object* l_Std_Http_Response_instReprHead_repr___redArg___closed__2 = (const lean_object*)&l_Std_Http_Response_instReprHead_repr___redArg___closed__2_value;
static const lean_ctor_object l_Std_Http_Response_instReprHead_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_Response_instReprHead_repr___redArg___closed__2_value)}};
static const lean_object* l_Std_Http_Response_instReprHead_repr___redArg___closed__3 = (const lean_object*)&l_Std_Http_Response_instReprHead_repr___redArg___closed__3_value;
static const lean_string_object l_Std_Http_Response_instReprHead_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Std_Http_Response_instReprHead_repr___redArg___closed__4 = (const lean_object*)&l_Std_Http_Response_instReprHead_repr___redArg___closed__4_value;
static const lean_ctor_object l_Std_Http_Response_instReprHead_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Response_instReprHead_repr___redArg___closed__4_value)}};
static const lean_object* l_Std_Http_Response_instReprHead_repr___redArg___closed__5 = (const lean_object*)&l_Std_Http_Response_instReprHead_repr___redArg___closed__5_value;
static const lean_ctor_object l_Std_Http_Response_instReprHead_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Http_Response_instReprHead_repr___redArg___closed__3_value),((lean_object*)&l_Std_Http_Response_instReprHead_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Http_Response_instReprHead_repr___redArg___closed__6 = (const lean_object*)&l_Std_Http_Response_instReprHead_repr___redArg___closed__6_value;
static lean_once_cell_t l_Std_Http_Response_instReprHead_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_instReprHead_repr___redArg___closed__7;
static const lean_string_object l_Std_Http_Response_instReprHead_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Std_Http_Response_instReprHead_repr___redArg___closed__8 = (const lean_object*)&l_Std_Http_Response_instReprHead_repr___redArg___closed__8_value;
static const lean_ctor_object l_Std_Http_Response_instReprHead_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Response_instReprHead_repr___redArg___closed__8_value)}};
static const lean_object* l_Std_Http_Response_instReprHead_repr___redArg___closed__9 = (const lean_object*)&l_Std_Http_Response_instReprHead_repr___redArg___closed__9_value;
static const lean_string_object l_Std_Http_Response_instReprHead_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "version"};
static const lean_object* l_Std_Http_Response_instReprHead_repr___redArg___closed__10 = (const lean_object*)&l_Std_Http_Response_instReprHead_repr___redArg___closed__10_value;
static const lean_ctor_object l_Std_Http_Response_instReprHead_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Response_instReprHead_repr___redArg___closed__10_value)}};
static const lean_object* l_Std_Http_Response_instReprHead_repr___redArg___closed__11 = (const lean_object*)&l_Std_Http_Response_instReprHead_repr___redArg___closed__11_value;
static lean_once_cell_t l_Std_Http_Response_instReprHead_repr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_instReprHead_repr___redArg___closed__12;
static const lean_string_object l_Std_Http_Response_instReprHead_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "headers"};
static const lean_object* l_Std_Http_Response_instReprHead_repr___redArg___closed__13 = (const lean_object*)&l_Std_Http_Response_instReprHead_repr___redArg___closed__13_value;
static const lean_ctor_object l_Std_Http_Response_instReprHead_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Response_instReprHead_repr___redArg___closed__13_value)}};
static const lean_object* l_Std_Http_Response_instReprHead_repr___redArg___closed__14 = (const lean_object*)&l_Std_Http_Response_instReprHead_repr___redArg___closed__14_value;
static const lean_string_object l_Std_Http_Response_instReprHead_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Std_Http_Response_instReprHead_repr___redArg___closed__15 = (const lean_object*)&l_Std_Http_Response_instReprHead_repr___redArg___closed__15_value;
static lean_once_cell_t l_Std_Http_Response_instReprHead_repr___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_instReprHead_repr___redArg___closed__16;
static lean_once_cell_t l_Std_Http_Response_instReprHead_repr___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_instReprHead_repr___redArg___closed__17;
static const lean_ctor_object l_Std_Http_Response_instReprHead_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Response_instReprHead_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Http_Response_instReprHead_repr___redArg___closed__18 = (const lean_object*)&l_Std_Http_Response_instReprHead_repr___redArg___closed__18_value;
static const lean_ctor_object l_Std_Http_Response_instReprHead_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Response_instReprHead_repr___redArg___closed__15_value)}};
static const lean_object* l_Std_Http_Response_instReprHead_repr___redArg___closed__19 = (const lean_object*)&l_Std_Http_Response_instReprHead_repr___redArg___closed__19_value;
LEAN_EXPORT lean_object* l_Std_Http_Response_instReprHead_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_instReprHead_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_instReprHead_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Response_instReprHead___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Response_instReprHead_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Response_instReprHead___closed__0 = (const lean_object*)&l_Std_Http_Response_instReprHead___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Response_instReprHead = (const lean_object*)&l_Std_Http_Response_instReprHead___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_instInhabitedResponse_default___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instInhabitedResponse_default(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instInhabitedResponse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instInhabitedResponse(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_instToStringHead___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_instToStringHead___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Http_Response_instToStringHead___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Std_Http_Response_instToStringHead___lam__1___closed__0 = (const lean_object*)&l_Std_Http_Response_instToStringHead___lam__1___closed__0_value;
static const lean_closure_object l_Std_Http_Response_instToStringHead___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Response_instToStringHead___lam__1___closed__1 = (const lean_object*)&l_Std_Http_Response_instToStringHead___lam__1___closed__1_value;
static const lean_string_object l_Std_Http_Response_instToStringHead___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Std_Http_Response_instToStringHead___lam__1___closed__2 = (const lean_object*)&l_Std_Http_Response_instToStringHead___lam__1___closed__2_value;
static lean_once_cell_t l_Std_Http_Response_instToStringHead___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_instToStringHead___lam__1___closed__3;
static const lean_string_object l_Std_Http_Response_instToStringHead___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_Http_Response_instToStringHead___lam__1___closed__4 = (const lean_object*)&l_Std_Http_Response_instToStringHead___lam__1___closed__4_value;
LEAN_EXPORT lean_object* l_Std_Http_Response_instToStringHead___lam__1___boxed__const__1;
LEAN_EXPORT lean_object* l_Std_Http_Response_instToStringHead___lam__1(lean_object*);
static const lean_string_object l_Std_Http_Response_instToStringHead___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Std_Http_Response_instToStringHead___lam__2___closed__0 = (const lean_object*)&l_Std_Http_Response_instToStringHead___lam__2___closed__0_value;
static const lean_string_object l_Std_Http_Response_instToStringHead___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\r\n"};
static const lean_object* l_Std_Http_Response_instToStringHead___lam__2___closed__1 = (const lean_object*)&l_Std_Http_Response_instToStringHead___lam__2___closed__1_value;
static const lean_closure_object l_Std_Http_Response_instToStringHead___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Response_instToStringHead___lam__2___closed__2 = (const lean_object*)&l_Std_Http_Response_instToStringHead___lam__2___closed__2_value;
static const lean_closure_object l_Std_Http_Response_instToStringHead___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Response_instToStringHead___lam__2___closed__3 = (const lean_object*)&l_Std_Http_Response_instToStringHead___lam__2___closed__3_value;
static const lean_closure_object l_Std_Http_Response_instToStringHead___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Response_instToStringHead___lam__2___closed__4 = (const lean_object*)&l_Std_Http_Response_instToStringHead___lam__2___closed__4_value;
static const lean_closure_object l_Std_Http_Response_instToStringHead___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Response_instToStringHead___lam__2___closed__5 = (const lean_object*)&l_Std_Http_Response_instToStringHead___lam__2___closed__5_value;
static const lean_closure_object l_Std_Http_Response_instToStringHead___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Response_instToStringHead___lam__2___closed__6 = (const lean_object*)&l_Std_Http_Response_instToStringHead___lam__2___closed__6_value;
static const lean_closure_object l_Std_Http_Response_instToStringHead___lam__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Response_instToStringHead___lam__2___closed__7 = (const lean_object*)&l_Std_Http_Response_instToStringHead___lam__2___closed__7_value;
static const lean_closure_object l_Std_Http_Response_instToStringHead___lam__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Response_instToStringHead___lam__2___closed__8 = (const lean_object*)&l_Std_Http_Response_instToStringHead___lam__2___closed__8_value;
static const lean_ctor_object l_Std_Http_Response_instToStringHead___lam__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Response_instToStringHead___lam__2___closed__2_value),((lean_object*)&l_Std_Http_Response_instToStringHead___lam__2___closed__3_value)}};
static const lean_object* l_Std_Http_Response_instToStringHead___lam__2___closed__9 = (const lean_object*)&l_Std_Http_Response_instToStringHead___lam__2___closed__9_value;
static const lean_ctor_object l_Std_Http_Response_instToStringHead___lam__2___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Response_instToStringHead___lam__2___closed__9_value),((lean_object*)&l_Std_Http_Response_instToStringHead___lam__2___closed__4_value),((lean_object*)&l_Std_Http_Response_instToStringHead___lam__2___closed__5_value),((lean_object*)&l_Std_Http_Response_instToStringHead___lam__2___closed__6_value),((lean_object*)&l_Std_Http_Response_instToStringHead___lam__2___closed__7_value)}};
static const lean_object* l_Std_Http_Response_instToStringHead___lam__2___closed__10 = (const lean_object*)&l_Std_Http_Response_instToStringHead___lam__2___closed__10_value;
static const lean_ctor_object l_Std_Http_Response_instToStringHead___lam__2___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Response_instToStringHead___lam__2___closed__10_value),((lean_object*)&l_Std_Http_Response_instToStringHead___lam__2___closed__8_value)}};
static const lean_object* l_Std_Http_Response_instToStringHead___lam__2___closed__11 = (const lean_object*)&l_Std_Http_Response_instToStringHead___lam__2___closed__11_value;
static const lean_string_object l_Std_Http_Response_instToStringHead___lam__2___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "HTTP/1.0"};
static const lean_object* l_Std_Http_Response_instToStringHead___lam__2___closed__12 = (const lean_object*)&l_Std_Http_Response_instToStringHead___lam__2___closed__12_value;
static const lean_string_object l_Std_Http_Response_instToStringHead___lam__2___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "HTTP/1.1"};
static const lean_object* l_Std_Http_Response_instToStringHead___lam__2___closed__13 = (const lean_object*)&l_Std_Http_Response_instToStringHead___lam__2___closed__13_value;
static const lean_string_object l_Std_Http_Response_instToStringHead___lam__2___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "HTTP/2.0"};
static const lean_object* l_Std_Http_Response_instToStringHead___lam__2___closed__14 = (const lean_object*)&l_Std_Http_Response_instToStringHead___lam__2___closed__14_value;
static const lean_string_object l_Std_Http_Response_instToStringHead___lam__2___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "HTTP/3.0"};
static const lean_object* l_Std_Http_Response_instToStringHead___lam__2___closed__15 = (const lean_object*)&l_Std_Http_Response_instToStringHead___lam__2___closed__15_value;
LEAN_EXPORT lean_object* l_Std_Http_Response_instToStringHead___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Response_instToStringHead___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Response_instToStringHead___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Response_instToStringHead___closed__0 = (const lean_object*)&l_Std_Http_Response_instToStringHead___closed__0_value;
static const lean_closure_object l_Std_Http_Response_instToStringHead___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Response_instToStringHead___lam__2, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Response_instToStringHead___closed__0_value)} };
static const lean_object* l_Std_Http_Response_instToStringHead___closed__1 = (const lean_object*)&l_Std_Http_Response_instToStringHead___closed__1_value;
LEAN_EXPORT const lean_object* l_Std_Http_Response_instToStringHead = (const lean_object*)&l_Std_Http_Response_instToStringHead___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Response_instEncodeV11Head___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_instEncodeV11Head___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_instEncodeV11Head___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_instEncodeV11Head___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Http_Response_instEncodeV11Head___lam__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_Response_instEncodeV11Head___lam__2___closed__0;
static lean_once_cell_t l_Std_Http_Response_instEncodeV11Head___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_instEncodeV11Head___lam__2___closed__1;
static lean_once_cell_t l_Std_Http_Response_instEncodeV11Head___lam__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_instEncodeV11Head___lam__2___closed__2;
static lean_once_cell_t l_Std_Http_Response_instEncodeV11Head___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_instEncodeV11Head___lam__2___closed__3;
static lean_once_cell_t l_Std_Http_Response_instEncodeV11Head___lam__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_instEncodeV11Head___lam__2___closed__4;
LEAN_EXPORT lean_object* l_Std_Http_Response_instEncodeV11Head___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_instEncodeV11Head___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Response_instEncodeV11Head___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Response_instEncodeV11Head___lam__1___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Response_instEncodeV11Head___closed__0 = (const lean_object*)&l_Std_Http_Response_instEncodeV11Head___closed__0_value;
static const lean_closure_object l_Std_Http_Response_instEncodeV11Head___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Response_instEncodeV11Head___lam__2___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Response_instEncodeV11Head___closed__0_value)} };
static const lean_object* l_Std_Http_Response_instEncodeV11Head___closed__1 = (const lean_object*)&l_Std_Http_Response_instEncodeV11Head___closed__1_value;
LEAN_EXPORT const lean_object* l_Std_Http_Response_instEncodeV11Head = (const lean_object*)&l_Std_Http_Response_instEncodeV11Head___closed__1_value;
static lean_once_cell_t l_Std_Http_Response_new___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_new___closed__0;
LEAN_EXPORT lean_object* l_Std_Http_Response_new;
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_new;
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_status(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_headers(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_header___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Http_Response_Builder_header_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Http_Response_Builder_header_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Http_Response_Builder_header_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Http_Response_Builder_header_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Http_Response_Builder_header_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Http_Response_Builder_header_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Http_Response_Builder_header_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Http_Response_Builder_header_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Http_Response_Builder_header_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Http_Response_Builder_header_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_header(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Http_Response_Builder_header_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Http_Response_Builder_header_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Http_Response_Builder_header_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Http_Response_Builder_header_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Http_Response_Builder_header_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Http_Response_Builder_header_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Http_Response_Builder_header_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Http_Response_Builder_header_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Http_Response_Builder_header_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Http_Response_Builder_header_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_header_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_header_x3f(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Response_Builder_extension___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Extensions_compareName___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Response_Builder_extension___redArg___closed__0 = (const lean_object*)&l_Std_Http_Response_Builder_extension___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_extension___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_extension(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_body___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_body___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_body(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_body___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_build___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_build___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_build(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_build___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Http_Response_ok___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_ok___closed__0;
LEAN_EXPORT lean_object* l_Std_Http_Response_ok;
LEAN_EXPORT lean_object* l_Std_Http_Response_withStatus(lean_object*);
static lean_once_cell_t l_Std_Http_Response_notFound___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_notFound___closed__0;
LEAN_EXPORT lean_object* l_Std_Http_Response_notFound;
static lean_once_cell_t l_Std_Http_Response_internalServerError___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_internalServerError___closed__0;
LEAN_EXPORT lean_object* l_Std_Http_Response_internalServerError;
static lean_once_cell_t l_Std_Http_Response_badRequest___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_badRequest___closed__0;
LEAN_EXPORT lean_object* l_Std_Http_Response_badRequest;
static lean_once_cell_t l_Std_Http_Response_created___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_created___closed__0;
LEAN_EXPORT lean_object* l_Std_Http_Response_created;
static lean_once_cell_t l_Std_Http_Response_accepted___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_accepted___closed__0;
LEAN_EXPORT lean_object* l_Std_Http_Response_accepted;
static lean_once_cell_t l_Std_Http_Response_unauthorized___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_unauthorized___closed__0;
LEAN_EXPORT lean_object* l_Std_Http_Response_unauthorized;
static lean_once_cell_t l_Std_Http_Response_forbidden___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_forbidden___closed__0;
LEAN_EXPORT lean_object* l_Std_Http_Response_forbidden;
static lean_once_cell_t l_Std_Http_Response_conflict___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_conflict___closed__0;
LEAN_EXPORT lean_object* l_Std_Http_Response_conflict;
static lean_once_cell_t l_Std_Http_Response_serviceUnavailable___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_serviceUnavailable___closed__0;
LEAN_EXPORT lean_object* l_Std_Http_Response_serviceUnavailable;
static lean_object* _init_l_Std_Http_Response_instInhabitedHead_default___closed__0(void){
_start:
{
lean_object* v___x_1_; uint8_t v___x_2_; lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_1_ = l_Std_Http_Headers_empty;
v___x_2_ = 1;
v___x_3_ = lean_box(4);
v___x_4_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4_, 0, v___x_3_);
lean_ctor_set(v___x_4_, 1, v___x_1_);
lean_ctor_set_uint8(v___x_4_, sizeof(void*)*2, v___x_2_);
return v___x_4_;
}
}
static lean_object* _init_l_Std_Http_Response_instInhabitedHead_default(void){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = lean_obj_once(&l_Std_Http_Response_instInhabitedHead_default___closed__0, &l_Std_Http_Response_instInhabitedHead_default___closed__0_once, _init_l_Std_Http_Response_instInhabitedHead_default___closed__0);
return v___x_5_;
}
}
static lean_object* _init_l_Std_Http_Response_instInhabitedHead(void){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = l_Std_Http_Response_instInhabitedHead_default;
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Http_Response_instReprHead_repr_spec__0(lean_object* v_a_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lean_nat_to_int(v_a_7_);
return v___x_8_;
}
}
static lean_object* _init_l_Std_Http_Response_instReprHead_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_22_ = lean_unsigned_to_nat(10u);
v___x_23_ = lean_nat_to_int(v___x_22_);
return v___x_23_;
}
}
static lean_object* _init_l_Std_Http_Response_instReprHead_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_30_ = lean_unsigned_to_nat(11u);
v___x_31_ = lean_nat_to_int(v___x_30_);
return v___x_31_;
}
}
static lean_object* _init_l_Std_Http_Response_instReprHead_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_36_ = ((lean_object*)(l_Std_Http_Response_instReprHead_repr___redArg___closed__0));
v___x_37_ = lean_string_length(v___x_36_);
return v___x_37_;
}
}
static lean_object* _init_l_Std_Http_Response_instReprHead_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_38_ = lean_obj_once(&l_Std_Http_Response_instReprHead_repr___redArg___closed__16, &l_Std_Http_Response_instReprHead_repr___redArg___closed__16_once, _init_l_Std_Http_Response_instReprHead_repr___redArg___closed__16);
v___x_39_ = lean_nat_to_int(v___x_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instReprHead_repr___redArg(lean_object* v_x_44_){
_start:
{
lean_object* v_status_45_; uint8_t v_version_46_; lean_object* v_headers_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; uint8_t v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v_status_45_ = lean_ctor_get(v_x_44_, 0);
lean_inc(v_status_45_);
v_version_46_ = lean_ctor_get_uint8(v_x_44_, sizeof(void*)*2);
v_headers_47_ = lean_ctor_get(v_x_44_, 1);
lean_inc_ref(v_headers_47_);
lean_dec_ref(v_x_44_);
v___x_48_ = ((lean_object*)(l_Std_Http_Response_instReprHead_repr___redArg___closed__5));
v___x_49_ = ((lean_object*)(l_Std_Http_Response_instReprHead_repr___redArg___closed__6));
v___x_50_ = lean_obj_once(&l_Std_Http_Response_instReprHead_repr___redArg___closed__7, &l_Std_Http_Response_instReprHead_repr___redArg___closed__7_once, _init_l_Std_Http_Response_instReprHead_repr___redArg___closed__7);
v___x_51_ = lean_unsigned_to_nat(0u);
v___x_52_ = l_Std_Http_instReprStatus_repr(v_status_45_, v___x_51_);
v___x_53_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_53_, 0, v___x_50_);
lean_ctor_set(v___x_53_, 1, v___x_52_);
v___x_54_ = 0;
v___x_55_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_55_, 0, v___x_53_);
lean_ctor_set_uint8(v___x_55_, sizeof(void*)*1, v___x_54_);
v___x_56_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_56_, 0, v___x_49_);
lean_ctor_set(v___x_56_, 1, v___x_55_);
v___x_57_ = ((lean_object*)(l_Std_Http_Response_instReprHead_repr___redArg___closed__9));
v___x_58_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_58_, 0, v___x_56_);
lean_ctor_set(v___x_58_, 1, v___x_57_);
v___x_59_ = lean_box(1);
v___x_60_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_60_, 0, v___x_58_);
lean_ctor_set(v___x_60_, 1, v___x_59_);
v___x_61_ = ((lean_object*)(l_Std_Http_Response_instReprHead_repr___redArg___closed__11));
v___x_62_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_62_, 0, v___x_60_);
lean_ctor_set(v___x_62_, 1, v___x_61_);
v___x_63_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_63_, 0, v___x_62_);
lean_ctor_set(v___x_63_, 1, v___x_48_);
v___x_64_ = lean_obj_once(&l_Std_Http_Response_instReprHead_repr___redArg___closed__12, &l_Std_Http_Response_instReprHead_repr___redArg___closed__12_once, _init_l_Std_Http_Response_instReprHead_repr___redArg___closed__12);
v___x_65_ = l_Std_Http_instReprVersion_repr(v_version_46_, v___x_51_);
v___x_66_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_66_, 0, v___x_64_);
lean_ctor_set(v___x_66_, 1, v___x_65_);
v___x_67_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_67_, 0, v___x_66_);
lean_ctor_set_uint8(v___x_67_, sizeof(void*)*1, v___x_54_);
v___x_68_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_68_, 0, v___x_63_);
lean_ctor_set(v___x_68_, 1, v___x_67_);
v___x_69_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_69_, 0, v___x_68_);
lean_ctor_set(v___x_69_, 1, v___x_57_);
v___x_70_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_70_, 0, v___x_69_);
lean_ctor_set(v___x_70_, 1, v___x_59_);
v___x_71_ = ((lean_object*)(l_Std_Http_Response_instReprHead_repr___redArg___closed__14));
v___x_72_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_72_, 0, v___x_70_);
lean_ctor_set(v___x_72_, 1, v___x_71_);
v___x_73_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
lean_ctor_set(v___x_73_, 1, v___x_48_);
v___x_74_ = l_Std_Http_instReprHeaders_repr___redArg(v_headers_47_);
v___x_75_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_75_, 0, v___x_64_);
lean_ctor_set(v___x_75_, 1, v___x_74_);
v___x_76_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_76_, 0, v___x_75_);
lean_ctor_set_uint8(v___x_76_, sizeof(void*)*1, v___x_54_);
v___x_77_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_77_, 0, v___x_73_);
lean_ctor_set(v___x_77_, 1, v___x_76_);
v___x_78_ = lean_obj_once(&l_Std_Http_Response_instReprHead_repr___redArg___closed__17, &l_Std_Http_Response_instReprHead_repr___redArg___closed__17_once, _init_l_Std_Http_Response_instReprHead_repr___redArg___closed__17);
v___x_79_ = ((lean_object*)(l_Std_Http_Response_instReprHead_repr___redArg___closed__18));
v___x_80_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_80_, 0, v___x_79_);
lean_ctor_set(v___x_80_, 1, v___x_77_);
v___x_81_ = ((lean_object*)(l_Std_Http_Response_instReprHead_repr___redArg___closed__19));
v___x_82_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_82_, 0, v___x_80_);
lean_ctor_set(v___x_82_, 1, v___x_81_);
v___x_83_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_83_, 0, v___x_78_);
lean_ctor_set(v___x_83_, 1, v___x_82_);
v___x_84_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_84_, 0, v___x_83_);
lean_ctor_set_uint8(v___x_84_, sizeof(void*)*1, v___x_54_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instReprHead_repr(lean_object* v_x_85_, lean_object* v_prec_86_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = l_Std_Http_Response_instReprHead_repr___redArg(v_x_85_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instReprHead_repr___boxed(lean_object* v_x_88_, lean_object* v_prec_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Std_Http_Response_instReprHead_repr(v_x_88_, v_prec_89_);
lean_dec(v_prec_89_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instInhabitedResponse_default___redArg(lean_object* v_inst_93_){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_94_ = lean_obj_once(&l_Std_Http_Response_instInhabitedHead_default___closed__0, &l_Std_Http_Response_instInhabitedHead_default___closed__0_once, _init_l_Std_Http_Response_instInhabitedHead_default___closed__0);
v___x_95_ = l_Std_Http_Extensions_empty;
v___x_96_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_96_, 0, v___x_94_);
lean_ctor_set(v___x_96_, 1, v_inst_93_);
lean_ctor_set(v___x_96_, 2, v___x_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instInhabitedResponse_default(lean_object* v_t_97_, lean_object* v_inst_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = l_Std_Http_instInhabitedResponse_default___redArg(v_inst_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instInhabitedResponse___redArg(lean_object* v_inst_100_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = l_Std_Http_instInhabitedResponse_default___redArg(v_inst_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instInhabitedResponse(lean_object* v_a_102_, lean_object* v_inst_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l_Std_Http_instInhabitedResponse_default___redArg(v_inst_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instToStringHead___lam__0(lean_object* v___x_105_, lean_object* v___x_106_, lean_object* v___x_107_, lean_object* v_fst_108_, lean_object* v___x_109_, uint32_t v___x_110_, lean_object* v___x_111_, lean_object* v_it_112_, lean_object* v_acc_113_, lean_object* v_hP_114_, lean_object* v_recur_115_){
_start:
{
lean_object* v_it_117_; lean_object* v_out_118_; lean_object* v_it_134_; lean_object* v_startInclusive_135_; lean_object* v_endExclusive_136_; 
if (lean_obj_tag(v_it_112_) == 0)
{
lean_object* v_currPos_148_; lean_object* v_searcher_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_171_; 
v_currPos_148_ = lean_ctor_get(v_it_112_, 0);
v_searcher_149_ = lean_ctor_get(v_it_112_, 1);
v_isSharedCheck_171_ = !lean_is_exclusive(v_it_112_);
if (v_isSharedCheck_171_ == 0)
{
v___x_151_ = v_it_112_;
v_isShared_152_ = v_isSharedCheck_171_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_searcher_149_);
lean_inc(v_currPos_148_);
lean_dec(v_it_112_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_171_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
uint8_t v___x_153_; 
v___x_153_ = lean_nat_dec_eq(v_searcher_149_, v___x_109_);
if (v___x_153_ == 0)
{
uint32_t v___x_154_; uint8_t v___x_155_; 
lean_dec(v___x_109_);
v___x_154_ = lean_string_utf8_get_fast(v_fst_108_, v_searcher_149_);
v___x_155_ = lean_uint32_dec_eq(v___x_154_, v___x_110_);
if (v___x_155_ == 0)
{
lean_object* v___x_156_; lean_object* v___x_158_; 
v___x_156_ = lean_string_utf8_next_fast(v_fst_108_, v_searcher_149_);
lean_dec(v_searcher_149_);
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 1, v___x_156_);
v___x_158_ = v___x_151_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_currPos_148_);
lean_ctor_set(v_reuseFailAlloc_160_, 1, v___x_156_);
v___x_158_ = v_reuseFailAlloc_160_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
lean_object* v___x_159_; 
v___x_159_ = lean_apply_4(v_recur_115_, v___x_158_, v_acc_113_, lean_box(0), lean_box(0));
return v___x_159_;
}
}
else
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v_slice_164_; lean_object* v_nextIt_166_; 
v___x_161_ = lean_string_utf8_next_fast(v_fst_108_, v_searcher_149_);
v___x_162_ = lean_nat_sub(v___x_161_, v_searcher_149_);
v___x_163_ = lean_nat_add(v_searcher_149_, v___x_162_);
lean_dec(v___x_162_);
v_slice_164_ = l_String_Slice_subslice_x21(v___x_111_, v_currPos_148_, v_searcher_149_);
lean_inc(v___x_163_);
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 1, v___x_163_);
lean_ctor_set(v___x_151_, 0, v___x_163_);
v_nextIt_166_ = v___x_151_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v___x_163_);
lean_ctor_set(v_reuseFailAlloc_169_, 1, v___x_163_);
v_nextIt_166_ = v_reuseFailAlloc_169_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
lean_object* v_startInclusive_167_; lean_object* v_endExclusive_168_; 
v_startInclusive_167_ = lean_ctor_get(v_slice_164_, 0);
lean_inc(v_startInclusive_167_);
v_endExclusive_168_ = lean_ctor_get(v_slice_164_, 1);
lean_inc(v_endExclusive_168_);
lean_dec_ref(v_slice_164_);
v_it_134_ = v_nextIt_166_;
v_startInclusive_135_ = v_startInclusive_167_;
v_endExclusive_136_ = v_endExclusive_168_;
goto v___jp_133_;
}
}
}
else
{
lean_object* v___x_170_; 
lean_del_object(v___x_151_);
lean_dec(v_searcher_149_);
v___x_170_ = lean_box(1);
v_it_134_ = v___x_170_;
v_startInclusive_135_ = v_currPos_148_;
v_endExclusive_136_ = v___x_109_;
goto v___jp_133_;
}
}
}
else
{
lean_dec_ref(v_recur_115_);
lean_dec(v___x_109_);
return v_acc_113_;
}
v___jp_116_:
{
if (lean_obj_tag(v_acc_113_) == 0)
{
lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_119_, 0, v_out_118_);
v___x_120_ = lean_apply_4(v_recur_115_, v_it_117_, v___x_119_, lean_box(0), lean_box(0));
return v___x_120_;
}
else
{
lean_object* v_val_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_132_; 
v_val_121_ = lean_ctor_get(v_acc_113_, 0);
v_isSharedCheck_132_ = !lean_is_exclusive(v_acc_113_);
if (v_isSharedCheck_132_ == 0)
{
v___x_123_ = v_acc_113_;
v_isShared_124_ = v_isSharedCheck_132_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_val_121_);
lean_dec(v_acc_113_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_132_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_129_; 
v___x_125_ = lean_string_utf8_extract_fast(v___x_105_, v___x_106_, v___x_107_);
v___x_126_ = lean_string_append(v_val_121_, v___x_125_);
lean_dec_ref(v___x_125_);
v___x_127_ = lean_string_append(v___x_126_, v_out_118_);
lean_dec_ref(v_out_118_);
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 0, v___x_127_);
v___x_129_ = v___x_123_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v___x_127_);
v___x_129_ = v_reuseFailAlloc_131_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
lean_object* v___x_130_; 
v___x_130_ = lean_apply_4(v_recur_115_, v_it_117_, v___x_129_, lean_box(0), lean_box(0));
return v___x_130_;
}
}
}
}
v___jp_133_:
{
lean_object* v___x_137_; uint32_t v___x_138_; uint32_t v___x_139_; uint8_t v___x_140_; 
v___x_137_ = lean_string_utf8_extract_fast(v_fst_108_, v_startInclusive_135_, v_endExclusive_136_);
lean_dec(v_endExclusive_136_);
lean_dec(v_startInclusive_135_);
v___x_138_ = lean_string_utf8_get(v___x_137_, v___x_106_);
v___x_139_ = 97;
v___x_140_ = lean_uint32_dec_le(v___x_139_, v___x_138_);
if (v___x_140_ == 0)
{
lean_object* v___x_141_; 
v___x_141_ = lean_string_utf8_set(v___x_137_, v___x_106_, v___x_138_);
v_it_117_ = v_it_134_;
v_out_118_ = v___x_141_;
goto v___jp_116_;
}
else
{
uint32_t v___x_142_; uint8_t v___x_143_; 
v___x_142_ = 122;
v___x_143_ = lean_uint32_dec_le(v___x_138_, v___x_142_);
if (v___x_143_ == 0)
{
lean_object* v___x_144_; 
v___x_144_ = lean_string_utf8_set(v___x_137_, v___x_106_, v___x_138_);
v_it_117_ = v_it_134_;
v_out_118_ = v___x_144_;
goto v___jp_116_;
}
else
{
uint32_t v___x_145_; uint32_t v___x_146_; lean_object* v___x_147_; 
v___x_145_ = 4294967264;
v___x_146_ = lean_uint32_add(v___x_138_, v___x_145_);
v___x_147_ = lean_string_utf8_set(v___x_137_, v___x_106_, v___x_146_);
v_it_117_ = v_it_134_;
v_out_118_ = v___x_147_;
goto v___jp_116_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instToStringHead___lam__0___boxed(lean_object* v___x_172_, lean_object* v___x_173_, lean_object* v___x_174_, lean_object* v_fst_175_, lean_object* v___x_176_, lean_object* v___x_177_, lean_object* v___x_178_, lean_object* v_it_179_, lean_object* v_acc_180_, lean_object* v_hP_181_, lean_object* v_recur_182_){
_start:
{
uint32_t v___x_729__boxed_183_; lean_object* v_res_184_; 
v___x_729__boxed_183_ = lean_unbox_uint32(v___x_177_);
lean_dec(v___x_177_);
v_res_184_ = l_Std_Http_Response_instToStringHead___lam__0(v___x_172_, v___x_173_, v___x_174_, v_fst_175_, v___x_176_, v___x_729__boxed_183_, v___x_178_, v_it_179_, v_acc_180_, v_hP_181_, v_recur_182_);
lean_dec_ref(v___x_178_);
lean_dec_ref(v_fst_175_);
lean_dec(v___x_174_);
lean_dec(v___x_173_);
lean_dec_ref(v___x_172_);
return v_res_184_;
}
}
static lean_object* _init_l_Std_Http_Response_instToStringHead___lam__1___closed__3(void){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_188_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__1___closed__2));
v___x_189_ = lean_string_utf8_byte_size(v___x_188_);
return v___x_189_;
}
}
static lean_object* _init_l_Std_Http_Response_instToStringHead___lam__1___boxed__const__1(void){
_start:
{
uint32_t v___x_191_; lean_object* v___x_192_; 
v___x_191_ = 45;
v___x_192_ = lean_box_uint32(v___x_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instToStringHead___lam__1(lean_object* v_x_193_){
_start:
{
lean_object* v_fst_194_; lean_object* v_snd_195_; lean_object* v___y_197_; lean_object* v___f_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v_it_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___f_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v_fst_194_ = lean_ctor_get(v_x_193_, 0);
lean_inc_n(v_fst_194_, 2);
v_snd_195_ = lean_ctor_get(v_x_193_, 1);
lean_inc(v_snd_195_);
lean_dec_ref(v_x_193_);
v___f_201_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__1___closed__1));
v___x_202_ = lean_unsigned_to_nat(0u);
v___x_203_ = lean_string_utf8_byte_size(v_fst_194_);
v___x_204_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_204_, 0, v_fst_194_);
lean_ctor_set(v___x_204_, 1, v___x_202_);
lean_ctor_set(v___x_204_, 2, v___x_203_);
lean_inc_ref(v___x_204_);
v_it_205_ = l_String_Slice_splitToSubslice___redArg(v___x_204_, v___f_201_);
v___x_206_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__1___closed__2));
v___x_207_ = lean_obj_once(&l_Std_Http_Response_instToStringHead___lam__1___closed__3, &l_Std_Http_Response_instToStringHead___lam__1___closed__3_once, _init_l_Std_Http_Response_instToStringHead___lam__1___closed__3);
v___x_208_ = l_Std_Http_Response_instToStringHead___lam__1___boxed__const__1;
v___f_209_ = lean_alloc_closure((void*)(l_Std_Http_Response_instToStringHead___lam__0___boxed), 11, 7);
lean_closure_set(v___f_209_, 0, v___x_206_);
lean_closure_set(v___f_209_, 1, v___x_202_);
lean_closure_set(v___f_209_, 2, v___x_207_);
lean_closure_set(v___f_209_, 3, v_fst_194_);
lean_closure_set(v___f_209_, 4, v___x_203_);
lean_closure_set(v___f_209_, 5, v___x_208_);
lean_closure_set(v___f_209_, 6, v___x_204_);
v___x_210_ = lean_box(0);
v___x_211_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_209_, v_it_205_, v___x_210_, lean_box(0));
if (lean_obj_tag(v___x_211_) == 0)
{
lean_object* v___x_212_; 
v___x_212_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__1___closed__4));
v___y_197_ = v___x_212_;
goto v___jp_196_;
}
else
{
lean_object* v_val_213_; 
v_val_213_ = lean_ctor_get(v___x_211_, 0);
lean_inc(v_val_213_);
lean_dec_ref_known(v___x_211_, 1);
v___y_197_ = v_val_213_;
goto v___jp_196_;
}
v___jp_196_:
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_198_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__1___closed__0));
v___x_199_ = lean_string_append(v___y_197_, v___x_198_);
v___x_200_ = lean_string_append(v___x_199_, v_snd_195_);
lean_dec(v_snd_195_);
return v___x_200_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instToStringHead___lam__2(lean_object* v___f_239_, lean_object* v_r_240_){
_start:
{
lean_object* v_status_241_; uint8_t v_version_242_; lean_object* v_headers_243_; lean_object* v___y_245_; 
v_status_241_ = lean_ctor_get(v_r_240_, 0);
lean_inc(v_status_241_);
v_version_242_ = lean_ctor_get_uint8(v_r_240_, sizeof(void*)*2);
v_headers_243_ = lean_ctor_get(v_r_240_, 1);
lean_inc_ref(v_headers_243_);
lean_dec_ref(v_r_240_);
switch(v_version_242_)
{
case 0:
{
lean_object* v___x_266_; 
v___x_266_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__12));
v___y_245_ = v___x_266_;
goto v___jp_244_;
}
case 1:
{
lean_object* v___x_267_; 
v___x_267_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__13));
v___y_245_ = v___x_267_;
goto v___jp_244_;
}
case 2:
{
lean_object* v___x_268_; 
v___x_268_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__14));
v___y_245_ = v___x_268_;
goto v___jp_244_;
}
default: 
{
lean_object* v___x_269_; 
v___x_269_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__15));
v___y_245_ = v___x_269_;
goto v___jp_244_;
}
}
v___jp_244_:
{
lean_object* v_entries_246_; lean_object* v___x_247_; lean_object* v___x_248_; uint16_t v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; size_t v_sz_259_; size_t v___x_260_; lean_object* v_pairs_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v_entries_246_ = lean_ctor_get(v_headers_243_, 0);
lean_inc_ref(v_entries_246_);
lean_dec_ref(v_headers_243_);
v___x_247_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__0));
lean_inc_ref(v___y_245_);
v___x_248_ = lean_string_append(v___y_245_, v___x_247_);
v___x_249_ = l_Std_Http_Status_toCode(v_status_241_);
v___x_250_ = lean_uint16_to_nat(v___x_249_);
v___x_251_ = l_Nat_reprFast(v___x_250_);
v___x_252_ = lean_string_append(v___x_248_, v___x_251_);
lean_dec_ref(v___x_251_);
v___x_253_ = lean_string_append(v___x_252_, v___x_247_);
v___x_254_ = l_Std_Http_Status_reasonPhrase(v_status_241_);
lean_dec(v_status_241_);
v___x_255_ = lean_string_append(v___x_253_, v___x_254_);
lean_dec_ref(v___x_254_);
v___x_256_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__1));
v___x_257_ = lean_string_append(v___x_255_, v___x_256_);
v___x_258_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__11));
v_sz_259_ = lean_array_size(v_entries_246_);
v___x_260_ = ((size_t)0ULL);
v_pairs_261_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_258_, v___f_239_, v_sz_259_, v___x_260_, v_entries_246_);
v___x_262_ = lean_array_to_list(v_pairs_261_);
v___x_263_ = l_String_intercalate(v___x_256_, v___x_262_);
v___x_264_ = lean_string_append(v___x_257_, v___x_263_);
lean_dec_ref(v___x_263_);
v___x_265_ = lean_string_append(v___x_264_, v___x_256_);
return v___x_265_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instEncodeV11Head___lam__0(lean_object* v___x_274_, lean_object* v___x_275_, lean_object* v___x_276_, lean_object* v_name_277_, lean_object* v___x_278_, uint32_t v___x_279_, lean_object* v___x_280_, lean_object* v_it_281_, lean_object* v_acc_282_, lean_object* v_hP_283_, lean_object* v_recur_284_){
_start:
{
lean_object* v_it_286_; lean_object* v_out_287_; lean_object* v_it_303_; lean_object* v_startInclusive_304_; lean_object* v_endExclusive_305_; 
if (lean_obj_tag(v_it_281_) == 0)
{
lean_object* v_currPos_317_; lean_object* v_searcher_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_340_; 
v_currPos_317_ = lean_ctor_get(v_it_281_, 0);
v_searcher_318_ = lean_ctor_get(v_it_281_, 1);
v_isSharedCheck_340_ = !lean_is_exclusive(v_it_281_);
if (v_isSharedCheck_340_ == 0)
{
v___x_320_ = v_it_281_;
v_isShared_321_ = v_isSharedCheck_340_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_searcher_318_);
lean_inc(v_currPos_317_);
lean_dec(v_it_281_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_340_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
uint8_t v___x_322_; 
v___x_322_ = lean_nat_dec_eq(v_searcher_318_, v___x_278_);
if (v___x_322_ == 0)
{
uint32_t v___x_323_; uint8_t v___x_324_; 
lean_dec(v___x_278_);
v___x_323_ = lean_string_utf8_get_fast(v_name_277_, v_searcher_318_);
v___x_324_ = lean_uint32_dec_eq(v___x_323_, v___x_279_);
if (v___x_324_ == 0)
{
lean_object* v___x_325_; lean_object* v___x_327_; 
v___x_325_ = lean_string_utf8_next_fast(v_name_277_, v_searcher_318_);
lean_dec(v_searcher_318_);
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 1, v___x_325_);
v___x_327_ = v___x_320_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_currPos_317_);
lean_ctor_set(v_reuseFailAlloc_329_, 1, v___x_325_);
v___x_327_ = v_reuseFailAlloc_329_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
lean_object* v___x_328_; 
v___x_328_ = lean_apply_4(v_recur_284_, v___x_327_, v_acc_282_, lean_box(0), lean_box(0));
return v___x_328_;
}
}
else
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v_slice_333_; lean_object* v_nextIt_335_; 
v___x_330_ = lean_string_utf8_next_fast(v_name_277_, v_searcher_318_);
v___x_331_ = lean_nat_sub(v___x_330_, v_searcher_318_);
v___x_332_ = lean_nat_add(v_searcher_318_, v___x_331_);
lean_dec(v___x_331_);
v_slice_333_ = l_String_Slice_subslice_x21(v___x_280_, v_currPos_317_, v_searcher_318_);
lean_inc(v___x_332_);
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 1, v___x_332_);
lean_ctor_set(v___x_320_, 0, v___x_332_);
v_nextIt_335_ = v___x_320_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v___x_332_);
lean_ctor_set(v_reuseFailAlloc_338_, 1, v___x_332_);
v_nextIt_335_ = v_reuseFailAlloc_338_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
lean_object* v_startInclusive_336_; lean_object* v_endExclusive_337_; 
v_startInclusive_336_ = lean_ctor_get(v_slice_333_, 0);
lean_inc(v_startInclusive_336_);
v_endExclusive_337_ = lean_ctor_get(v_slice_333_, 1);
lean_inc(v_endExclusive_337_);
lean_dec_ref(v_slice_333_);
v_it_303_ = v_nextIt_335_;
v_startInclusive_304_ = v_startInclusive_336_;
v_endExclusive_305_ = v_endExclusive_337_;
goto v___jp_302_;
}
}
}
else
{
lean_object* v___x_339_; 
lean_del_object(v___x_320_);
lean_dec(v_searcher_318_);
v___x_339_ = lean_box(1);
v_it_303_ = v___x_339_;
v_startInclusive_304_ = v_currPos_317_;
v_endExclusive_305_ = v___x_278_;
goto v___jp_302_;
}
}
}
else
{
lean_dec_ref(v_recur_284_);
lean_dec(v___x_278_);
return v_acc_282_;
}
v___jp_285_:
{
if (lean_obj_tag(v_acc_282_) == 0)
{
lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_288_, 0, v_out_287_);
v___x_289_ = lean_apply_4(v_recur_284_, v_it_286_, v___x_288_, lean_box(0), lean_box(0));
return v___x_289_;
}
else
{
lean_object* v_val_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_301_; 
v_val_290_ = lean_ctor_get(v_acc_282_, 0);
v_isSharedCheck_301_ = !lean_is_exclusive(v_acc_282_);
if (v_isSharedCheck_301_ == 0)
{
v___x_292_ = v_acc_282_;
v_isShared_293_ = v_isSharedCheck_301_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_val_290_);
lean_dec(v_acc_282_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_301_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_298_; 
v___x_294_ = lean_string_utf8_extract_fast(v___x_274_, v___x_275_, v___x_276_);
v___x_295_ = lean_string_append(v_val_290_, v___x_294_);
lean_dec_ref(v___x_294_);
v___x_296_ = lean_string_append(v___x_295_, v_out_287_);
lean_dec_ref(v_out_287_);
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 0, v___x_296_);
v___x_298_ = v___x_292_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v___x_296_);
v___x_298_ = v_reuseFailAlloc_300_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
lean_object* v___x_299_; 
v___x_299_ = lean_apply_4(v_recur_284_, v_it_286_, v___x_298_, lean_box(0), lean_box(0));
return v___x_299_;
}
}
}
}
v___jp_302_:
{
lean_object* v___x_306_; uint32_t v___x_307_; uint32_t v___x_308_; uint8_t v___x_309_; 
v___x_306_ = lean_string_utf8_extract_fast(v_name_277_, v_startInclusive_304_, v_endExclusive_305_);
lean_dec(v_endExclusive_305_);
lean_dec(v_startInclusive_304_);
v___x_307_ = lean_string_utf8_get(v___x_306_, v___x_275_);
v___x_308_ = 97;
v___x_309_ = lean_uint32_dec_le(v___x_308_, v___x_307_);
if (v___x_309_ == 0)
{
lean_object* v___x_310_; 
v___x_310_ = lean_string_utf8_set(v___x_306_, v___x_275_, v___x_307_);
v_it_286_ = v_it_303_;
v_out_287_ = v___x_310_;
goto v___jp_285_;
}
else
{
uint32_t v___x_311_; uint8_t v___x_312_; 
v___x_311_ = 122;
v___x_312_ = lean_uint32_dec_le(v___x_307_, v___x_311_);
if (v___x_312_ == 0)
{
lean_object* v___x_313_; 
v___x_313_ = lean_string_utf8_set(v___x_306_, v___x_275_, v___x_307_);
v_it_286_ = v_it_303_;
v_out_287_ = v___x_313_;
goto v___jp_285_;
}
else
{
uint32_t v___x_314_; uint32_t v___x_315_; lean_object* v___x_316_; 
v___x_314_ = 4294967264;
v___x_315_ = lean_uint32_add(v___x_307_, v___x_314_);
v___x_316_ = lean_string_utf8_set(v___x_306_, v___x_275_, v___x_315_);
v_it_286_ = v_it_303_;
v_out_287_ = v___x_316_;
goto v___jp_285_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instEncodeV11Head___lam__0___boxed(lean_object* v___x_341_, lean_object* v___x_342_, lean_object* v___x_343_, lean_object* v_name_344_, lean_object* v___x_345_, lean_object* v___x_346_, lean_object* v___x_347_, lean_object* v_it_348_, lean_object* v_acc_349_, lean_object* v_hP_350_, lean_object* v_recur_351_){
_start:
{
uint32_t v___x_1176__boxed_352_; lean_object* v_res_353_; 
v___x_1176__boxed_352_ = lean_unbox_uint32(v___x_346_);
lean_dec(v___x_346_);
v_res_353_ = l_Std_Http_Response_instEncodeV11Head___lam__0(v___x_341_, v___x_342_, v___x_343_, v_name_344_, v___x_345_, v___x_1176__boxed_352_, v___x_347_, v_it_348_, v_acc_349_, v_hP_350_, v_recur_351_);
lean_dec_ref(v___x_347_);
lean_dec_ref(v_name_344_);
lean_dec(v___x_343_);
lean_dec(v___x_342_);
lean_dec_ref(v___x_341_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instEncodeV11Head___lam__1(lean_object* v_buf_354_, lean_object* v_name_355_, lean_object* v_value_356_){
_start:
{
lean_object* v___y_358_; lean_object* v___f_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v_it_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___f_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___f_377_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__1___closed__1));
v___x_378_ = lean_unsigned_to_nat(0u);
v___x_379_ = lean_string_utf8_byte_size(v_name_355_);
lean_inc_ref(v_name_355_);
v___x_380_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_380_, 0, v_name_355_);
lean_ctor_set(v___x_380_, 1, v___x_378_);
lean_ctor_set(v___x_380_, 2, v___x_379_);
lean_inc_ref(v___x_380_);
v_it_381_ = l_String_Slice_splitToSubslice___redArg(v___x_380_, v___f_377_);
v___x_382_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__1___closed__2));
v___x_383_ = lean_obj_once(&l_Std_Http_Response_instToStringHead___lam__1___closed__3, &l_Std_Http_Response_instToStringHead___lam__1___closed__3_once, _init_l_Std_Http_Response_instToStringHead___lam__1___closed__3);
v___x_384_ = l_Std_Http_Response_instToStringHead___lam__1___boxed__const__1;
v___f_385_ = lean_alloc_closure((void*)(l_Std_Http_Response_instEncodeV11Head___lam__0___boxed), 11, 7);
lean_closure_set(v___f_385_, 0, v___x_382_);
lean_closure_set(v___f_385_, 1, v___x_378_);
lean_closure_set(v___f_385_, 2, v___x_383_);
lean_closure_set(v___f_385_, 3, v_name_355_);
lean_closure_set(v___f_385_, 4, v___x_379_);
lean_closure_set(v___f_385_, 5, v___x_384_);
lean_closure_set(v___f_385_, 6, v___x_380_);
v___x_386_ = lean_box(0);
v___x_387_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_385_, v_it_381_, v___x_386_, lean_box(0));
if (lean_obj_tag(v___x_387_) == 0)
{
lean_object* v___x_388_; 
v___x_388_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__1___closed__4));
v___y_358_ = v___x_388_;
goto v___jp_357_;
}
else
{
lean_object* v_val_389_; 
v_val_389_ = lean_ctor_get(v___x_387_, 0);
lean_inc(v_val_389_);
lean_dec_ref_known(v___x_387_, 1);
v___y_358_ = v_val_389_;
goto v___jp_357_;
}
v___jp_357_:
{
lean_object* v_data_359_; lean_object* v_size_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_376_; 
v_data_359_ = lean_ctor_get(v_buf_354_, 0);
v_size_360_ = lean_ctor_get(v_buf_354_, 1);
v_isSharedCheck_376_ = !lean_is_exclusive(v_buf_354_);
if (v_isSharedCheck_376_ == 0)
{
v___x_362_ = v_buf_354_;
v_isShared_363_ = v_isSharedCheck_376_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_size_360_);
lean_inc(v_data_359_);
lean_dec(v_buf_354_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_376_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_374_; 
v___x_364_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__1___closed__0));
v___x_365_ = lean_string_append(v___y_358_, v___x_364_);
v___x_366_ = lean_string_append(v___x_365_, v_value_356_);
v___x_367_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__1));
v___x_368_ = lean_string_append(v___x_366_, v___x_367_);
v___x_369_ = lean_string_to_utf8(v___x_368_);
lean_dec_ref(v___x_368_);
lean_inc_ref(v___x_369_);
v___x_370_ = lean_array_push(v_data_359_, v___x_369_);
v___x_371_ = lean_byte_array_size(v___x_369_);
lean_dec_ref(v___x_369_);
v___x_372_ = lean_nat_add(v_size_360_, v___x_371_);
lean_dec(v_size_360_);
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 1, v___x_372_);
lean_ctor_set(v___x_362_, 0, v___x_370_);
v___x_374_ = v___x_362_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v___x_370_);
lean_ctor_set(v_reuseFailAlloc_375_, 1, v___x_372_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instEncodeV11Head___lam__1___boxed(lean_object* v_buf_390_, lean_object* v_name_391_, lean_object* v_value_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Std_Http_Response_instEncodeV11Head___lam__1(v_buf_390_, v_name_391_, v_value_392_);
lean_dec_ref(v_value_392_);
return v_res_393_;
}
}
static uint8_t _init_l_Std_Http_Response_instEncodeV11Head___lam__2___closed__0(void){
_start:
{
uint32_t v___x_394_; uint8_t v___x_395_; 
v___x_394_ = 32;
v___x_395_ = lean_uint32_to_uint8(v___x_394_);
return v___x_395_;
}
}
static lean_object* _init_l_Std_Http_Response_instEncodeV11Head___lam__2___closed__1(void){
_start:
{
uint8_t v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_396_ = lean_uint8_once(&l_Std_Http_Response_instEncodeV11Head___lam__2___closed__0, &l_Std_Http_Response_instEncodeV11Head___lam__2___closed__0_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__2___closed__0);
v___x_397_ = lean_unsigned_to_nat(1u);
v___x_398_ = lean_mk_empty_array_with_capacity(v___x_397_);
v___x_399_ = lean_box(v___x_396_);
v___x_400_ = lean_array_push(v___x_398_, v___x_399_);
v___x_401_ = lean_byte_array_mk(v___x_400_);
return v___x_401_;
}
}
static lean_object* _init_l_Std_Http_Response_instEncodeV11Head___lam__2___closed__2(void){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_402_ = lean_obj_once(&l_Std_Http_Response_instEncodeV11Head___lam__2___closed__1, &l_Std_Http_Response_instEncodeV11Head___lam__2___closed__1_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__2___closed__1);
v___x_403_ = lean_byte_array_size(v___x_402_);
return v___x_403_;
}
}
static lean_object* _init_l_Std_Http_Response_instEncodeV11Head___lam__2___closed__3(void){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_404_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__1));
v___x_405_ = lean_string_to_utf8(v___x_404_);
return v___x_405_;
}
}
static lean_object* _init_l_Std_Http_Response_instEncodeV11Head___lam__2___closed__4(void){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_406_ = lean_obj_once(&l_Std_Http_Response_instEncodeV11Head___lam__2___closed__3, &l_Std_Http_Response_instEncodeV11Head___lam__2___closed__3_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__2___closed__3);
v___x_407_ = lean_byte_array_size(v___x_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instEncodeV11Head___lam__2(lean_object* v___f_408_, lean_object* v_buffer_409_, lean_object* v_r_410_){
_start:
{
lean_object* v_status_411_; uint8_t v_version_412_; lean_object* v_headers_413_; lean_object* v___y_415_; 
v_status_411_ = lean_ctor_get(v_r_410_, 0);
v_version_412_ = lean_ctor_get_uint8(v_r_410_, sizeof(void*)*2);
v_headers_413_ = lean_ctor_get(v_r_410_, 1);
switch(v_version_412_)
{
case 0:
{
lean_object* v___x_463_; 
v___x_463_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__12));
v___y_415_ = v___x_463_;
goto v___jp_414_;
}
case 1:
{
lean_object* v___x_464_; 
v___x_464_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__13));
v___y_415_ = v___x_464_;
goto v___jp_414_;
}
case 2:
{
lean_object* v___x_465_; 
v___x_465_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__14));
v___y_415_ = v___x_465_;
goto v___jp_414_;
}
default: 
{
lean_object* v___x_466_; 
v___x_466_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__15));
v___y_415_ = v___x_466_;
goto v___jp_414_;
}
}
v___jp_414_:
{
lean_object* v_data_416_; lean_object* v_size_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_462_; 
v_data_416_ = lean_ctor_get(v_buffer_409_, 0);
v_size_417_ = lean_ctor_get(v_buffer_409_, 1);
v_isSharedCheck_462_ = !lean_is_exclusive(v_buffer_409_);
if (v_isSharedCheck_462_ == 0)
{
v___x_419_ = v_buffer_409_;
v_isShared_420_ = v_isSharedCheck_462_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_size_417_);
lean_inc(v_data_416_);
lean_dec(v_buffer_409_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_462_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; uint16_t v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v_buffer_448_; 
v___x_421_ = lean_string_to_utf8(v___y_415_);
lean_inc_ref(v___x_421_);
v___x_422_ = lean_array_push(v_data_416_, v___x_421_);
v___x_423_ = lean_byte_array_size(v___x_421_);
lean_dec_ref(v___x_421_);
v___x_424_ = lean_nat_add(v_size_417_, v___x_423_);
lean_dec(v_size_417_);
v___x_425_ = lean_obj_once(&l_Std_Http_Response_instEncodeV11Head___lam__2___closed__1, &l_Std_Http_Response_instEncodeV11Head___lam__2___closed__1_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__2___closed__1);
v___x_426_ = lean_array_push(v___x_422_, v___x_425_);
v___x_427_ = lean_obj_once(&l_Std_Http_Response_instEncodeV11Head___lam__2___closed__2, &l_Std_Http_Response_instEncodeV11Head___lam__2___closed__2_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__2___closed__2);
v___x_428_ = lean_nat_add(v___x_424_, v___x_427_);
lean_dec(v___x_424_);
v___x_429_ = l_Std_Http_Status_toCode(v_status_411_);
v___x_430_ = lean_uint16_to_nat(v___x_429_);
v___x_431_ = l_Nat_reprFast(v___x_430_);
v___x_432_ = lean_string_to_utf8(v___x_431_);
lean_dec_ref(v___x_431_);
lean_inc_ref(v___x_432_);
v___x_433_ = lean_array_push(v___x_426_, v___x_432_);
v___x_434_ = lean_byte_array_size(v___x_432_);
lean_dec_ref(v___x_432_);
v___x_435_ = lean_nat_add(v___x_428_, v___x_434_);
lean_dec(v___x_428_);
v___x_436_ = lean_array_push(v___x_433_, v___x_425_);
v___x_437_ = lean_nat_add(v___x_435_, v___x_427_);
lean_dec(v___x_435_);
v___x_438_ = l_Std_Http_Status_reasonPhrase(v_status_411_);
v___x_439_ = lean_string_to_utf8(v___x_438_);
lean_dec_ref(v___x_438_);
lean_inc_ref(v___x_439_);
v___x_440_ = lean_array_push(v___x_436_, v___x_439_);
v___x_441_ = lean_byte_array_size(v___x_439_);
lean_dec_ref(v___x_439_);
v___x_442_ = lean_nat_add(v___x_437_, v___x_441_);
lean_dec(v___x_437_);
v___x_443_ = lean_obj_once(&l_Std_Http_Response_instEncodeV11Head___lam__2___closed__3, &l_Std_Http_Response_instEncodeV11Head___lam__2___closed__3_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__2___closed__3);
v___x_444_ = lean_array_push(v___x_440_, v___x_443_);
v___x_445_ = lean_obj_once(&l_Std_Http_Response_instEncodeV11Head___lam__2___closed__4, &l_Std_Http_Response_instEncodeV11Head___lam__2___closed__4_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__2___closed__4);
v___x_446_ = lean_nat_add(v___x_442_, v___x_445_);
lean_dec(v___x_442_);
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 1, v___x_446_);
lean_ctor_set(v___x_419_, 0, v___x_444_);
v_buffer_448_ = v___x_419_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v___x_444_);
lean_ctor_set(v_reuseFailAlloc_461_, 1, v___x_446_);
v_buffer_448_ = v_reuseFailAlloc_461_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
lean_object* v_buffer_449_; lean_object* v_data_450_; lean_object* v_size_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_460_; 
v_buffer_449_ = l_Std_Http_Headers_fold___redArg(v_headers_413_, v_buffer_448_, v___f_408_);
v_data_450_ = lean_ctor_get(v_buffer_449_, 0);
v_size_451_ = lean_ctor_get(v_buffer_449_, 1);
v_isSharedCheck_460_ = !lean_is_exclusive(v_buffer_449_);
if (v_isSharedCheck_460_ == 0)
{
v___x_453_ = v_buffer_449_;
v_isShared_454_ = v_isSharedCheck_460_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_size_451_);
lean_inc(v_data_450_);
lean_dec(v_buffer_449_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_460_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_458_; 
v___x_455_ = lean_array_push(v_data_450_, v___x_443_);
v___x_456_ = lean_nat_add(v_size_451_, v___x_445_);
lean_dec(v_size_451_);
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 1, v___x_456_);
lean_ctor_set(v___x_453_, 0, v___x_455_);
v___x_458_ = v___x_453_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v___x_455_);
lean_ctor_set(v_reuseFailAlloc_459_, 1, v___x_456_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instEncodeV11Head___lam__2___boxed(lean_object* v___f_467_, lean_object* v_buffer_468_, lean_object* v_r_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_Std_Http_Response_instEncodeV11Head___lam__2(v___f_467_, v_buffer_468_, v_r_469_);
lean_dec_ref(v_r_469_);
return v_res_470_;
}
}
static lean_object* _init_l_Std_Http_Response_new___closed__0(void){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_475_ = l_Std_Http_Extensions_empty;
v___x_476_ = lean_obj_once(&l_Std_Http_Response_instInhabitedHead_default___closed__0, &l_Std_Http_Response_instInhabitedHead_default___closed__0_once, _init_l_Std_Http_Response_instInhabitedHead_default___closed__0);
v___x_477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_477_, 0, v___x_476_);
lean_ctor_set(v___x_477_, 1, v___x_475_);
return v___x_477_;
}
}
static lean_object* _init_l_Std_Http_Response_new(void){
_start:
{
lean_object* v___x_478_; 
v___x_478_ = lean_obj_once(&l_Std_Http_Response_new___closed__0, &l_Std_Http_Response_new___closed__0_once, _init_l_Std_Http_Response_new___closed__0);
return v___x_478_;
}
}
static lean_object* _init_l_Std_Http_Response_Builder_new(void){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = lean_obj_once(&l_Std_Http_Response_new___closed__0, &l_Std_Http_Response_new___closed__0_once, _init_l_Std_Http_Response_new___closed__0);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_status(lean_object* v_builder_480_, lean_object* v_status_481_){
_start:
{
lean_object* v_line_482_; lean_object* v_extensions_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_500_; 
v_line_482_ = lean_ctor_get(v_builder_480_, 0);
v_extensions_483_ = lean_ctor_get(v_builder_480_, 1);
v_isSharedCheck_500_ = !lean_is_exclusive(v_builder_480_);
if (v_isSharedCheck_500_ == 0)
{
v___x_485_ = v_builder_480_;
v_isShared_486_ = v_isSharedCheck_500_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_extensions_483_);
lean_inc(v_line_482_);
lean_dec(v_builder_480_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_500_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
uint8_t v_version_487_; lean_object* v_headers_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_498_; 
v_version_487_ = lean_ctor_get_uint8(v_line_482_, sizeof(void*)*2);
v_headers_488_ = lean_ctor_get(v_line_482_, 1);
v_isSharedCheck_498_ = !lean_is_exclusive(v_line_482_);
if (v_isSharedCheck_498_ == 0)
{
lean_object* v_unused_499_; 
v_unused_499_ = lean_ctor_get(v_line_482_, 0);
lean_dec(v_unused_499_);
v___x_490_ = v_line_482_;
v_isShared_491_ = v_isSharedCheck_498_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_headers_488_);
lean_dec(v_line_482_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_498_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_493_; 
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 0, v_status_481_);
v___x_493_ = v___x_490_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_status_481_);
lean_ctor_set(v_reuseFailAlloc_497_, 1, v_headers_488_);
lean_ctor_set_uint8(v_reuseFailAlloc_497_, sizeof(void*)*2, v_version_487_);
v___x_493_ = v_reuseFailAlloc_497_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
lean_object* v___x_495_; 
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 0, v___x_493_);
v___x_495_ = v___x_485_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v___x_493_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v_extensions_483_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_headers(lean_object* v_builder_501_, lean_object* v_headers_502_){
_start:
{
lean_object* v_line_503_; lean_object* v_extensions_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_521_; 
v_line_503_ = lean_ctor_get(v_builder_501_, 0);
v_extensions_504_ = lean_ctor_get(v_builder_501_, 1);
v_isSharedCheck_521_ = !lean_is_exclusive(v_builder_501_);
if (v_isSharedCheck_521_ == 0)
{
v___x_506_ = v_builder_501_;
v_isShared_507_ = v_isSharedCheck_521_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_extensions_504_);
lean_inc(v_line_503_);
lean_dec(v_builder_501_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_521_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v_status_508_; uint8_t v_version_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_519_; 
v_status_508_ = lean_ctor_get(v_line_503_, 0);
v_version_509_ = lean_ctor_get_uint8(v_line_503_, sizeof(void*)*2);
v_isSharedCheck_519_ = !lean_is_exclusive(v_line_503_);
if (v_isSharedCheck_519_ == 0)
{
lean_object* v_unused_520_; 
v_unused_520_ = lean_ctor_get(v_line_503_, 1);
lean_dec(v_unused_520_);
v___x_511_ = v_line_503_;
v_isShared_512_ = v_isSharedCheck_519_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_status_508_);
lean_dec(v_line_503_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_519_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_514_; 
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 1, v_headers_502_);
v___x_514_ = v___x_511_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_status_508_);
lean_ctor_set(v_reuseFailAlloc_518_, 1, v_headers_502_);
lean_ctor_set_uint8(v_reuseFailAlloc_518_, sizeof(void*)*2, v_version_509_);
v___x_514_ = v_reuseFailAlloc_518_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
lean_object* v___x_516_; 
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 0, v___x_514_);
v___x_516_ = v___x_506_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_514_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v_extensions_504_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_header___lam__0(lean_object* v_i_522_, lean_object* v_x_523_){
_start:
{
if (lean_obj_tag(v_x_523_) == 0)
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_524_ = lean_unsigned_to_nat(1u);
v___x_525_ = lean_mk_empty_array_with_capacity(v___x_524_);
v___x_526_ = lean_array_push(v___x_525_, v_i_522_);
v___x_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
return v___x_527_;
}
else
{
lean_object* v_val_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_536_; 
v_val_528_ = lean_ctor_get(v_x_523_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v_x_523_);
if (v_isSharedCheck_536_ == 0)
{
v___x_530_ = v_x_523_;
v_isShared_531_ = v_isSharedCheck_536_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_val_528_);
lean_dec(v_x_523_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_536_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_532_; lean_object* v___x_534_; 
v___x_532_ = lean_array_push(v_val_528_, v_i_522_);
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 0, v___x_532_);
v___x_534_ = v___x_530_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_532_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Http_Response_Builder_header_spec__0_spec__0___redArg(lean_object* v_m_537_, lean_object* v_query_538_, lean_object* v_x_539_, lean_object* v_x_540_, lean_object* v_x_541_){
_start:
{
lean_object* v_zero_542_; uint8_t v_isZero_543_; 
v_zero_542_ = lean_unsigned_to_nat(0u);
v_isZero_543_ = lean_nat_dec_eq(v_x_540_, v_zero_542_);
if (v_isZero_543_ == 1)
{
lean_dec(v_x_541_);
lean_dec(v_x_540_);
if (lean_obj_tag(v_x_539_) == 0)
{
lean_object* v___x_544_; 
v___x_544_ = lean_box(2);
return v___x_544_;
}
else
{
lean_object* v_val_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_552_; 
v_val_545_ = lean_ctor_get(v_x_539_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v_x_539_);
if (v_isSharedCheck_552_ == 0)
{
v___x_547_ = v_x_539_;
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_val_545_);
lean_dec(v_x_539_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_550_; 
if (v_isShared_548_ == 0)
{
v___x_550_ = v___x_547_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_val_545_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
}
else
{
lean_object* v_keyArray_553_; lean_object* v_valueArray_554_; lean_object* v___x_555_; uint8_t v_isSome_556_; 
v_keyArray_553_ = lean_ctor_get(v_m_537_, 1);
v_valueArray_554_ = lean_ctor_get(v_m_537_, 2);
v___x_555_ = lean_array_fget_borrowed(v_keyArray_553_, v_x_541_);
v_isSome_556_ = lean_noption_is_some(v___x_555_);
if (v_isSome_556_ == 0)
{
lean_dec(v_x_540_);
if (lean_obj_tag(v_x_539_) == 0)
{
lean_object* v___x_557_; 
v___x_557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_557_, 0, v_x_541_);
return v___x_557_;
}
else
{
lean_object* v_val_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_565_; 
lean_dec(v_x_541_);
v_val_558_ = lean_ctor_get(v_x_539_, 0);
v_isSharedCheck_565_ = !lean_is_exclusive(v_x_539_);
if (v_isSharedCheck_565_ == 0)
{
v___x_560_ = v_x_539_;
v_isShared_561_ = v_isSharedCheck_565_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_val_558_);
lean_dec(v_x_539_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_565_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v___x_563_; 
if (v_isShared_561_ == 0)
{
v___x_563_ = v___x_560_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_val_558_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
}
}
else
{
lean_object* v_one_566_; lean_object* v_n_567_; lean_object* v___y_569_; 
v_one_566_ = lean_unsigned_to_nat(1u);
v_n_567_ = lean_nat_sub(v_x_540_, v_one_566_);
lean_dec(v_x_540_);
if (v_isSome_556_ == 0)
{
goto v___jp_575_;
}
else
{
lean_object* v___x_577_; uint8_t v_isSome_578_; 
v___x_577_ = lean_array_fget_borrowed(v_valueArray_554_, v_x_541_);
v_isSome_578_ = lean_noption_is_some(v___x_577_);
if (v_isSome_578_ == 0)
{
goto v___jp_575_;
}
else
{
lean_object* v_val_579_; uint8_t v___x_580_; 
lean_inc(v___x_555_);
v_val_579_ = lean_noption_get(v___x_555_);
v___x_580_ = lean_string_dec_eq(v_val_579_, v_query_538_);
if (v___x_580_ == 0)
{
lean_object* v___x_581_; lean_object* v___x_582_; uint8_t v___x_583_; 
lean_dec(v_val_579_);
v___x_581_ = lean_array_get_size(v_keyArray_553_);
v___x_582_ = lean_nat_add(v_x_541_, v_one_566_);
lean_dec(v_x_541_);
v___x_583_ = lean_nat_dec_lt(v___x_582_, v___x_581_);
if (v___x_583_ == 0)
{
lean_dec(v___x_582_);
v_x_540_ = v_n_567_;
v_x_541_ = v_zero_542_;
goto _start;
}
else
{
v_x_540_ = v_n_567_;
v_x_541_ = v___x_582_;
goto _start;
}
}
else
{
lean_object* v_val_586_; lean_object* v___x_587_; 
lean_dec(v_n_567_);
lean_dec(v_x_539_);
lean_inc(v___x_577_);
v_val_586_ = lean_noption_get(v___x_577_);
v___x_587_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_587_, 0, v_x_541_);
lean_ctor_set(v___x_587_, 1, v_val_579_);
lean_ctor_set(v___x_587_, 2, v_val_586_);
return v___x_587_;
}
}
}
v___jp_568_:
{
lean_object* v___x_570_; lean_object* v___x_571_; uint8_t v___x_572_; 
v___x_570_ = lean_array_get_size(v_keyArray_553_);
v___x_571_ = lean_nat_add(v_x_541_, v_one_566_);
lean_dec(v_x_541_);
v___x_572_ = lean_nat_dec_lt(v___x_571_, v___x_570_);
if (v___x_572_ == 0)
{
lean_dec(v___x_571_);
v_x_539_ = v___y_569_;
v_x_540_ = v_n_567_;
v_x_541_ = v_zero_542_;
goto _start;
}
else
{
v_x_539_ = v___y_569_;
v_x_540_ = v_n_567_;
v_x_541_ = v___x_571_;
goto _start;
}
}
v___jp_575_:
{
if (lean_obj_tag(v_x_539_) == 0)
{
lean_object* v___x_576_; 
lean_inc(v_x_541_);
v___x_576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_576_, 0, v_x_541_);
v___y_569_ = v___x_576_;
goto v___jp_568_;
}
else
{
v___y_569_ = v_x_539_;
goto v___jp_568_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Http_Response_Builder_header_spec__0_spec__0___redArg___boxed(lean_object* v_m_588_, lean_object* v_query_589_, lean_object* v_x_590_, lean_object* v_x_591_, lean_object* v_x_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Http_Response_Builder_header_spec__0_spec__0___redArg(v_m_588_, v_query_589_, v_x_590_, v_x_591_, v_x_592_);
lean_dec_ref(v_query_589_);
lean_dec_ref(v_m_588_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Http_Response_Builder_header_spec__0___redArg(lean_object* v_m_594_, lean_object* v_query_595_){
_start:
{
lean_object* v_keyArray_596_; lean_object* v___x_597_; uint64_t v___x_598_; uint64_t v___x_599_; uint64_t v___x_600_; uint64_t v_fold_601_; uint64_t v___x_602_; uint64_t v___x_603_; uint64_t v___x_604_; size_t v___x_605_; size_t v___x_606_; size_t v___x_607_; size_t v___x_608_; size_t v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v_keyArray_596_ = lean_ctor_get(v_m_594_, 1);
v___x_597_ = lean_array_get_size(v_keyArray_596_);
v___x_598_ = lean_string_hash(v_query_595_);
v___x_599_ = 32ULL;
v___x_600_ = lean_uint64_shift_right(v___x_598_, v___x_599_);
v_fold_601_ = lean_uint64_xor(v___x_598_, v___x_600_);
v___x_602_ = 16ULL;
v___x_603_ = lean_uint64_shift_right(v_fold_601_, v___x_602_);
v___x_604_ = lean_uint64_xor(v_fold_601_, v___x_603_);
v___x_605_ = lean_uint64_to_usize(v___x_604_);
v___x_606_ = lean_usize_of_nat(v___x_597_);
v___x_607_ = ((size_t)1ULL);
v___x_608_ = lean_usize_sub(v___x_606_, v___x_607_);
v___x_609_ = lean_usize_land(v___x_605_, v___x_608_);
v___x_610_ = lean_usize_to_nat(v___x_609_);
v___x_611_ = lean_box(0);
v___x_612_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Http_Response_Builder_header_spec__0_spec__0___redArg(v_m_594_, v_query_595_, v___x_611_, v___x_597_, v___x_610_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Http_Response_Builder_header_spec__0___redArg___boxed(lean_object* v_m_613_, lean_object* v_query_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Http_Response_Builder_header_spec__0___redArg(v_m_613_, v_query_614_);
lean_dec_ref(v_query_614_);
lean_dec_ref(v_m_613_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Http_Response_Builder_header_spec__1_spec__2_spec__3___redArg(lean_object* v_b_616_, lean_object* v_acc_617_, lean_object* v_i_618_){
_start:
{
lean_object* v___y_620_; lean_object* v_keyArray_628_; lean_object* v_valueArray_629_; lean_object* v___x_630_; uint8_t v___x_631_; 
v_keyArray_628_ = lean_ctor_get(v_b_616_, 1);
v_valueArray_629_ = lean_ctor_get(v_b_616_, 2);
v___x_630_ = lean_array_get_size(v_keyArray_628_);
v___x_631_ = lean_nat_dec_lt(v_i_618_, v___x_630_);
if (v___x_631_ == 0)
{
lean_dec(v_i_618_);
return v_acc_617_;
}
else
{
lean_object* v___x_632_; uint8_t v_isSome_633_; 
v___x_632_ = lean_array_fget_borrowed(v_keyArray_628_, v_i_618_);
v_isSome_633_ = lean_noption_is_some(v___x_632_);
if (v_isSome_633_ == 0)
{
goto v___jp_624_;
}
else
{
lean_object* v___x_634_; uint8_t v_isSome_635_; 
v___x_634_ = lean_array_fget_borrowed(v_valueArray_629_, v_i_618_);
v_isSome_635_ = lean_noption_is_some(v___x_634_);
if (v_isSome_635_ == 0)
{
goto v___jp_624_;
}
else
{
lean_object* v_val_636_; lean_object* v_val_637_; lean_object* v_i_639_; lean_object* v___x_644_; 
lean_inc(v___x_632_);
v_val_636_ = lean_noption_get(v___x_632_);
lean_inc(v___x_634_);
v_val_637_ = lean_noption_get(v___x_634_);
v___x_644_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Http_Response_Builder_header_spec__0___redArg(v_acc_617_, v_val_636_);
switch(lean_obj_tag(v___x_644_))
{
case 0:
{
lean_object* v_index_645_; lean_object* v_size_646_; lean_object* v___x_647_; 
v_index_645_ = lean_ctor_get(v___x_644_, 0);
lean_inc(v_index_645_);
lean_dec_ref_known(v___x_644_, 3);
v_size_646_ = lean_ctor_get(v_acc_617_, 0);
lean_inc(v_size_646_);
v___x_647_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_617_, v_size_646_, v_index_645_, v_val_636_, v_val_637_);
lean_dec(v_index_645_);
v___y_620_ = v___x_647_;
goto v___jp_619_;
}
case 1:
{
lean_object* v_index_648_; 
v_index_648_ = lean_ctor_get(v___x_644_, 0);
lean_inc(v_index_648_);
lean_dec_ref_known(v___x_644_, 1);
v_i_639_ = v_index_648_;
goto v___jp_638_;
}
default: 
{
lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_649_ = lean_unsigned_to_nat(0u);
v___x_650_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_617_, v___x_649_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v_index_651_; 
v_index_651_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_index_651_);
lean_dec_ref_known(v___x_650_, 1);
v_i_639_ = v_index_651_;
goto v___jp_638_;
}
else
{
lean_dec(v_val_637_);
lean_dec(v_val_636_);
v___y_620_ = v_acc_617_;
goto v___jp_619_;
}
}
}
v___jp_638_:
{
lean_object* v_size_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v_size_640_ = lean_ctor_get(v_acc_617_, 0);
v___x_641_ = lean_unsigned_to_nat(1u);
v___x_642_ = lean_nat_add(v_size_640_, v___x_641_);
v___x_643_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_617_, v___x_642_, v_i_639_, v_val_636_, v_val_637_);
lean_dec(v_i_639_);
v___y_620_ = v___x_643_;
goto v___jp_619_;
}
}
}
}
v___jp_619_:
{
lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_621_ = lean_unsigned_to_nat(1u);
v___x_622_ = lean_nat_add(v_i_618_, v___x_621_);
lean_dec(v_i_618_);
v_acc_617_ = v___y_620_;
v_i_618_ = v___x_622_;
goto _start;
}
v___jp_624_:
{
lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_625_ = lean_unsigned_to_nat(1u);
v___x_626_ = lean_nat_add(v_i_618_, v___x_625_);
lean_dec(v_i_618_);
v_i_618_ = v___x_626_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Http_Response_Builder_header_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_b_652_, lean_object* v_acc_653_, lean_object* v_i_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Http_Response_Builder_header_spec__1_spec__2_spec__3___redArg(v_b_652_, v_acc_653_, v_i_654_);
lean_dec_ref(v_b_652_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Http_Response_Builder_header_spec__1_spec__2___redArg(lean_object* v_init_656_, lean_object* v_b_657_){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = lean_unsigned_to_nat(0u);
v___x_659_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Http_Response_Builder_header_spec__1_spec__2_spec__3___redArg(v_b_657_, v_init_656_, v___x_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Http_Response_Builder_header_spec__1_spec__2___redArg___boxed(lean_object* v_init_660_, lean_object* v_b_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Http_Response_Builder_header_spec__1_spec__2___redArg(v_init_660_, v_b_661_);
lean_dec_ref(v_b_661_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Http_Response_Builder_header_spec__1___redArg(lean_object* v_m_663_){
_start:
{
lean_object* v_keyArray_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v_cellCount_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v_target_671_; lean_object* v___x_672_; 
v_keyArray_664_ = lean_ctor_get(v_m_663_, 1);
v___x_665_ = lean_array_get_size(v_keyArray_664_);
v___x_666_ = lean_unsigned_to_nat(2u);
v_cellCount_667_ = lean_nat_mul(v___x_665_, v___x_666_);
v___x_668_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_667_);
v___x_669_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_667_);
v___x_670_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_667_);
v_target_671_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_671_, 0, v___x_668_);
lean_ctor_set(v_target_671_, 1, v___x_669_);
lean_ctor_set(v_target_671_, 2, v___x_670_);
v___x_672_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Http_Response_Builder_header_spec__1_spec__2___redArg(v_target_671_, v_m_663_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Http_Response_Builder_header_spec__1___redArg___boxed(lean_object* v_m_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Http_Response_Builder_header_spec__1___redArg(v_m_673_);
lean_dec_ref(v_m_673_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_header(lean_object* v_builder_675_, lean_object* v_key_676_, lean_object* v_value_677_){
_start:
{
lean_object* v_line_678_; lean_object* v_headers_679_; lean_object* v_extensions_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_785_; 
v_line_678_ = lean_ctor_get(v_builder_675_, 0);
lean_inc_ref(v_line_678_);
v_headers_679_ = lean_ctor_get(v_line_678_, 1);
lean_inc_ref(v_headers_679_);
v_extensions_680_ = lean_ctor_get(v_builder_675_, 1);
v_isSharedCheck_785_ = !lean_is_exclusive(v_builder_675_);
if (v_isSharedCheck_785_ == 0)
{
lean_object* v_unused_786_; 
v_unused_786_ = lean_ctor_get(v_builder_675_, 0);
lean_dec(v_unused_786_);
v___x_682_ = v_builder_675_;
v_isShared_683_ = v_isSharedCheck_785_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_extensions_680_);
lean_dec(v_builder_675_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_785_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v_status_684_; uint8_t v_version_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_783_; 
v_status_684_ = lean_ctor_get(v_line_678_, 0);
v_version_685_ = lean_ctor_get_uint8(v_line_678_, sizeof(void*)*2);
v_isSharedCheck_783_ = !lean_is_exclusive(v_line_678_);
if (v_isSharedCheck_783_ == 0)
{
lean_object* v_unused_784_; 
v_unused_784_ = lean_ctor_get(v_line_678_, 1);
lean_dec(v_unused_784_);
v___x_687_ = v_line_678_;
v_isShared_688_ = v_isSharedCheck_783_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_status_684_);
lean_dec(v_line_678_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_783_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v_entries_689_; lean_object* v_indexes_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_782_; 
v_entries_689_ = lean_ctor_get(v_headers_679_, 0);
v_indexes_690_ = lean_ctor_get(v_headers_679_, 1);
v_isSharedCheck_782_ = !lean_is_exclusive(v_headers_679_);
if (v_isSharedCheck_782_ == 0)
{
v___x_692_ = v_headers_679_;
v_isShared_693_ = v_isSharedCheck_782_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_indexes_690_);
lean_inc(v_entries_689_);
lean_dec(v_headers_679_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_782_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v_i_694_; lean_object* v___x_695_; lean_object* v_entries_696_; lean_object* v___y_698_; lean_object* v___x_708_; 
v_i_694_ = lean_array_get_size(v_entries_689_);
lean_inc_ref(v_key_676_);
v___x_695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_695_, 0, v_key_676_);
lean_ctor_set(v___x_695_, 1, v_value_677_);
v_entries_696_ = lean_array_push(v_entries_689_, v___x_695_);
v___x_708_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Http_Response_Builder_header_spec__0___redArg(v_indexes_690_, v_key_676_);
switch(lean_obj_tag(v___x_708_))
{
case 0:
{
lean_object* v_index_709_; lean_object* v_value_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v_val_713_; lean_object* v_size_714_; lean_object* v___x_715_; 
v_index_709_ = lean_ctor_get(v___x_708_, 0);
lean_inc(v_index_709_);
v_value_710_ = lean_ctor_get(v___x_708_, 2);
lean_inc(v_value_710_);
lean_dec_ref_known(v___x_708_, 3);
v___x_711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_711_, 0, v_value_710_);
v___x_712_ = l_Std_Http_Response_Builder_header___lam__0(v_i_694_, v___x_711_);
v_val_713_ = lean_ctor_get(v___x_712_, 0);
lean_inc(v_val_713_);
lean_dec(v___x_712_);
v_size_714_ = lean_ctor_get(v_indexes_690_, 0);
lean_inc(v_size_714_);
v___x_715_ = l_Std_DHashMap_Raw_setEntry___redArg(v_indexes_690_, v_size_714_, v_index_709_, v_key_676_, v_val_713_);
lean_dec(v_index_709_);
v___y_698_ = v___x_715_;
goto v___jp_697_;
}
case 1:
{
lean_object* v_index_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v_val_719_; lean_object* v___y_721_; lean_object* v_i_722_; lean_object* v_size_737_; lean_object* v_keyArray_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; uint8_t v___x_742_; 
v_index_716_ = lean_ctor_get(v___x_708_, 0);
lean_inc(v_index_716_);
lean_dec_ref_known(v___x_708_, 1);
v___x_717_ = lean_box(0);
v___x_718_ = l_Std_Http_Response_Builder_header___lam__0(v_i_694_, v___x_717_);
v_val_719_ = lean_ctor_get(v___x_718_, 0);
lean_inc(v_val_719_);
lean_dec(v___x_718_);
v_size_737_ = lean_ctor_get(v_indexes_690_, 0);
v_keyArray_738_ = lean_ctor_get(v_indexes_690_, 1);
v___x_739_ = lean_unsigned_to_nat(1u);
v___x_740_ = lean_nat_add(v_size_737_, v___x_739_);
v___x_741_ = lean_array_get_size(v_keyArray_738_);
v___x_742_ = lean_nat_dec_lt(v___x_740_, v___x_741_);
if (v___x_742_ == 0)
{
lean_dec(v___x_740_);
lean_dec(v_index_716_);
goto v___jp_727_;
}
else
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; uint8_t v___x_747_; 
v___x_743_ = lean_unsigned_to_nat(4u);
v___x_744_ = lean_nat_mul(v___x_740_, v___x_743_);
v___x_745_ = lean_unsigned_to_nat(3u);
v___x_746_ = lean_nat_mul(v___x_741_, v___x_745_);
v___x_747_ = lean_nat_dec_le(v___x_744_, v___x_746_);
lean_dec(v___x_746_);
lean_dec(v___x_744_);
if (v___x_747_ == 0)
{
lean_dec(v___x_740_);
lean_dec(v_index_716_);
goto v___jp_727_;
}
else
{
lean_object* v___x_748_; 
v___x_748_ = l_Std_DHashMap_Raw_setEntry___redArg(v_indexes_690_, v___x_740_, v_index_716_, v_key_676_, v_val_719_);
lean_dec(v_index_716_);
v___y_698_ = v___x_748_;
goto v___jp_697_;
}
}
v___jp_720_:
{
lean_object* v_size_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v_size_723_ = lean_ctor_get(v___y_721_, 0);
v___x_724_ = lean_unsigned_to_nat(1u);
v___x_725_ = lean_nat_add(v_size_723_, v___x_724_);
v___x_726_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_721_, v___x_725_, v_i_722_, v_key_676_, v_val_719_);
lean_dec(v_i_722_);
v___y_698_ = v___x_726_;
goto v___jp_697_;
}
v___jp_727_:
{
lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_728_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Http_Response_Builder_header_spec__1___redArg(v_indexes_690_);
lean_dec_ref(v_indexes_690_);
v___x_729_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Http_Response_Builder_header_spec__0___redArg(v___x_728_, v_key_676_);
switch(lean_obj_tag(v___x_729_))
{
case 0:
{
lean_object* v_index_730_; lean_object* v_size_731_; lean_object* v___x_732_; 
v_index_730_ = lean_ctor_get(v___x_729_, 0);
lean_inc(v_index_730_);
lean_dec_ref_known(v___x_729_, 3);
v_size_731_ = lean_ctor_get(v___x_728_, 0);
lean_inc(v_size_731_);
v___x_732_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_728_, v_size_731_, v_index_730_, v_key_676_, v_val_719_);
lean_dec(v_index_730_);
v___y_698_ = v___x_732_;
goto v___jp_697_;
}
case 1:
{
lean_object* v_index_733_; 
v_index_733_ = lean_ctor_get(v___x_729_, 0);
lean_inc(v_index_733_);
lean_dec_ref_known(v___x_729_, 1);
v___y_721_ = v___x_728_;
v_i_722_ = v_index_733_;
goto v___jp_720_;
}
default: 
{
lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_734_ = lean_unsigned_to_nat(0u);
v___x_735_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_728_, v___x_734_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v_index_736_; 
v_index_736_ = lean_ctor_get(v___x_735_, 0);
lean_inc(v_index_736_);
lean_dec_ref_known(v___x_735_, 1);
v___y_721_ = v___x_728_;
v_i_722_ = v_index_736_;
goto v___jp_720_;
}
else
{
lean_dec(v_val_719_);
lean_dec_ref(v_key_676_);
v___y_698_ = v___x_728_;
goto v___jp_697_;
}
}
}
}
}
default: 
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v_val_751_; lean_object* v___y_753_; lean_object* v_i_754_; lean_object* v___y_760_; lean_object* v_size_769_; lean_object* v_keyArray_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; uint8_t v___x_774_; 
v___x_749_ = lean_box(0);
v___x_750_ = l_Std_Http_Response_Builder_header___lam__0(v_i_694_, v___x_749_);
v_val_751_ = lean_ctor_get(v___x_750_, 0);
lean_inc(v_val_751_);
lean_dec(v___x_750_);
v_size_769_ = lean_ctor_get(v_indexes_690_, 0);
v_keyArray_770_ = lean_ctor_get(v_indexes_690_, 1);
v___x_771_ = lean_unsigned_to_nat(1u);
v___x_772_ = lean_nat_add(v_size_769_, v___x_771_);
v___x_773_ = lean_array_get_size(v_keyArray_770_);
v___x_774_ = lean_nat_dec_lt(v___x_772_, v___x_773_);
if (v___x_774_ == 0)
{
lean_object* v___x_775_; 
lean_dec(v___x_772_);
v___x_775_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Http_Response_Builder_header_spec__1___redArg(v_indexes_690_);
lean_dec_ref(v_indexes_690_);
v___y_760_ = v___x_775_;
goto v___jp_759_;
}
else
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; uint8_t v___x_780_; 
v___x_776_ = lean_unsigned_to_nat(4u);
v___x_777_ = lean_nat_mul(v___x_772_, v___x_776_);
lean_dec(v___x_772_);
v___x_778_ = lean_unsigned_to_nat(3u);
v___x_779_ = lean_nat_mul(v___x_773_, v___x_778_);
v___x_780_ = lean_nat_dec_le(v___x_777_, v___x_779_);
lean_dec(v___x_779_);
lean_dec(v___x_777_);
if (v___x_780_ == 0)
{
lean_object* v___x_781_; 
v___x_781_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Http_Response_Builder_header_spec__1___redArg(v_indexes_690_);
lean_dec_ref(v_indexes_690_);
v___y_760_ = v___x_781_;
goto v___jp_759_;
}
else
{
v___y_760_ = v_indexes_690_;
goto v___jp_759_;
}
}
v___jp_752_:
{
lean_object* v_size_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v_size_755_ = lean_ctor_get(v___y_753_, 0);
v___x_756_ = lean_unsigned_to_nat(1u);
v___x_757_ = lean_nat_add(v_size_755_, v___x_756_);
v___x_758_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_753_, v___x_757_, v_i_754_, v_key_676_, v_val_751_);
lean_dec(v_i_754_);
v___y_698_ = v___x_758_;
goto v___jp_697_;
}
v___jp_759_:
{
lean_object* v___x_761_; 
v___x_761_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Http_Response_Builder_header_spec__0___redArg(v___y_760_, v_key_676_);
switch(lean_obj_tag(v___x_761_))
{
case 0:
{
lean_object* v_index_762_; lean_object* v_size_763_; lean_object* v___x_764_; 
v_index_762_ = lean_ctor_get(v___x_761_, 0);
lean_inc(v_index_762_);
lean_dec_ref_known(v___x_761_, 3);
v_size_763_ = lean_ctor_get(v___y_760_, 0);
lean_inc(v_size_763_);
v___x_764_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_760_, v_size_763_, v_index_762_, v_key_676_, v_val_751_);
lean_dec(v_index_762_);
v___y_698_ = v___x_764_;
goto v___jp_697_;
}
case 1:
{
lean_object* v_index_765_; 
v_index_765_ = lean_ctor_get(v___x_761_, 0);
lean_inc(v_index_765_);
lean_dec_ref_known(v___x_761_, 1);
v___y_753_ = v___y_760_;
v_i_754_ = v_index_765_;
goto v___jp_752_;
}
default: 
{
lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_766_ = lean_unsigned_to_nat(0u);
v___x_767_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_760_, v___x_766_);
if (lean_obj_tag(v___x_767_) == 0)
{
lean_object* v_index_768_; 
v_index_768_ = lean_ctor_get(v___x_767_, 0);
lean_inc(v_index_768_);
lean_dec_ref_known(v___x_767_, 1);
v___y_753_ = v___y_760_;
v_i_754_ = v_index_768_;
goto v___jp_752_;
}
else
{
lean_dec(v_val_751_);
lean_dec_ref(v_key_676_);
v___y_698_ = v___y_760_;
goto v___jp_697_;
}
}
}
}
}
}
v___jp_697_:
{
lean_object* v___x_700_; 
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 1, v___y_698_);
lean_ctor_set(v___x_692_, 0, v_entries_696_);
v___x_700_ = v___x_692_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_entries_696_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v___y_698_);
v___x_700_ = v_reuseFailAlloc_707_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
lean_object* v___x_702_; 
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 1, v___x_700_);
v___x_702_ = v___x_687_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_status_684_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v___x_700_);
lean_ctor_set_uint8(v_reuseFailAlloc_706_, sizeof(void*)*2, v_version_685_);
v___x_702_ = v_reuseFailAlloc_706_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
lean_object* v___x_704_; 
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 0, v___x_702_);
v___x_704_ = v___x_682_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_702_);
lean_ctor_set(v_reuseFailAlloc_705_, 1, v_extensions_680_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Http_Response_Builder_header_spec__0(lean_object* v_00_u03b2_787_, lean_object* v_m_788_, lean_object* v_query_789_){
_start:
{
lean_object* v___x_790_; 
v___x_790_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Http_Response_Builder_header_spec__0___redArg(v_m_788_, v_query_789_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Http_Response_Builder_header_spec__0___boxed(lean_object* v_00_u03b2_791_, lean_object* v_m_792_, lean_object* v_query_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Http_Response_Builder_header_spec__0(v_00_u03b2_791_, v_m_792_, v_query_793_);
lean_dec_ref(v_query_793_);
lean_dec_ref(v_m_792_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Http_Response_Builder_header_spec__1(lean_object* v_00_u03b2_795_, lean_object* v_m_796_){
_start:
{
lean_object* v___x_797_; 
v___x_797_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Http_Response_Builder_header_spec__1___redArg(v_m_796_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Http_Response_Builder_header_spec__1___boxed(lean_object* v_00_u03b2_798_, lean_object* v_m_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Http_Response_Builder_header_spec__1(v_00_u03b2_798_, v_m_799_);
lean_dec_ref(v_m_799_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Http_Response_Builder_header_spec__0_spec__0(lean_object* v_00_u03b2_801_, lean_object* v_m_802_, lean_object* v_query_803_, lean_object* v_x_804_, lean_object* v_x_805_, lean_object* v_x_806_, lean_object* v_x_807_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Http_Response_Builder_header_spec__0_spec__0___redArg(v_m_802_, v_query_803_, v_x_804_, v_x_805_, v_x_806_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Http_Response_Builder_header_spec__0_spec__0___boxed(lean_object* v_00_u03b2_809_, lean_object* v_m_810_, lean_object* v_query_811_, lean_object* v_x_812_, lean_object* v_x_813_, lean_object* v_x_814_, lean_object* v_x_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Http_Response_Builder_header_spec__0_spec__0(v_00_u03b2_809_, v_m_810_, v_query_811_, v_x_812_, v_x_813_, v_x_814_, v_x_815_);
lean_dec_ref(v_query_811_);
lean_dec_ref(v_m_810_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Http_Response_Builder_header_spec__1_spec__2(lean_object* v_00_u03b2_817_, lean_object* v_init_818_, lean_object* v_b_819_){
_start:
{
lean_object* v___x_820_; 
v___x_820_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Http_Response_Builder_header_spec__1_spec__2___redArg(v_init_818_, v_b_819_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Http_Response_Builder_header_spec__1_spec__2___boxed(lean_object* v_00_u03b2_821_, lean_object* v_init_822_, lean_object* v_b_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Http_Response_Builder_header_spec__1_spec__2(v_00_u03b2_821_, v_init_822_, v_b_823_);
lean_dec_ref(v_b_823_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Http_Response_Builder_header_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_825_, lean_object* v_b_826_, lean_object* v_acc_827_, lean_object* v_i_828_){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Http_Response_Builder_header_spec__1_spec__2_spec__3___redArg(v_b_826_, v_acc_827_, v_i_828_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Http_Response_Builder_header_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_830_, lean_object* v_b_831_, lean_object* v_acc_832_, lean_object* v_i_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Http_Response_Builder_header_spec__1_spec__2_spec__3(v_00_u03b2_830_, v_b_831_, v_acc_832_, v_i_833_);
lean_dec_ref(v_b_831_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_header_x21(lean_object* v_builder_835_, lean_object* v_key_836_, lean_object* v_value_837_){
_start:
{
lean_object* v_line_838_; lean_object* v_headers_839_; lean_object* v_extensions_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_947_; 
v_line_838_ = lean_ctor_get(v_builder_835_, 0);
lean_inc_ref(v_line_838_);
v_headers_839_ = lean_ctor_get(v_line_838_, 1);
lean_inc_ref(v_headers_839_);
v_extensions_840_ = lean_ctor_get(v_builder_835_, 1);
v_isSharedCheck_947_ = !lean_is_exclusive(v_builder_835_);
if (v_isSharedCheck_947_ == 0)
{
lean_object* v_unused_948_; 
v_unused_948_ = lean_ctor_get(v_builder_835_, 0);
lean_dec(v_unused_948_);
v___x_842_ = v_builder_835_;
v_isShared_843_ = v_isSharedCheck_947_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_extensions_840_);
lean_dec(v_builder_835_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_947_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v_status_844_; uint8_t v_version_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_945_; 
v_status_844_ = lean_ctor_get(v_line_838_, 0);
v_version_845_ = lean_ctor_get_uint8(v_line_838_, sizeof(void*)*2);
v_isSharedCheck_945_ = !lean_is_exclusive(v_line_838_);
if (v_isSharedCheck_945_ == 0)
{
lean_object* v_unused_946_; 
v_unused_946_ = lean_ctor_get(v_line_838_, 1);
lean_dec(v_unused_946_);
v___x_847_ = v_line_838_;
v_isShared_848_ = v_isSharedCheck_945_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_status_844_);
lean_dec(v_line_838_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_945_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v_entries_849_; lean_object* v_indexes_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_944_; 
v_entries_849_ = lean_ctor_get(v_headers_839_, 0);
v_indexes_850_ = lean_ctor_get(v_headers_839_, 1);
v_isSharedCheck_944_ = !lean_is_exclusive(v_headers_839_);
if (v_isSharedCheck_944_ == 0)
{
v___x_852_ = v_headers_839_;
v_isShared_853_ = v_isSharedCheck_944_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_indexes_850_);
lean_inc(v_entries_849_);
lean_dec(v_headers_839_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_944_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v_key_854_; lean_object* v_value_855_; lean_object* v_i_856_; lean_object* v___x_857_; lean_object* v_entries_858_; lean_object* v___y_860_; lean_object* v___x_870_; 
v_key_854_ = l_Std_Http_Header_Name_ofString_x21(v_key_836_);
v_value_855_ = l_Std_Http_Header_Value_ofString_x21(v_value_837_);
v_i_856_ = lean_array_get_size(v_entries_849_);
lean_inc_ref(v_key_854_);
v___x_857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_857_, 0, v_key_854_);
lean_ctor_set(v___x_857_, 1, v_value_855_);
v_entries_858_ = lean_array_push(v_entries_849_, v___x_857_);
v___x_870_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Http_Response_Builder_header_spec__0___redArg(v_indexes_850_, v_key_854_);
switch(lean_obj_tag(v___x_870_))
{
case 0:
{
lean_object* v_index_871_; lean_object* v_value_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v_val_875_; lean_object* v_size_876_; lean_object* v___x_877_; 
v_index_871_ = lean_ctor_get(v___x_870_, 0);
lean_inc(v_index_871_);
v_value_872_ = lean_ctor_get(v___x_870_, 2);
lean_inc(v_value_872_);
lean_dec_ref_known(v___x_870_, 3);
v___x_873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_873_, 0, v_value_872_);
v___x_874_ = l_Std_Http_Response_Builder_header___lam__0(v_i_856_, v___x_873_);
v_val_875_ = lean_ctor_get(v___x_874_, 0);
lean_inc(v_val_875_);
lean_dec(v___x_874_);
v_size_876_ = lean_ctor_get(v_indexes_850_, 0);
lean_inc(v_size_876_);
v___x_877_ = l_Std_DHashMap_Raw_setEntry___redArg(v_indexes_850_, v_size_876_, v_index_871_, v_key_854_, v_val_875_);
lean_dec(v_index_871_);
v___y_860_ = v___x_877_;
goto v___jp_859_;
}
case 1:
{
lean_object* v_index_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v_val_881_; lean_object* v___y_883_; lean_object* v_i_884_; lean_object* v_size_899_; lean_object* v_keyArray_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; uint8_t v___x_904_; 
v_index_878_ = lean_ctor_get(v___x_870_, 0);
lean_inc(v_index_878_);
lean_dec_ref_known(v___x_870_, 1);
v___x_879_ = lean_box(0);
v___x_880_ = l_Std_Http_Response_Builder_header___lam__0(v_i_856_, v___x_879_);
v_val_881_ = lean_ctor_get(v___x_880_, 0);
lean_inc(v_val_881_);
lean_dec(v___x_880_);
v_size_899_ = lean_ctor_get(v_indexes_850_, 0);
v_keyArray_900_ = lean_ctor_get(v_indexes_850_, 1);
v___x_901_ = lean_unsigned_to_nat(1u);
v___x_902_ = lean_nat_add(v_size_899_, v___x_901_);
v___x_903_ = lean_array_get_size(v_keyArray_900_);
v___x_904_ = lean_nat_dec_lt(v___x_902_, v___x_903_);
if (v___x_904_ == 0)
{
lean_dec(v___x_902_);
lean_dec(v_index_878_);
goto v___jp_889_;
}
else
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; uint8_t v___x_909_; 
v___x_905_ = lean_unsigned_to_nat(4u);
v___x_906_ = lean_nat_mul(v___x_902_, v___x_905_);
v___x_907_ = lean_unsigned_to_nat(3u);
v___x_908_ = lean_nat_mul(v___x_903_, v___x_907_);
v___x_909_ = lean_nat_dec_le(v___x_906_, v___x_908_);
lean_dec(v___x_908_);
lean_dec(v___x_906_);
if (v___x_909_ == 0)
{
lean_dec(v___x_902_);
lean_dec(v_index_878_);
goto v___jp_889_;
}
else
{
lean_object* v___x_910_; 
v___x_910_ = l_Std_DHashMap_Raw_setEntry___redArg(v_indexes_850_, v___x_902_, v_index_878_, v_key_854_, v_val_881_);
lean_dec(v_index_878_);
v___y_860_ = v___x_910_;
goto v___jp_859_;
}
}
v___jp_882_:
{
lean_object* v_size_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
v_size_885_ = lean_ctor_get(v___y_883_, 0);
v___x_886_ = lean_unsigned_to_nat(1u);
v___x_887_ = lean_nat_add(v_size_885_, v___x_886_);
v___x_888_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_883_, v___x_887_, v_i_884_, v_key_854_, v_val_881_);
lean_dec(v_i_884_);
v___y_860_ = v___x_888_;
goto v___jp_859_;
}
v___jp_889_:
{
lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_890_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Http_Response_Builder_header_spec__1___redArg(v_indexes_850_);
lean_dec_ref(v_indexes_850_);
v___x_891_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Http_Response_Builder_header_spec__0___redArg(v___x_890_, v_key_854_);
switch(lean_obj_tag(v___x_891_))
{
case 0:
{
lean_object* v_index_892_; lean_object* v_size_893_; lean_object* v___x_894_; 
v_index_892_ = lean_ctor_get(v___x_891_, 0);
lean_inc(v_index_892_);
lean_dec_ref_known(v___x_891_, 3);
v_size_893_ = lean_ctor_get(v___x_890_, 0);
lean_inc(v_size_893_);
v___x_894_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_890_, v_size_893_, v_index_892_, v_key_854_, v_val_881_);
lean_dec(v_index_892_);
v___y_860_ = v___x_894_;
goto v___jp_859_;
}
case 1:
{
lean_object* v_index_895_; 
v_index_895_ = lean_ctor_get(v___x_891_, 0);
lean_inc(v_index_895_);
lean_dec_ref_known(v___x_891_, 1);
v___y_883_ = v___x_890_;
v_i_884_ = v_index_895_;
goto v___jp_882_;
}
default: 
{
lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_896_ = lean_unsigned_to_nat(0u);
v___x_897_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_890_, v___x_896_);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_object* v_index_898_; 
v_index_898_ = lean_ctor_get(v___x_897_, 0);
lean_inc(v_index_898_);
lean_dec_ref_known(v___x_897_, 1);
v___y_883_ = v___x_890_;
v_i_884_ = v_index_898_;
goto v___jp_882_;
}
else
{
lean_dec(v_val_881_);
lean_dec_ref(v_key_854_);
v___y_860_ = v___x_890_;
goto v___jp_859_;
}
}
}
}
}
default: 
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v_val_913_; lean_object* v___y_915_; lean_object* v_i_916_; lean_object* v___y_922_; lean_object* v_size_931_; lean_object* v_keyArray_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; uint8_t v___x_936_; 
v___x_911_ = lean_box(0);
v___x_912_ = l_Std_Http_Response_Builder_header___lam__0(v_i_856_, v___x_911_);
v_val_913_ = lean_ctor_get(v___x_912_, 0);
lean_inc(v_val_913_);
lean_dec(v___x_912_);
v_size_931_ = lean_ctor_get(v_indexes_850_, 0);
v_keyArray_932_ = lean_ctor_get(v_indexes_850_, 1);
v___x_933_ = lean_unsigned_to_nat(1u);
v___x_934_ = lean_nat_add(v_size_931_, v___x_933_);
v___x_935_ = lean_array_get_size(v_keyArray_932_);
v___x_936_ = lean_nat_dec_lt(v___x_934_, v___x_935_);
if (v___x_936_ == 0)
{
lean_object* v___x_937_; 
lean_dec(v___x_934_);
v___x_937_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Http_Response_Builder_header_spec__1___redArg(v_indexes_850_);
lean_dec_ref(v_indexes_850_);
v___y_922_ = v___x_937_;
goto v___jp_921_;
}
else
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; uint8_t v___x_942_; 
v___x_938_ = lean_unsigned_to_nat(4u);
v___x_939_ = lean_nat_mul(v___x_934_, v___x_938_);
lean_dec(v___x_934_);
v___x_940_ = lean_unsigned_to_nat(3u);
v___x_941_ = lean_nat_mul(v___x_935_, v___x_940_);
v___x_942_ = lean_nat_dec_le(v___x_939_, v___x_941_);
lean_dec(v___x_941_);
lean_dec(v___x_939_);
if (v___x_942_ == 0)
{
lean_object* v___x_943_; 
v___x_943_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Http_Response_Builder_header_spec__1___redArg(v_indexes_850_);
lean_dec_ref(v_indexes_850_);
v___y_922_ = v___x_943_;
goto v___jp_921_;
}
else
{
v___y_922_ = v_indexes_850_;
goto v___jp_921_;
}
}
v___jp_914_:
{
lean_object* v_size_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v_size_917_ = lean_ctor_get(v___y_915_, 0);
v___x_918_ = lean_unsigned_to_nat(1u);
v___x_919_ = lean_nat_add(v_size_917_, v___x_918_);
v___x_920_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_915_, v___x_919_, v_i_916_, v_key_854_, v_val_913_);
lean_dec(v_i_916_);
v___y_860_ = v___x_920_;
goto v___jp_859_;
}
v___jp_921_:
{
lean_object* v___x_923_; 
v___x_923_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Http_Response_Builder_header_spec__0___redArg(v___y_922_, v_key_854_);
switch(lean_obj_tag(v___x_923_))
{
case 0:
{
lean_object* v_index_924_; lean_object* v_size_925_; lean_object* v___x_926_; 
v_index_924_ = lean_ctor_get(v___x_923_, 0);
lean_inc(v_index_924_);
lean_dec_ref_known(v___x_923_, 3);
v_size_925_ = lean_ctor_get(v___y_922_, 0);
lean_inc(v_size_925_);
v___x_926_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_922_, v_size_925_, v_index_924_, v_key_854_, v_val_913_);
lean_dec(v_index_924_);
v___y_860_ = v___x_926_;
goto v___jp_859_;
}
case 1:
{
lean_object* v_index_927_; 
v_index_927_ = lean_ctor_get(v___x_923_, 0);
lean_inc(v_index_927_);
lean_dec_ref_known(v___x_923_, 1);
v___y_915_ = v___y_922_;
v_i_916_ = v_index_927_;
goto v___jp_914_;
}
default: 
{
lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_928_ = lean_unsigned_to_nat(0u);
v___x_929_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_922_, v___x_928_);
if (lean_obj_tag(v___x_929_) == 0)
{
lean_object* v_index_930_; 
v_index_930_ = lean_ctor_get(v___x_929_, 0);
lean_inc(v_index_930_);
lean_dec_ref_known(v___x_929_, 1);
v___y_915_ = v___y_922_;
v_i_916_ = v_index_930_;
goto v___jp_914_;
}
else
{
lean_dec(v_val_913_);
lean_dec_ref(v_key_854_);
v___y_860_ = v___y_922_;
goto v___jp_859_;
}
}
}
}
}
}
v___jp_859_:
{
lean_object* v___x_862_; 
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 1, v___y_860_);
lean_ctor_set(v___x_852_, 0, v_entries_858_);
v___x_862_ = v___x_852_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_entries_858_);
lean_ctor_set(v_reuseFailAlloc_869_, 1, v___y_860_);
v___x_862_ = v_reuseFailAlloc_869_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
lean_object* v___x_864_; 
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 1, v___x_862_);
v___x_864_ = v___x_847_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_status_844_);
lean_ctor_set(v_reuseFailAlloc_868_, 1, v___x_862_);
lean_ctor_set_uint8(v_reuseFailAlloc_868_, sizeof(void*)*2, v_version_845_);
v___x_864_ = v_reuseFailAlloc_868_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
lean_object* v___x_866_; 
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 0, v___x_864_);
v___x_866_ = v___x_842_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v___x_864_);
lean_ctor_set(v_reuseFailAlloc_867_, 1, v_extensions_840_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_header_x3f(lean_object* v_builder_949_, lean_object* v_key_950_, lean_object* v_value_951_){
_start:
{
lean_object* v___x_952_; 
v___x_952_ = l_Std_Http_Header_Name_ofString_x3f(v_key_950_);
if (lean_obj_tag(v___x_952_) == 0)
{
lean_object* v___x_953_; 
lean_dec_ref(v_value_951_);
lean_dec_ref(v_builder_949_);
v___x_953_ = lean_box(0);
return v___x_953_;
}
else
{
lean_object* v_val_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_1079_; 
v_val_954_ = lean_ctor_get(v___x_952_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_956_ = v___x_952_;
v_isShared_957_ = v_isSharedCheck_1079_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_val_954_);
lean_dec(v___x_952_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_1079_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_958_; 
v___x_958_ = l_Std_Http_Header_Value_ofString_x3f(v_value_951_);
if (lean_obj_tag(v___x_958_) == 0)
{
lean_object* v___x_959_; 
lean_del_object(v___x_956_);
lean_dec(v_val_954_);
lean_dec_ref(v_builder_949_);
v___x_959_ = lean_box(0);
return v___x_959_;
}
else
{
lean_object* v_line_960_; lean_object* v_headers_961_; lean_object* v_val_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_1078_; 
v_line_960_ = lean_ctor_get(v_builder_949_, 0);
lean_inc_ref(v_line_960_);
v_headers_961_ = lean_ctor_get(v_line_960_, 1);
lean_inc_ref(v_headers_961_);
v_val_962_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_964_ = v___x_958_;
v_isShared_965_ = v_isSharedCheck_1078_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_val_962_);
lean_dec(v___x_958_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_1078_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v_extensions_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_1076_; 
v_extensions_966_ = lean_ctor_get(v_builder_949_, 1);
v_isSharedCheck_1076_ = !lean_is_exclusive(v_builder_949_);
if (v_isSharedCheck_1076_ == 0)
{
lean_object* v_unused_1077_; 
v_unused_1077_ = lean_ctor_get(v_builder_949_, 0);
lean_dec(v_unused_1077_);
v___x_968_ = v_builder_949_;
v_isShared_969_ = v_isSharedCheck_1076_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_extensions_966_);
lean_dec(v_builder_949_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_1076_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v_status_970_; uint8_t v_version_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_1074_; 
v_status_970_ = lean_ctor_get(v_line_960_, 0);
v_version_971_ = lean_ctor_get_uint8(v_line_960_, sizeof(void*)*2);
v_isSharedCheck_1074_ = !lean_is_exclusive(v_line_960_);
if (v_isSharedCheck_1074_ == 0)
{
lean_object* v_unused_1075_; 
v_unused_1075_ = lean_ctor_get(v_line_960_, 1);
lean_dec(v_unused_1075_);
v___x_973_ = v_line_960_;
v_isShared_974_ = v_isSharedCheck_1074_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_status_970_);
lean_dec(v_line_960_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_1074_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v_entries_975_; lean_object* v_indexes_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_1073_; 
v_entries_975_ = lean_ctor_get(v_headers_961_, 0);
v_indexes_976_ = lean_ctor_get(v_headers_961_, 1);
v_isSharedCheck_1073_ = !lean_is_exclusive(v_headers_961_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_978_ = v_headers_961_;
v_isShared_979_ = v_isSharedCheck_1073_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_indexes_976_);
lean_inc(v_entries_975_);
lean_dec(v_headers_961_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_1073_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v_i_980_; lean_object* v___x_981_; lean_object* v_entries_982_; lean_object* v___y_984_; lean_object* v___x_997_; 
v_i_980_ = lean_array_get_size(v_entries_975_);
lean_inc(v_val_954_);
v___x_981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_981_, 0, v_val_954_);
lean_ctor_set(v___x_981_, 1, v_val_962_);
v_entries_982_ = lean_array_push(v_entries_975_, v___x_981_);
v___x_997_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Http_Response_Builder_header_spec__0___redArg(v_indexes_976_, v_val_954_);
switch(lean_obj_tag(v___x_997_))
{
case 0:
{
lean_object* v_index_998_; lean_object* v_value_999_; lean_object* v___x_1001_; 
v_index_998_ = lean_ctor_get(v___x_997_, 0);
lean_inc(v_index_998_);
v_value_999_ = lean_ctor_get(v___x_997_, 2);
lean_inc(v_value_999_);
lean_dec_ref_known(v___x_997_, 3);
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 0, v_value_999_);
v___x_1001_ = v___x_956_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_value_999_);
v___x_1001_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
lean_object* v___x_1002_; lean_object* v_val_1003_; lean_object* v_size_1004_; lean_object* v___x_1005_; 
v___x_1002_ = l_Std_Http_Response_Builder_header___lam__0(v_i_980_, v___x_1001_);
v_val_1003_ = lean_ctor_get(v___x_1002_, 0);
lean_inc(v_val_1003_);
lean_dec(v___x_1002_);
v_size_1004_ = lean_ctor_get(v_indexes_976_, 0);
lean_inc(v_size_1004_);
v___x_1005_ = l_Std_DHashMap_Raw_setEntry___redArg(v_indexes_976_, v_size_1004_, v_index_998_, v_val_954_, v_val_1003_);
lean_dec(v_index_998_);
v___y_984_ = v___x_1005_;
goto v___jp_983_;
}
}
case 1:
{
lean_object* v_index_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v_val_1010_; lean_object* v___y_1012_; lean_object* v_i_1013_; lean_object* v_size_1028_; lean_object* v_keyArray_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; uint8_t v___x_1033_; 
lean_del_object(v___x_956_);
v_index_1007_ = lean_ctor_get(v___x_997_, 0);
lean_inc(v_index_1007_);
lean_dec_ref_known(v___x_997_, 1);
v___x_1008_ = lean_box(0);
v___x_1009_ = l_Std_Http_Response_Builder_header___lam__0(v_i_980_, v___x_1008_);
v_val_1010_ = lean_ctor_get(v___x_1009_, 0);
lean_inc(v_val_1010_);
lean_dec(v___x_1009_);
v_size_1028_ = lean_ctor_get(v_indexes_976_, 0);
v_keyArray_1029_ = lean_ctor_get(v_indexes_976_, 1);
v___x_1030_ = lean_unsigned_to_nat(1u);
v___x_1031_ = lean_nat_add(v_size_1028_, v___x_1030_);
v___x_1032_ = lean_array_get_size(v_keyArray_1029_);
v___x_1033_ = lean_nat_dec_lt(v___x_1031_, v___x_1032_);
if (v___x_1033_ == 0)
{
lean_dec(v___x_1031_);
lean_dec(v_index_1007_);
goto v___jp_1018_;
}
else
{
lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; uint8_t v___x_1038_; 
v___x_1034_ = lean_unsigned_to_nat(4u);
v___x_1035_ = lean_nat_mul(v___x_1031_, v___x_1034_);
v___x_1036_ = lean_unsigned_to_nat(3u);
v___x_1037_ = lean_nat_mul(v___x_1032_, v___x_1036_);
v___x_1038_ = lean_nat_dec_le(v___x_1035_, v___x_1037_);
lean_dec(v___x_1037_);
lean_dec(v___x_1035_);
if (v___x_1038_ == 0)
{
lean_dec(v___x_1031_);
lean_dec(v_index_1007_);
goto v___jp_1018_;
}
else
{
lean_object* v___x_1039_; 
v___x_1039_ = l_Std_DHashMap_Raw_setEntry___redArg(v_indexes_976_, v___x_1031_, v_index_1007_, v_val_954_, v_val_1010_);
lean_dec(v_index_1007_);
v___y_984_ = v___x_1039_;
goto v___jp_983_;
}
}
v___jp_1011_:
{
lean_object* v_size_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v_size_1014_ = lean_ctor_get(v___y_1012_, 0);
v___x_1015_ = lean_unsigned_to_nat(1u);
v___x_1016_ = lean_nat_add(v_size_1014_, v___x_1015_);
v___x_1017_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1012_, v___x_1016_, v_i_1013_, v_val_954_, v_val_1010_);
lean_dec(v_i_1013_);
v___y_984_ = v___x_1017_;
goto v___jp_983_;
}
v___jp_1018_:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1019_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Http_Response_Builder_header_spec__1___redArg(v_indexes_976_);
lean_dec_ref(v_indexes_976_);
v___x_1020_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Http_Response_Builder_header_spec__0___redArg(v___x_1019_, v_val_954_);
switch(lean_obj_tag(v___x_1020_))
{
case 0:
{
lean_object* v_index_1021_; lean_object* v_size_1022_; lean_object* v___x_1023_; 
v_index_1021_ = lean_ctor_get(v___x_1020_, 0);
lean_inc(v_index_1021_);
lean_dec_ref_known(v___x_1020_, 3);
v_size_1022_ = lean_ctor_get(v___x_1019_, 0);
lean_inc(v_size_1022_);
v___x_1023_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1019_, v_size_1022_, v_index_1021_, v_val_954_, v_val_1010_);
lean_dec(v_index_1021_);
v___y_984_ = v___x_1023_;
goto v___jp_983_;
}
case 1:
{
lean_object* v_index_1024_; 
v_index_1024_ = lean_ctor_get(v___x_1020_, 0);
lean_inc(v_index_1024_);
lean_dec_ref_known(v___x_1020_, 1);
v___y_1012_ = v___x_1019_;
v_i_1013_ = v_index_1024_;
goto v___jp_1011_;
}
default: 
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = lean_unsigned_to_nat(0u);
v___x_1026_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1019_, v___x_1025_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_object* v_index_1027_; 
v_index_1027_ = lean_ctor_get(v___x_1026_, 0);
lean_inc(v_index_1027_);
lean_dec_ref_known(v___x_1026_, 1);
v___y_1012_ = v___x_1019_;
v_i_1013_ = v_index_1027_;
goto v___jp_1011_;
}
else
{
lean_dec(v_val_1010_);
lean_dec(v_val_954_);
v___y_984_ = v___x_1019_;
goto v___jp_983_;
}
}
}
}
}
default: 
{
lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v_val_1042_; lean_object* v___y_1044_; lean_object* v_i_1045_; lean_object* v___y_1051_; lean_object* v_size_1060_; lean_object* v_keyArray_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; uint8_t v___x_1065_; 
lean_del_object(v___x_956_);
v___x_1040_ = lean_box(0);
v___x_1041_ = l_Std_Http_Response_Builder_header___lam__0(v_i_980_, v___x_1040_);
v_val_1042_ = lean_ctor_get(v___x_1041_, 0);
lean_inc(v_val_1042_);
lean_dec(v___x_1041_);
v_size_1060_ = lean_ctor_get(v_indexes_976_, 0);
v_keyArray_1061_ = lean_ctor_get(v_indexes_976_, 1);
v___x_1062_ = lean_unsigned_to_nat(1u);
v___x_1063_ = lean_nat_add(v_size_1060_, v___x_1062_);
v___x_1064_ = lean_array_get_size(v_keyArray_1061_);
v___x_1065_ = lean_nat_dec_lt(v___x_1063_, v___x_1064_);
if (v___x_1065_ == 0)
{
lean_object* v___x_1066_; 
lean_dec(v___x_1063_);
v___x_1066_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Http_Response_Builder_header_spec__1___redArg(v_indexes_976_);
lean_dec_ref(v_indexes_976_);
v___y_1051_ = v___x_1066_;
goto v___jp_1050_;
}
else
{
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; uint8_t v___x_1071_; 
v___x_1067_ = lean_unsigned_to_nat(4u);
v___x_1068_ = lean_nat_mul(v___x_1063_, v___x_1067_);
lean_dec(v___x_1063_);
v___x_1069_ = lean_unsigned_to_nat(3u);
v___x_1070_ = lean_nat_mul(v___x_1064_, v___x_1069_);
v___x_1071_ = lean_nat_dec_le(v___x_1068_, v___x_1070_);
lean_dec(v___x_1070_);
lean_dec(v___x_1068_);
if (v___x_1071_ == 0)
{
lean_object* v___x_1072_; 
v___x_1072_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Http_Response_Builder_header_spec__1___redArg(v_indexes_976_);
lean_dec_ref(v_indexes_976_);
v___y_1051_ = v___x_1072_;
goto v___jp_1050_;
}
else
{
v___y_1051_ = v_indexes_976_;
goto v___jp_1050_;
}
}
v___jp_1043_:
{
lean_object* v_size_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
v_size_1046_ = lean_ctor_get(v___y_1044_, 0);
v___x_1047_ = lean_unsigned_to_nat(1u);
v___x_1048_ = lean_nat_add(v_size_1046_, v___x_1047_);
v___x_1049_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1044_, v___x_1048_, v_i_1045_, v_val_954_, v_val_1042_);
lean_dec(v_i_1045_);
v___y_984_ = v___x_1049_;
goto v___jp_983_;
}
v___jp_1050_:
{
lean_object* v___x_1052_; 
v___x_1052_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Http_Response_Builder_header_spec__0___redArg(v___y_1051_, v_val_954_);
switch(lean_obj_tag(v___x_1052_))
{
case 0:
{
lean_object* v_index_1053_; lean_object* v_size_1054_; lean_object* v___x_1055_; 
v_index_1053_ = lean_ctor_get(v___x_1052_, 0);
lean_inc(v_index_1053_);
lean_dec_ref_known(v___x_1052_, 3);
v_size_1054_ = lean_ctor_get(v___y_1051_, 0);
lean_inc(v_size_1054_);
v___x_1055_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1051_, v_size_1054_, v_index_1053_, v_val_954_, v_val_1042_);
lean_dec(v_index_1053_);
v___y_984_ = v___x_1055_;
goto v___jp_983_;
}
case 1:
{
lean_object* v_index_1056_; 
v_index_1056_ = lean_ctor_get(v___x_1052_, 0);
lean_inc(v_index_1056_);
lean_dec_ref_known(v___x_1052_, 1);
v___y_1044_ = v___y_1051_;
v_i_1045_ = v_index_1056_;
goto v___jp_1043_;
}
default: 
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1057_ = lean_unsigned_to_nat(0u);
v___x_1058_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1051_, v___x_1057_);
if (lean_obj_tag(v___x_1058_) == 0)
{
lean_object* v_index_1059_; 
v_index_1059_ = lean_ctor_get(v___x_1058_, 0);
lean_inc(v_index_1059_);
lean_dec_ref_known(v___x_1058_, 1);
v___y_1044_ = v___y_1051_;
v_i_1045_ = v_index_1059_;
goto v___jp_1043_;
}
else
{
lean_dec(v_val_1042_);
lean_dec(v_val_954_);
v___y_984_ = v___y_1051_;
goto v___jp_983_;
}
}
}
}
}
}
v___jp_983_:
{
lean_object* v___x_986_; 
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 1, v___y_984_);
lean_ctor_set(v___x_978_, 0, v_entries_982_);
v___x_986_ = v___x_978_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_entries_982_);
lean_ctor_set(v_reuseFailAlloc_996_, 1, v___y_984_);
v___x_986_ = v_reuseFailAlloc_996_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
lean_object* v___x_988_; 
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 1, v___x_986_);
v___x_988_ = v___x_973_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_status_970_);
lean_ctor_set(v_reuseFailAlloc_995_, 1, v___x_986_);
lean_ctor_set_uint8(v_reuseFailAlloc_995_, sizeof(void*)*2, v_version_971_);
v___x_988_ = v_reuseFailAlloc_995_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
lean_object* v___x_990_; 
if (v_isShared_969_ == 0)
{
lean_ctor_set(v___x_968_, 0, v___x_988_);
v___x_990_ = v___x_968_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v___x_988_);
lean_ctor_set(v_reuseFailAlloc_994_, 1, v_extensions_966_);
v___x_990_ = v_reuseFailAlloc_994_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
lean_object* v___x_992_; 
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 0, v___x_990_);
v___x_992_ = v___x_964_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v___x_990_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_extension___redArg(lean_object* v_builder_1081_, lean_object* v_inst_1082_, lean_object* v_data_1083_){
_start:
{
lean_object* v_line_1084_; lean_object* v_extensions_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1096_; 
v_line_1084_ = lean_ctor_get(v_builder_1081_, 0);
v_extensions_1085_ = lean_ctor_get(v_builder_1081_, 1);
v_isSharedCheck_1096_ = !lean_is_exclusive(v_builder_1081_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1087_ = v_builder_1081_;
v_isShared_1088_ = v_isSharedCheck_1096_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_extensions_1085_);
lean_inc(v_line_1084_);
lean_dec(v_builder_1081_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1096_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v_dyn_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1094_; 
v_dyn_1089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_dyn_1089_, 0, v_inst_1082_);
lean_ctor_set(v_dyn_1089_, 1, v_data_1083_);
v___x_1090_ = ((lean_object*)(l_Std_Http_Response_Builder_extension___redArg___closed__0));
v___x_1091_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_dyn_1089_);
v___x_1092_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_1090_, v___x_1091_, v_dyn_1089_, v_extensions_1085_);
if (v_isShared_1088_ == 0)
{
lean_ctor_set(v___x_1087_, 1, v___x_1092_);
v___x_1094_ = v___x_1087_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_line_1084_);
lean_ctor_set(v_reuseFailAlloc_1095_, 1, v___x_1092_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_extension(lean_object* v_00_u03b1_1097_, lean_object* v_builder_1098_, lean_object* v_inst_1099_, lean_object* v_data_1100_){
_start:
{
lean_object* v___x_1101_; 
v___x_1101_ = l_Std_Http_Response_Builder_extension___redArg(v_builder_1098_, v_inst_1099_, v_data_1100_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_body___redArg(lean_object* v_builder_1102_, lean_object* v_body_1103_){
_start:
{
lean_object* v_line_1104_; lean_object* v_extensions_1105_; lean_object* v___x_1106_; 
v_line_1104_ = lean_ctor_get(v_builder_1102_, 0);
v_extensions_1105_ = lean_ctor_get(v_builder_1102_, 1);
lean_inc(v_extensions_1105_);
lean_inc_ref(v_line_1104_);
v___x_1106_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1106_, 0, v_line_1104_);
lean_ctor_set(v___x_1106_, 1, v_body_1103_);
lean_ctor_set(v___x_1106_, 2, v_extensions_1105_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_body___redArg___boxed(lean_object* v_builder_1107_, lean_object* v_body_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l_Std_Http_Response_Builder_body___redArg(v_builder_1107_, v_body_1108_);
lean_dec_ref(v_builder_1107_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_body(lean_object* v_t_1110_, lean_object* v_builder_1111_, lean_object* v_body_1112_){
_start:
{
lean_object* v___x_1113_; 
v___x_1113_ = l_Std_Http_Response_Builder_body___redArg(v_builder_1111_, v_body_1112_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_body___boxed(lean_object* v_t_1114_, lean_object* v_builder_1115_, lean_object* v_body_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Std_Http_Response_Builder_body(v_t_1114_, v_builder_1115_, v_body_1116_);
lean_dec_ref(v_builder_1115_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_build___redArg(lean_object* v_inst_1118_, lean_object* v_builder_1119_){
_start:
{
lean_object* v_line_1120_; lean_object* v_extensions_1121_; lean_object* v___x_1122_; 
v_line_1120_ = lean_ctor_get(v_builder_1119_, 0);
v_extensions_1121_ = lean_ctor_get(v_builder_1119_, 1);
lean_inc(v_extensions_1121_);
lean_inc_ref(v_line_1120_);
v___x_1122_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1122_, 0, v_line_1120_);
lean_ctor_set(v___x_1122_, 1, v_inst_1118_);
lean_ctor_set(v___x_1122_, 2, v_extensions_1121_);
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_build___redArg___boxed(lean_object* v_inst_1123_, lean_object* v_builder_1124_){
_start:
{
lean_object* v_res_1125_; 
v_res_1125_ = l_Std_Http_Response_Builder_build___redArg(v_inst_1123_, v_builder_1124_);
lean_dec_ref(v_builder_1124_);
return v_res_1125_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_build(lean_object* v_t_1126_, lean_object* v_inst_1127_, lean_object* v_builder_1128_){
_start:
{
lean_object* v___x_1129_; 
v___x_1129_ = l_Std_Http_Response_Builder_build___redArg(v_inst_1127_, v_builder_1128_);
return v___x_1129_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_build___boxed(lean_object* v_t_1130_, lean_object* v_inst_1131_, lean_object* v_builder_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_Std_Http_Response_Builder_build(v_t_1130_, v_inst_1131_, v_builder_1132_);
lean_dec_ref(v_builder_1132_);
return v_res_1133_;
}
}
static lean_object* _init_l_Std_Http_Response_ok___closed__0(void){
_start:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1134_ = lean_box(4);
v___x_1135_ = l_Std_Http_Response_Builder_new;
v___x_1136_ = l_Std_Http_Response_Builder_status(v___x_1135_, v___x_1134_);
return v___x_1136_;
}
}
static lean_object* _init_l_Std_Http_Response_ok(void){
_start:
{
lean_object* v___x_1137_; 
v___x_1137_ = lean_obj_once(&l_Std_Http_Response_ok___closed__0, &l_Std_Http_Response_ok___closed__0_once, _init_l_Std_Http_Response_ok___closed__0);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_withStatus(lean_object* v_status_1138_){
_start:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1139_ = l_Std_Http_Response_Builder_new;
v___x_1140_ = l_Std_Http_Response_Builder_status(v___x_1139_, v_status_1138_);
return v___x_1140_;
}
}
static lean_object* _init_l_Std_Http_Response_notFound___closed__0(void){
_start:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1141_ = lean_box(27);
v___x_1142_ = l_Std_Http_Response_Builder_new;
v___x_1143_ = l_Std_Http_Response_Builder_status(v___x_1142_, v___x_1141_);
return v___x_1143_;
}
}
static lean_object* _init_l_Std_Http_Response_notFound(void){
_start:
{
lean_object* v___x_1144_; 
v___x_1144_ = lean_obj_once(&l_Std_Http_Response_notFound___closed__0, &l_Std_Http_Response_notFound___closed__0_once, _init_l_Std_Http_Response_notFound___closed__0);
return v___x_1144_;
}
}
static lean_object* _init_l_Std_Http_Response_internalServerError___closed__0(void){
_start:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1145_ = lean_box(52);
v___x_1146_ = l_Std_Http_Response_Builder_new;
v___x_1147_ = l_Std_Http_Response_Builder_status(v___x_1146_, v___x_1145_);
return v___x_1147_;
}
}
static lean_object* _init_l_Std_Http_Response_internalServerError(void){
_start:
{
lean_object* v___x_1148_; 
v___x_1148_ = lean_obj_once(&l_Std_Http_Response_internalServerError___closed__0, &l_Std_Http_Response_internalServerError___closed__0_once, _init_l_Std_Http_Response_internalServerError___closed__0);
return v___x_1148_;
}
}
static lean_object* _init_l_Std_Http_Response_badRequest___closed__0(void){
_start:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1149_ = lean_box(23);
v___x_1150_ = l_Std_Http_Response_Builder_new;
v___x_1151_ = l_Std_Http_Response_Builder_status(v___x_1150_, v___x_1149_);
return v___x_1151_;
}
}
static lean_object* _init_l_Std_Http_Response_badRequest(void){
_start:
{
lean_object* v___x_1152_; 
v___x_1152_ = lean_obj_once(&l_Std_Http_Response_badRequest___closed__0, &l_Std_Http_Response_badRequest___closed__0_once, _init_l_Std_Http_Response_badRequest___closed__0);
return v___x_1152_;
}
}
static lean_object* _init_l_Std_Http_Response_created___closed__0(void){
_start:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1153_ = lean_box(5);
v___x_1154_ = l_Std_Http_Response_Builder_new;
v___x_1155_ = l_Std_Http_Response_Builder_status(v___x_1154_, v___x_1153_);
return v___x_1155_;
}
}
static lean_object* _init_l_Std_Http_Response_created(void){
_start:
{
lean_object* v___x_1156_; 
v___x_1156_ = lean_obj_once(&l_Std_Http_Response_created___closed__0, &l_Std_Http_Response_created___closed__0_once, _init_l_Std_Http_Response_created___closed__0);
return v___x_1156_;
}
}
static lean_object* _init_l_Std_Http_Response_accepted___closed__0(void){
_start:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1157_ = lean_box(6);
v___x_1158_ = l_Std_Http_Response_Builder_new;
v___x_1159_ = l_Std_Http_Response_Builder_status(v___x_1158_, v___x_1157_);
return v___x_1159_;
}
}
static lean_object* _init_l_Std_Http_Response_accepted(void){
_start:
{
lean_object* v___x_1160_; 
v___x_1160_ = lean_obj_once(&l_Std_Http_Response_accepted___closed__0, &l_Std_Http_Response_accepted___closed__0_once, _init_l_Std_Http_Response_accepted___closed__0);
return v___x_1160_;
}
}
static lean_object* _init_l_Std_Http_Response_unauthorized___closed__0(void){
_start:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1161_ = lean_box(24);
v___x_1162_ = l_Std_Http_Response_Builder_new;
v___x_1163_ = l_Std_Http_Response_Builder_status(v___x_1162_, v___x_1161_);
return v___x_1163_;
}
}
static lean_object* _init_l_Std_Http_Response_unauthorized(void){
_start:
{
lean_object* v___x_1164_; 
v___x_1164_ = lean_obj_once(&l_Std_Http_Response_unauthorized___closed__0, &l_Std_Http_Response_unauthorized___closed__0_once, _init_l_Std_Http_Response_unauthorized___closed__0);
return v___x_1164_;
}
}
static lean_object* _init_l_Std_Http_Response_forbidden___closed__0(void){
_start:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1165_ = lean_box(26);
v___x_1166_ = l_Std_Http_Response_Builder_new;
v___x_1167_ = l_Std_Http_Response_Builder_status(v___x_1166_, v___x_1165_);
return v___x_1167_;
}
}
static lean_object* _init_l_Std_Http_Response_forbidden(void){
_start:
{
lean_object* v___x_1168_; 
v___x_1168_ = lean_obj_once(&l_Std_Http_Response_forbidden___closed__0, &l_Std_Http_Response_forbidden___closed__0_once, _init_l_Std_Http_Response_forbidden___closed__0);
return v___x_1168_;
}
}
static lean_object* _init_l_Std_Http_Response_conflict___closed__0(void){
_start:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1169_ = lean_box(32);
v___x_1170_ = l_Std_Http_Response_Builder_new;
v___x_1171_ = l_Std_Http_Response_Builder_status(v___x_1170_, v___x_1169_);
return v___x_1171_;
}
}
static lean_object* _init_l_Std_Http_Response_conflict(void){
_start:
{
lean_object* v___x_1172_; 
v___x_1172_ = lean_obj_once(&l_Std_Http_Response_conflict___closed__0, &l_Std_Http_Response_conflict___closed__0_once, _init_l_Std_Http_Response_conflict___closed__0);
return v___x_1172_;
}
}
static lean_object* _init_l_Std_Http_Response_serviceUnavailable___closed__0(void){
_start:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1173_ = lean_box(55);
v___x_1174_ = l_Std_Http_Response_Builder_new;
v___x_1175_ = l_Std_Http_Response_Builder_status(v___x_1174_, v___x_1173_);
return v___x_1175_;
}
}
static lean_object* _init_l_Std_Http_Response_serviceUnavailable(void){
_start:
{
lean_object* v___x_1176_; 
v___x_1176_ = lean_obj_once(&l_Std_Http_Response_serviceUnavailable___closed__0, &l_Std_Http_Response_serviceUnavailable___closed__0_once, _init_l_Std_Http_Response_serviceUnavailable___closed__0);
return v___x_1176_;
}
}
lean_object* runtime_initialize_Std_Http_Data_Extensions(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_Status(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_Version(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_Headers(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Data_Response(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Http_Data_Extensions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_Status(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_Version(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_Headers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Http_Response_instInhabitedHead_default = _init_l_Std_Http_Response_instInhabitedHead_default();
lean_mark_persistent(l_Std_Http_Response_instInhabitedHead_default);
l_Std_Http_Response_instInhabitedHead = _init_l_Std_Http_Response_instInhabitedHead();
lean_mark_persistent(l_Std_Http_Response_instInhabitedHead);
l_Std_Http_Response_instToStringHead___lam__1___boxed__const__1 = _init_l_Std_Http_Response_instToStringHead___lam__1___boxed__const__1();
lean_mark_persistent(l_Std_Http_Response_instToStringHead___lam__1___boxed__const__1);
l_Std_Http_Response_new = _init_l_Std_Http_Response_new();
lean_mark_persistent(l_Std_Http_Response_new);
l_Std_Http_Response_Builder_new = _init_l_Std_Http_Response_Builder_new();
lean_mark_persistent(l_Std_Http_Response_Builder_new);
l_Std_Http_Response_ok = _init_l_Std_Http_Response_ok();
lean_mark_persistent(l_Std_Http_Response_ok);
l_Std_Http_Response_notFound = _init_l_Std_Http_Response_notFound();
lean_mark_persistent(l_Std_Http_Response_notFound);
l_Std_Http_Response_internalServerError = _init_l_Std_Http_Response_internalServerError();
lean_mark_persistent(l_Std_Http_Response_internalServerError);
l_Std_Http_Response_badRequest = _init_l_Std_Http_Response_badRequest();
lean_mark_persistent(l_Std_Http_Response_badRequest);
l_Std_Http_Response_created = _init_l_Std_Http_Response_created();
lean_mark_persistent(l_Std_Http_Response_created);
l_Std_Http_Response_accepted = _init_l_Std_Http_Response_accepted();
lean_mark_persistent(l_Std_Http_Response_accepted);
l_Std_Http_Response_unauthorized = _init_l_Std_Http_Response_unauthorized();
lean_mark_persistent(l_Std_Http_Response_unauthorized);
l_Std_Http_Response_forbidden = _init_l_Std_Http_Response_forbidden();
lean_mark_persistent(l_Std_Http_Response_forbidden);
l_Std_Http_Response_conflict = _init_l_Std_Http_Response_conflict();
lean_mark_persistent(l_Std_Http_Response_conflict);
l_Std_Http_Response_serviceUnavailable = _init_l_Std_Http_Response_serviceUnavailable();
lean_mark_persistent(l_Std_Http_Response_serviceUnavailable);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Http_Data_Response(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Http_Data_Extensions(uint8_t builtin);
lean_object* initialize_Std_Http_Data_Status(uint8_t builtin);
lean_object* initialize_Std_Http_Data_Version(uint8_t builtin);
lean_object* initialize_Std_Http_Data_Headers(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Http_Data_Response(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Http_Data_Extensions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Data_Status(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Data_Version(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Data_Headers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_Response(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Http_Data_Response(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Http_Data_Response(builtin);
}
#ifdef __cplusplus
}
#endif
