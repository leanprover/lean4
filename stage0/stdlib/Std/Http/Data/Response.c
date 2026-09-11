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
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Std_Http_Headers_empty;
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___redArg___lam__0___boxed(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_splitToSubslice___redArg(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
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
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
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
static const lean_closure_object l_Std_Http_Response_instToStringHead___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__2___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_header(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
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
lean_object* v_it_117_; lean_object* v_out_118_; lean_object* v___y_134_; uint32_t v___y_135_; lean_object* v___y_136_; uint8_t v___y_137_; lean_object* v_it_143_; lean_object* v_startInclusive_144_; lean_object* v_endExclusive_145_; 
if (lean_obj_tag(v_it_112_) == 0)
{
lean_object* v_currPos_152_; lean_object* v_searcher_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_175_; 
v_currPos_152_ = lean_ctor_get(v_it_112_, 0);
v_searcher_153_ = lean_ctor_get(v_it_112_, 1);
v_isSharedCheck_175_ = !lean_is_exclusive(v_it_112_);
if (v_isSharedCheck_175_ == 0)
{
v___x_155_ = v_it_112_;
v_isShared_156_ = v_isSharedCheck_175_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_searcher_153_);
lean_inc(v_currPos_152_);
lean_dec(v_it_112_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_175_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
uint8_t v_decide_157_; 
v_decide_157_ = lean_nat_dec_eq(v_searcher_153_, v___x_109_);
if (v_decide_157_ == 0)
{
uint32_t v___x_158_; uint8_t v___x_159_; 
lean_dec(v___x_109_);
v___x_158_ = lean_string_utf8_get_fast(v_fst_108_, v_searcher_153_);
v___x_159_ = lean_uint32_dec_eq(v___x_158_, v___x_110_);
if (v___x_159_ == 0)
{
lean_object* v___x_160_; lean_object* v___x_162_; 
v___x_160_ = lean_string_utf8_next_fast(v_fst_108_, v_searcher_153_);
lean_dec(v_searcher_153_);
if (v_isShared_156_ == 0)
{
lean_ctor_set(v___x_155_, 1, v___x_160_);
v___x_162_ = v___x_155_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v_currPos_152_);
lean_ctor_set(v_reuseFailAlloc_164_, 1, v___x_160_);
v___x_162_ = v_reuseFailAlloc_164_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
lean_object* v___x_163_; 
v___x_163_ = lean_apply_4(v_recur_115_, v___x_162_, v_acc_113_, lean_box(0), lean_box(0));
return v___x_163_;
}
}
else
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v_slice_168_; lean_object* v_nextIt_170_; 
v___x_165_ = lean_string_utf8_next_fast(v_fst_108_, v_searcher_153_);
v___x_166_ = lean_nat_sub(v___x_165_, v_searcher_153_);
v___x_167_ = lean_nat_add(v_searcher_153_, v___x_166_);
lean_dec(v___x_166_);
v_slice_168_ = l_String_Slice_subslice_x21(v___x_111_, v_currPos_152_, v_searcher_153_);
lean_inc(v___x_167_);
if (v_isShared_156_ == 0)
{
lean_ctor_set(v___x_155_, 1, v___x_167_);
lean_ctor_set(v___x_155_, 0, v___x_167_);
v_nextIt_170_ = v___x_155_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v___x_167_);
lean_ctor_set(v_reuseFailAlloc_173_, 1, v___x_167_);
v_nextIt_170_ = v_reuseFailAlloc_173_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
lean_object* v_startInclusive_171_; lean_object* v_endExclusive_172_; 
v_startInclusive_171_ = lean_ctor_get(v_slice_168_, 0);
lean_inc(v_startInclusive_171_);
v_endExclusive_172_ = lean_ctor_get(v_slice_168_, 1);
lean_inc(v_endExclusive_172_);
lean_dec_ref(v_slice_168_);
v_it_143_ = v_nextIt_170_;
v_startInclusive_144_ = v_startInclusive_171_;
v_endExclusive_145_ = v_endExclusive_172_;
goto v___jp_142_;
}
}
}
else
{
lean_object* v___x_174_; 
lean_del_object(v___x_155_);
lean_dec(v_searcher_153_);
v___x_174_ = lean_box(1);
v_it_143_ = v___x_174_;
v_startInclusive_144_ = v_currPos_152_;
v_endExclusive_145_ = v___x_109_;
goto v___jp_142_;
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
if (v___y_137_ == 0)
{
lean_object* v___x_138_; 
v___x_138_ = lean_string_utf8_set(v___y_136_, v___x_106_, v___y_135_);
v_it_117_ = v___y_134_;
v_out_118_ = v___x_138_;
goto v___jp_116_;
}
else
{
uint32_t v___x_139_; uint32_t v___x_140_; lean_object* v___x_141_; 
v___x_139_ = 4294967264;
v___x_140_ = lean_uint32_add(v___y_135_, v___x_139_);
v___x_141_ = lean_string_utf8_set(v___y_136_, v___x_106_, v___x_140_);
v_it_117_ = v___y_134_;
v_out_118_ = v___x_141_;
goto v___jp_116_;
}
}
v___jp_142_:
{
lean_object* v___x_146_; uint32_t v___x_147_; uint32_t v___x_148_; uint8_t v___x_149_; 
v___x_146_ = lean_string_utf8_extract_fast(v_fst_108_, v_startInclusive_144_, v_endExclusive_145_);
lean_dec(v_endExclusive_145_);
lean_dec(v_startInclusive_144_);
v___x_147_ = lean_string_utf8_get(v___x_146_, v___x_106_);
v___x_148_ = 97;
v___x_149_ = lean_uint32_dec_le(v___x_148_, v___x_147_);
if (v___x_149_ == 0)
{
v___y_134_ = v_it_143_;
v___y_135_ = v___x_147_;
v___y_136_ = v___x_146_;
v___y_137_ = v___x_149_;
goto v___jp_133_;
}
else
{
uint32_t v___x_150_; uint8_t v___x_151_; 
v___x_150_ = 122;
v___x_151_ = lean_uint32_dec_le(v___x_147_, v___x_150_);
v___y_134_ = v_it_143_;
v___y_135_ = v___x_147_;
v___y_136_ = v___x_146_;
v___y_137_ = v___x_151_;
goto v___jp_133_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instToStringHead___lam__0___boxed(lean_object* v___x_176_, lean_object* v___x_177_, lean_object* v___x_178_, lean_object* v_fst_179_, lean_object* v___x_180_, lean_object* v___x_181_, lean_object* v___x_182_, lean_object* v_it_183_, lean_object* v_acc_184_, lean_object* v_hP_185_, lean_object* v_recur_186_){
_start:
{
uint32_t v___x_781__boxed_187_; lean_object* v_res_188_; 
v___x_781__boxed_187_ = lean_unbox_uint32(v___x_181_);
lean_dec(v___x_181_);
v_res_188_ = l_Std_Http_Response_instToStringHead___lam__0(v___x_176_, v___x_177_, v___x_178_, v_fst_179_, v___x_180_, v___x_781__boxed_187_, v___x_182_, v_it_183_, v_acc_184_, v_hP_185_, v_recur_186_);
lean_dec_ref(v___x_182_);
lean_dec_ref(v_fst_179_);
lean_dec(v___x_178_);
lean_dec(v___x_177_);
lean_dec_ref(v___x_176_);
return v_res_188_;
}
}
static lean_object* _init_l_Std_Http_Response_instToStringHead___lam__1___closed__3(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_192_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__1___closed__2));
v___x_193_ = lean_string_utf8_byte_size(v___x_192_);
return v___x_193_;
}
}
static lean_object* _init_l_Std_Http_Response_instToStringHead___lam__1___boxed__const__1(void){
_start:
{
uint32_t v___x_195_; lean_object* v___x_196_; 
v___x_195_ = 45;
v___x_196_ = lean_box_uint32(v___x_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instToStringHead___lam__1(lean_object* v_x_197_){
_start:
{
lean_object* v_fst_198_; lean_object* v_snd_199_; lean_object* v___y_201_; lean_object* v___f_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v_it_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___f_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v_fst_198_ = lean_ctor_get(v_x_197_, 0);
lean_inc_n(v_fst_198_, 2);
v_snd_199_ = lean_ctor_get(v_x_197_, 1);
lean_inc(v_snd_199_);
lean_dec_ref(v_x_197_);
v___f_205_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__1___closed__1));
v___x_206_ = lean_unsigned_to_nat(0u);
v___x_207_ = lean_string_utf8_byte_size(v_fst_198_);
v___x_208_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_208_, 0, v_fst_198_);
lean_ctor_set(v___x_208_, 1, v___x_206_);
lean_ctor_set(v___x_208_, 2, v___x_207_);
lean_inc_ref(v___x_208_);
v_it_209_ = l_String_Slice_splitToSubslice___redArg(v___x_208_, v___f_205_);
v___x_210_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__1___closed__2));
v___x_211_ = lean_obj_once(&l_Std_Http_Response_instToStringHead___lam__1___closed__3, &l_Std_Http_Response_instToStringHead___lam__1___closed__3_once, _init_l_Std_Http_Response_instToStringHead___lam__1___closed__3);
v___x_212_ = l_Std_Http_Response_instToStringHead___lam__1___boxed__const__1;
v___f_213_ = lean_alloc_closure((void*)(l_Std_Http_Response_instToStringHead___lam__0___boxed), 11, 7);
lean_closure_set(v___f_213_, 0, v___x_210_);
lean_closure_set(v___f_213_, 1, v___x_206_);
lean_closure_set(v___f_213_, 2, v___x_211_);
lean_closure_set(v___f_213_, 3, v_fst_198_);
lean_closure_set(v___f_213_, 4, v___x_207_);
lean_closure_set(v___f_213_, 5, v___x_212_);
lean_closure_set(v___f_213_, 6, v___x_208_);
v___x_214_ = lean_box(0);
v___x_215_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_213_, v_it_209_, v___x_214_, lean_box(0));
if (lean_obj_tag(v___x_215_) == 0)
{
lean_object* v___x_216_; 
v___x_216_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__1___closed__4));
v___y_201_ = v___x_216_;
goto v___jp_200_;
}
else
{
lean_object* v_val_217_; 
v_val_217_ = lean_ctor_get(v___x_215_, 0);
lean_inc(v_val_217_);
lean_dec_ref_known(v___x_215_, 1);
v___y_201_ = v_val_217_;
goto v___jp_200_;
}
v___jp_200_:
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_202_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__1___closed__0));
v___x_203_ = lean_string_append(v___y_201_, v___x_202_);
v___x_204_ = lean_string_append(v___x_203_, v_snd_199_);
lean_dec(v_snd_199_);
return v___x_204_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instToStringHead___lam__2(lean_object* v___f_243_, lean_object* v_r_244_){
_start:
{
lean_object* v_status_245_; uint8_t v_version_246_; lean_object* v_headers_247_; lean_object* v___y_249_; 
v_status_245_ = lean_ctor_get(v_r_244_, 0);
lean_inc(v_status_245_);
v_version_246_ = lean_ctor_get_uint8(v_r_244_, sizeof(void*)*2);
v_headers_247_ = lean_ctor_get(v_r_244_, 1);
lean_inc_ref(v_headers_247_);
lean_dec_ref(v_r_244_);
switch(v_version_246_)
{
case 0:
{
lean_object* v___x_270_; 
v___x_270_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__12));
v___y_249_ = v___x_270_;
goto v___jp_248_;
}
case 1:
{
lean_object* v___x_271_; 
v___x_271_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__13));
v___y_249_ = v___x_271_;
goto v___jp_248_;
}
case 2:
{
lean_object* v___x_272_; 
v___x_272_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__14));
v___y_249_ = v___x_272_;
goto v___jp_248_;
}
default: 
{
lean_object* v___x_273_; 
v___x_273_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__15));
v___y_249_ = v___x_273_;
goto v___jp_248_;
}
}
v___jp_248_:
{
lean_object* v_entries_250_; lean_object* v___x_251_; lean_object* v___x_252_; uint16_t v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; size_t v_sz_263_; size_t v___x_264_; lean_object* v_pairs_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v_entries_250_ = lean_ctor_get(v_headers_247_, 0);
lean_inc_ref(v_entries_250_);
lean_dec_ref(v_headers_247_);
v___x_251_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__0));
lean_inc_ref(v___y_249_);
v___x_252_ = lean_string_append(v___y_249_, v___x_251_);
v___x_253_ = l_Std_Http_Status_toCode(v_status_245_);
v___x_254_ = lean_uint16_to_nat(v___x_253_);
v___x_255_ = l_Nat_reprFast(v___x_254_);
v___x_256_ = lean_string_append(v___x_252_, v___x_255_);
lean_dec_ref(v___x_255_);
v___x_257_ = lean_string_append(v___x_256_, v___x_251_);
v___x_258_ = l_Std_Http_Status_reasonPhrase(v_status_245_);
lean_dec(v_status_245_);
v___x_259_ = lean_string_append(v___x_257_, v___x_258_);
lean_dec_ref(v___x_258_);
v___x_260_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__1));
v___x_261_ = lean_string_append(v___x_259_, v___x_260_);
v___x_262_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__11));
v_sz_263_ = lean_array_size(v_entries_250_);
v___x_264_ = ((size_t)0ULL);
v_pairs_265_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_262_, v___f_243_, v_sz_263_, v___x_264_, v_entries_250_);
v___x_266_ = lean_array_to_list(v_pairs_265_);
v___x_267_ = l_String_intercalate(v___x_260_, v___x_266_);
v___x_268_ = lean_string_append(v___x_261_, v___x_267_);
lean_dec_ref(v___x_267_);
v___x_269_ = lean_string_append(v___x_268_, v___x_260_);
return v___x_269_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instEncodeV11Head___lam__0(lean_object* v___x_278_, lean_object* v___x_279_, lean_object* v___x_280_, lean_object* v_name_281_, lean_object* v___x_282_, uint32_t v___x_283_, lean_object* v___x_284_, lean_object* v_it_285_, lean_object* v_acc_286_, lean_object* v_hP_287_, lean_object* v_recur_288_){
_start:
{
lean_object* v_it_290_; lean_object* v_out_291_; uint32_t v___y_307_; lean_object* v___y_308_; lean_object* v___y_309_; uint8_t v___y_310_; lean_object* v_it_316_; lean_object* v_startInclusive_317_; lean_object* v_endExclusive_318_; 
if (lean_obj_tag(v_it_285_) == 0)
{
lean_object* v_currPos_325_; lean_object* v_searcher_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_348_; 
v_currPos_325_ = lean_ctor_get(v_it_285_, 0);
v_searcher_326_ = lean_ctor_get(v_it_285_, 1);
v_isSharedCheck_348_ = !lean_is_exclusive(v_it_285_);
if (v_isSharedCheck_348_ == 0)
{
v___x_328_ = v_it_285_;
v_isShared_329_ = v_isSharedCheck_348_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_searcher_326_);
lean_inc(v_currPos_325_);
lean_dec(v_it_285_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_348_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
uint8_t v_decide_330_; 
v_decide_330_ = lean_nat_dec_eq(v_searcher_326_, v___x_282_);
if (v_decide_330_ == 0)
{
uint32_t v___x_331_; uint8_t v___x_332_; 
lean_dec(v___x_282_);
v___x_331_ = lean_string_utf8_get_fast(v_name_281_, v_searcher_326_);
v___x_332_ = lean_uint32_dec_eq(v___x_331_, v___x_283_);
if (v___x_332_ == 0)
{
lean_object* v___x_333_; lean_object* v___x_335_; 
v___x_333_ = lean_string_utf8_next_fast(v_name_281_, v_searcher_326_);
lean_dec(v_searcher_326_);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 1, v___x_333_);
v___x_335_ = v___x_328_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v_currPos_325_);
lean_ctor_set(v_reuseFailAlloc_337_, 1, v___x_333_);
v___x_335_ = v_reuseFailAlloc_337_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
lean_object* v___x_336_; 
v___x_336_ = lean_apply_4(v_recur_288_, v___x_335_, v_acc_286_, lean_box(0), lean_box(0));
return v___x_336_;
}
}
else
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v_slice_341_; lean_object* v_nextIt_343_; 
v___x_338_ = lean_string_utf8_next_fast(v_name_281_, v_searcher_326_);
v___x_339_ = lean_nat_sub(v___x_338_, v_searcher_326_);
v___x_340_ = lean_nat_add(v_searcher_326_, v___x_339_);
lean_dec(v___x_339_);
v_slice_341_ = l_String_Slice_subslice_x21(v___x_284_, v_currPos_325_, v_searcher_326_);
lean_inc(v___x_340_);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 1, v___x_340_);
lean_ctor_set(v___x_328_, 0, v___x_340_);
v_nextIt_343_ = v___x_328_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_340_);
lean_ctor_set(v_reuseFailAlloc_346_, 1, v___x_340_);
v_nextIt_343_ = v_reuseFailAlloc_346_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
lean_object* v_startInclusive_344_; lean_object* v_endExclusive_345_; 
v_startInclusive_344_ = lean_ctor_get(v_slice_341_, 0);
lean_inc(v_startInclusive_344_);
v_endExclusive_345_ = lean_ctor_get(v_slice_341_, 1);
lean_inc(v_endExclusive_345_);
lean_dec_ref(v_slice_341_);
v_it_316_ = v_nextIt_343_;
v_startInclusive_317_ = v_startInclusive_344_;
v_endExclusive_318_ = v_endExclusive_345_;
goto v___jp_315_;
}
}
}
else
{
lean_object* v___x_347_; 
lean_del_object(v___x_328_);
lean_dec(v_searcher_326_);
v___x_347_ = lean_box(1);
v_it_316_ = v___x_347_;
v_startInclusive_317_ = v_currPos_325_;
v_endExclusive_318_ = v___x_282_;
goto v___jp_315_;
}
}
}
else
{
lean_dec_ref(v_recur_288_);
lean_dec(v___x_282_);
return v_acc_286_;
}
v___jp_289_:
{
if (lean_obj_tag(v_acc_286_) == 0)
{
lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_292_, 0, v_out_291_);
v___x_293_ = lean_apply_4(v_recur_288_, v_it_290_, v___x_292_, lean_box(0), lean_box(0));
return v___x_293_;
}
else
{
lean_object* v_val_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_305_; 
v_val_294_ = lean_ctor_get(v_acc_286_, 0);
v_isSharedCheck_305_ = !lean_is_exclusive(v_acc_286_);
if (v_isSharedCheck_305_ == 0)
{
v___x_296_ = v_acc_286_;
v_isShared_297_ = v_isSharedCheck_305_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_val_294_);
lean_dec(v_acc_286_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_305_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_302_; 
v___x_298_ = lean_string_utf8_extract_fast(v___x_278_, v___x_279_, v___x_280_);
v___x_299_ = lean_string_append(v_val_294_, v___x_298_);
lean_dec_ref(v___x_298_);
v___x_300_ = lean_string_append(v___x_299_, v_out_291_);
lean_dec_ref(v_out_291_);
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 0, v___x_300_);
v___x_302_ = v___x_296_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v___x_300_);
v___x_302_ = v_reuseFailAlloc_304_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
lean_object* v___x_303_; 
v___x_303_ = lean_apply_4(v_recur_288_, v_it_290_, v___x_302_, lean_box(0), lean_box(0));
return v___x_303_;
}
}
}
}
v___jp_306_:
{
if (v___y_310_ == 0)
{
lean_object* v___x_311_; 
v___x_311_ = lean_string_utf8_set(v___y_308_, v___x_279_, v___y_307_);
v_it_290_ = v___y_309_;
v_out_291_ = v___x_311_;
goto v___jp_289_;
}
else
{
uint32_t v___x_312_; uint32_t v___x_313_; lean_object* v___x_314_; 
v___x_312_ = 4294967264;
v___x_313_ = lean_uint32_add(v___y_307_, v___x_312_);
v___x_314_ = lean_string_utf8_set(v___y_308_, v___x_279_, v___x_313_);
v_it_290_ = v___y_309_;
v_out_291_ = v___x_314_;
goto v___jp_289_;
}
}
v___jp_315_:
{
lean_object* v___x_319_; uint32_t v___x_320_; uint32_t v___x_321_; uint8_t v___x_322_; 
v___x_319_ = lean_string_utf8_extract_fast(v_name_281_, v_startInclusive_317_, v_endExclusive_318_);
lean_dec(v_endExclusive_318_);
lean_dec(v_startInclusive_317_);
v___x_320_ = lean_string_utf8_get(v___x_319_, v___x_279_);
v___x_321_ = 97;
v___x_322_ = lean_uint32_dec_le(v___x_321_, v___x_320_);
if (v___x_322_ == 0)
{
v___y_307_ = v___x_320_;
v___y_308_ = v___x_319_;
v___y_309_ = v_it_316_;
v___y_310_ = v___x_322_;
goto v___jp_306_;
}
else
{
uint32_t v___x_323_; uint8_t v___x_324_; 
v___x_323_ = 122;
v___x_324_ = lean_uint32_dec_le(v___x_320_, v___x_323_);
v___y_307_ = v___x_320_;
v___y_308_ = v___x_319_;
v___y_309_ = v_it_316_;
v___y_310_ = v___x_324_;
goto v___jp_306_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instEncodeV11Head___lam__0___boxed(lean_object* v___x_349_, lean_object* v___x_350_, lean_object* v___x_351_, lean_object* v_name_352_, lean_object* v___x_353_, lean_object* v___x_354_, lean_object* v___x_355_, lean_object* v_it_356_, lean_object* v_acc_357_, lean_object* v_hP_358_, lean_object* v_recur_359_){
_start:
{
uint32_t v___x_1241__boxed_360_; lean_object* v_res_361_; 
v___x_1241__boxed_360_ = lean_unbox_uint32(v___x_354_);
lean_dec(v___x_354_);
v_res_361_ = l_Std_Http_Response_instEncodeV11Head___lam__0(v___x_349_, v___x_350_, v___x_351_, v_name_352_, v___x_353_, v___x_1241__boxed_360_, v___x_355_, v_it_356_, v_acc_357_, v_hP_358_, v_recur_359_);
lean_dec_ref(v___x_355_);
lean_dec_ref(v_name_352_);
lean_dec(v___x_351_);
lean_dec(v___x_350_);
lean_dec_ref(v___x_349_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instEncodeV11Head___lam__1(lean_object* v_buf_362_, lean_object* v_name_363_, lean_object* v_value_364_){
_start:
{
lean_object* v___y_366_; lean_object* v___f_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v_it_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___f_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v___f_385_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__1___closed__1));
v___x_386_ = lean_unsigned_to_nat(0u);
v___x_387_ = lean_string_utf8_byte_size(v_name_363_);
lean_inc_ref(v_name_363_);
v___x_388_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_388_, 0, v_name_363_);
lean_ctor_set(v___x_388_, 1, v___x_386_);
lean_ctor_set(v___x_388_, 2, v___x_387_);
lean_inc_ref(v___x_388_);
v_it_389_ = l_String_Slice_splitToSubslice___redArg(v___x_388_, v___f_385_);
v___x_390_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__1___closed__2));
v___x_391_ = lean_obj_once(&l_Std_Http_Response_instToStringHead___lam__1___closed__3, &l_Std_Http_Response_instToStringHead___lam__1___closed__3_once, _init_l_Std_Http_Response_instToStringHead___lam__1___closed__3);
v___x_392_ = l_Std_Http_Response_instToStringHead___lam__1___boxed__const__1;
v___f_393_ = lean_alloc_closure((void*)(l_Std_Http_Response_instEncodeV11Head___lam__0___boxed), 11, 7);
lean_closure_set(v___f_393_, 0, v___x_390_);
lean_closure_set(v___f_393_, 1, v___x_386_);
lean_closure_set(v___f_393_, 2, v___x_391_);
lean_closure_set(v___f_393_, 3, v_name_363_);
lean_closure_set(v___f_393_, 4, v___x_387_);
lean_closure_set(v___f_393_, 5, v___x_392_);
lean_closure_set(v___f_393_, 6, v___x_388_);
v___x_394_ = lean_box(0);
v___x_395_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_393_, v_it_389_, v___x_394_, lean_box(0));
if (lean_obj_tag(v___x_395_) == 0)
{
lean_object* v___x_396_; 
v___x_396_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__1___closed__4));
v___y_366_ = v___x_396_;
goto v___jp_365_;
}
else
{
lean_object* v_val_397_; 
v_val_397_ = lean_ctor_get(v___x_395_, 0);
lean_inc(v_val_397_);
lean_dec_ref_known(v___x_395_, 1);
v___y_366_ = v_val_397_;
goto v___jp_365_;
}
v___jp_365_:
{
lean_object* v_data_367_; lean_object* v_size_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_384_; 
v_data_367_ = lean_ctor_get(v_buf_362_, 0);
v_size_368_ = lean_ctor_get(v_buf_362_, 1);
v_isSharedCheck_384_ = !lean_is_exclusive(v_buf_362_);
if (v_isSharedCheck_384_ == 0)
{
v___x_370_ = v_buf_362_;
v_isShared_371_ = v_isSharedCheck_384_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_size_368_);
lean_inc(v_data_367_);
lean_dec(v_buf_362_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_384_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_382_; 
v___x_372_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__1___closed__0));
v___x_373_ = lean_string_append(v___y_366_, v___x_372_);
v___x_374_ = lean_string_append(v___x_373_, v_value_364_);
v___x_375_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__1));
v___x_376_ = lean_string_append(v___x_374_, v___x_375_);
v___x_377_ = lean_string_to_utf8(v___x_376_);
lean_dec_ref(v___x_376_);
lean_inc_ref(v___x_377_);
v___x_378_ = lean_array_push(v_data_367_, v___x_377_);
v___x_379_ = lean_byte_array_size(v___x_377_);
lean_dec_ref(v___x_377_);
v___x_380_ = lean_nat_add(v_size_368_, v___x_379_);
lean_dec(v_size_368_);
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 1, v___x_380_);
lean_ctor_set(v___x_370_, 0, v___x_378_);
v___x_382_ = v___x_370_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v___x_378_);
lean_ctor_set(v_reuseFailAlloc_383_, 1, v___x_380_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instEncodeV11Head___lam__1___boxed(lean_object* v_buf_398_, lean_object* v_name_399_, lean_object* v_value_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Std_Http_Response_instEncodeV11Head___lam__1(v_buf_398_, v_name_399_, v_value_400_);
lean_dec_ref(v_value_400_);
return v_res_401_;
}
}
static uint8_t _init_l_Std_Http_Response_instEncodeV11Head___lam__2___closed__0(void){
_start:
{
uint32_t v___x_402_; uint8_t v___x_403_; 
v___x_402_ = 32;
v___x_403_ = lean_uint32_to_uint8(v___x_402_);
return v___x_403_;
}
}
static lean_object* _init_l_Std_Http_Response_instEncodeV11Head___lam__2___closed__1(void){
_start:
{
uint8_t v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_404_ = lean_uint8_once(&l_Std_Http_Response_instEncodeV11Head___lam__2___closed__0, &l_Std_Http_Response_instEncodeV11Head___lam__2___closed__0_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__2___closed__0);
v___x_405_ = lean_unsigned_to_nat(1u);
v___x_406_ = lean_mk_empty_array_with_capacity(v___x_405_);
v___x_407_ = lean_box(v___x_404_);
v___x_408_ = lean_array_push(v___x_406_, v___x_407_);
v___x_409_ = lean_byte_array_mk(v___x_408_);
return v___x_409_;
}
}
static lean_object* _init_l_Std_Http_Response_instEncodeV11Head___lam__2___closed__2(void){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_410_ = lean_obj_once(&l_Std_Http_Response_instEncodeV11Head___lam__2___closed__1, &l_Std_Http_Response_instEncodeV11Head___lam__2___closed__1_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__2___closed__1);
v___x_411_ = lean_byte_array_size(v___x_410_);
return v___x_411_;
}
}
static lean_object* _init_l_Std_Http_Response_instEncodeV11Head___lam__2___closed__3(void){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_412_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__1));
v___x_413_ = lean_string_to_utf8(v___x_412_);
return v___x_413_;
}
}
static lean_object* _init_l_Std_Http_Response_instEncodeV11Head___lam__2___closed__4(void){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_414_ = lean_obj_once(&l_Std_Http_Response_instEncodeV11Head___lam__2___closed__3, &l_Std_Http_Response_instEncodeV11Head___lam__2___closed__3_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__2___closed__3);
v___x_415_ = lean_byte_array_size(v___x_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instEncodeV11Head___lam__2(lean_object* v___f_416_, lean_object* v_buffer_417_, lean_object* v_r_418_){
_start:
{
lean_object* v_status_419_; uint8_t v_version_420_; lean_object* v_headers_421_; lean_object* v___y_423_; 
v_status_419_ = lean_ctor_get(v_r_418_, 0);
v_version_420_ = lean_ctor_get_uint8(v_r_418_, sizeof(void*)*2);
v_headers_421_ = lean_ctor_get(v_r_418_, 1);
switch(v_version_420_)
{
case 0:
{
lean_object* v___x_471_; 
v___x_471_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__12));
v___y_423_ = v___x_471_;
goto v___jp_422_;
}
case 1:
{
lean_object* v___x_472_; 
v___x_472_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__13));
v___y_423_ = v___x_472_;
goto v___jp_422_;
}
case 2:
{
lean_object* v___x_473_; 
v___x_473_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__14));
v___y_423_ = v___x_473_;
goto v___jp_422_;
}
default: 
{
lean_object* v___x_474_; 
v___x_474_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__15));
v___y_423_ = v___x_474_;
goto v___jp_422_;
}
}
v___jp_422_:
{
lean_object* v_data_424_; lean_object* v_size_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_470_; 
v_data_424_ = lean_ctor_get(v_buffer_417_, 0);
v_size_425_ = lean_ctor_get(v_buffer_417_, 1);
v_isSharedCheck_470_ = !lean_is_exclusive(v_buffer_417_);
if (v_isSharedCheck_470_ == 0)
{
v___x_427_ = v_buffer_417_;
v_isShared_428_ = v_isSharedCheck_470_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_size_425_);
lean_inc(v_data_424_);
lean_dec(v_buffer_417_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_470_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; uint16_t v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v_buffer_456_; 
v___x_429_ = lean_string_to_utf8(v___y_423_);
lean_inc_ref(v___x_429_);
v___x_430_ = lean_array_push(v_data_424_, v___x_429_);
v___x_431_ = lean_byte_array_size(v___x_429_);
lean_dec_ref(v___x_429_);
v___x_432_ = lean_nat_add(v_size_425_, v___x_431_);
lean_dec(v_size_425_);
v___x_433_ = lean_obj_once(&l_Std_Http_Response_instEncodeV11Head___lam__2___closed__1, &l_Std_Http_Response_instEncodeV11Head___lam__2___closed__1_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__2___closed__1);
v___x_434_ = lean_array_push(v___x_430_, v___x_433_);
v___x_435_ = lean_obj_once(&l_Std_Http_Response_instEncodeV11Head___lam__2___closed__2, &l_Std_Http_Response_instEncodeV11Head___lam__2___closed__2_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__2___closed__2);
v___x_436_ = lean_nat_add(v___x_432_, v___x_435_);
lean_dec(v___x_432_);
v___x_437_ = l_Std_Http_Status_toCode(v_status_419_);
v___x_438_ = lean_uint16_to_nat(v___x_437_);
v___x_439_ = l_Nat_reprFast(v___x_438_);
v___x_440_ = lean_string_to_utf8(v___x_439_);
lean_dec_ref(v___x_439_);
lean_inc_ref(v___x_440_);
v___x_441_ = lean_array_push(v___x_434_, v___x_440_);
v___x_442_ = lean_byte_array_size(v___x_440_);
lean_dec_ref(v___x_440_);
v___x_443_ = lean_nat_add(v___x_436_, v___x_442_);
lean_dec(v___x_436_);
v___x_444_ = lean_array_push(v___x_441_, v___x_433_);
v___x_445_ = lean_nat_add(v___x_443_, v___x_435_);
lean_dec(v___x_443_);
v___x_446_ = l_Std_Http_Status_reasonPhrase(v_status_419_);
v___x_447_ = lean_string_to_utf8(v___x_446_);
lean_dec_ref(v___x_446_);
lean_inc_ref(v___x_447_);
v___x_448_ = lean_array_push(v___x_444_, v___x_447_);
v___x_449_ = lean_byte_array_size(v___x_447_);
lean_dec_ref(v___x_447_);
v___x_450_ = lean_nat_add(v___x_445_, v___x_449_);
lean_dec(v___x_445_);
v___x_451_ = lean_obj_once(&l_Std_Http_Response_instEncodeV11Head___lam__2___closed__3, &l_Std_Http_Response_instEncodeV11Head___lam__2___closed__3_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__2___closed__3);
v___x_452_ = lean_array_push(v___x_448_, v___x_451_);
v___x_453_ = lean_obj_once(&l_Std_Http_Response_instEncodeV11Head___lam__2___closed__4, &l_Std_Http_Response_instEncodeV11Head___lam__2___closed__4_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__2___closed__4);
v___x_454_ = lean_nat_add(v___x_450_, v___x_453_);
lean_dec(v___x_450_);
if (v_isShared_428_ == 0)
{
lean_ctor_set(v___x_427_, 1, v___x_454_);
lean_ctor_set(v___x_427_, 0, v___x_452_);
v_buffer_456_ = v___x_427_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_452_);
lean_ctor_set(v_reuseFailAlloc_469_, 1, v___x_454_);
v_buffer_456_ = v_reuseFailAlloc_469_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
lean_object* v_buffer_457_; lean_object* v_data_458_; lean_object* v_size_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_468_; 
v_buffer_457_ = l_Std_Http_Headers_fold___redArg(v_headers_421_, v_buffer_456_, v___f_416_);
v_data_458_ = lean_ctor_get(v_buffer_457_, 0);
v_size_459_ = lean_ctor_get(v_buffer_457_, 1);
v_isSharedCheck_468_ = !lean_is_exclusive(v_buffer_457_);
if (v_isSharedCheck_468_ == 0)
{
v___x_461_ = v_buffer_457_;
v_isShared_462_ = v_isSharedCheck_468_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_size_459_);
lean_inc(v_data_458_);
lean_dec(v_buffer_457_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_468_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_466_; 
v___x_463_ = lean_array_push(v_data_458_, v___x_451_);
v___x_464_ = lean_nat_add(v_size_459_, v___x_453_);
lean_dec(v_size_459_);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 1, v___x_464_);
lean_ctor_set(v___x_461_, 0, v___x_463_);
v___x_466_ = v___x_461_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v___x_463_);
lean_ctor_set(v_reuseFailAlloc_467_, 1, v___x_464_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instEncodeV11Head___lam__2___boxed(lean_object* v___f_475_, lean_object* v_buffer_476_, lean_object* v_r_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l_Std_Http_Response_instEncodeV11Head___lam__2(v___f_475_, v_buffer_476_, v_r_477_);
lean_dec_ref(v_r_477_);
return v_res_478_;
}
}
static lean_object* _init_l_Std_Http_Response_new___closed__0(void){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_483_ = l_Std_Http_Extensions_empty;
v___x_484_ = lean_obj_once(&l_Std_Http_Response_instInhabitedHead_default___closed__0, &l_Std_Http_Response_instInhabitedHead_default___closed__0_once, _init_l_Std_Http_Response_instInhabitedHead_default___closed__0);
v___x_485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_485_, 0, v___x_484_);
lean_ctor_set(v___x_485_, 1, v___x_483_);
return v___x_485_;
}
}
static lean_object* _init_l_Std_Http_Response_new(void){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = lean_obj_once(&l_Std_Http_Response_new___closed__0, &l_Std_Http_Response_new___closed__0_once, _init_l_Std_Http_Response_new___closed__0);
return v___x_486_;
}
}
static lean_object* _init_l_Std_Http_Response_Builder_new(void){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = lean_obj_once(&l_Std_Http_Response_new___closed__0, &l_Std_Http_Response_new___closed__0_once, _init_l_Std_Http_Response_new___closed__0);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_status(lean_object* v_builder_488_, lean_object* v_status_489_){
_start:
{
lean_object* v_line_490_; lean_object* v_extensions_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_508_; 
v_line_490_ = lean_ctor_get(v_builder_488_, 0);
v_extensions_491_ = lean_ctor_get(v_builder_488_, 1);
v_isSharedCheck_508_ = !lean_is_exclusive(v_builder_488_);
if (v_isSharedCheck_508_ == 0)
{
v___x_493_ = v_builder_488_;
v_isShared_494_ = v_isSharedCheck_508_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_extensions_491_);
lean_inc(v_line_490_);
lean_dec(v_builder_488_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_508_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
uint8_t v_version_495_; lean_object* v_headers_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_506_; 
v_version_495_ = lean_ctor_get_uint8(v_line_490_, sizeof(void*)*2);
v_headers_496_ = lean_ctor_get(v_line_490_, 1);
v_isSharedCheck_506_ = !lean_is_exclusive(v_line_490_);
if (v_isSharedCheck_506_ == 0)
{
lean_object* v_unused_507_; 
v_unused_507_ = lean_ctor_get(v_line_490_, 0);
lean_dec(v_unused_507_);
v___x_498_ = v_line_490_;
v_isShared_499_ = v_isSharedCheck_506_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_headers_496_);
lean_dec(v_line_490_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_506_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_501_; 
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 0, v_status_489_);
v___x_501_ = v___x_498_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_status_489_);
lean_ctor_set(v_reuseFailAlloc_505_, 1, v_headers_496_);
lean_ctor_set_uint8(v_reuseFailAlloc_505_, sizeof(void*)*2, v_version_495_);
v___x_501_ = v_reuseFailAlloc_505_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
lean_object* v___x_503_; 
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 0, v___x_501_);
v___x_503_ = v___x_493_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v___x_501_);
lean_ctor_set(v_reuseFailAlloc_504_, 1, v_extensions_491_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_headers(lean_object* v_builder_509_, lean_object* v_headers_510_){
_start:
{
lean_object* v_line_511_; lean_object* v_extensions_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_529_; 
v_line_511_ = lean_ctor_get(v_builder_509_, 0);
v_extensions_512_ = lean_ctor_get(v_builder_509_, 1);
v_isSharedCheck_529_ = !lean_is_exclusive(v_builder_509_);
if (v_isSharedCheck_529_ == 0)
{
v___x_514_ = v_builder_509_;
v_isShared_515_ = v_isSharedCheck_529_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_extensions_512_);
lean_inc(v_line_511_);
lean_dec(v_builder_509_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_529_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v_status_516_; uint8_t v_version_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_527_; 
v_status_516_ = lean_ctor_get(v_line_511_, 0);
v_version_517_ = lean_ctor_get_uint8(v_line_511_, sizeof(void*)*2);
v_isSharedCheck_527_ = !lean_is_exclusive(v_line_511_);
if (v_isSharedCheck_527_ == 0)
{
lean_object* v_unused_528_; 
v_unused_528_ = lean_ctor_get(v_line_511_, 1);
lean_dec(v_unused_528_);
v___x_519_ = v_line_511_;
v_isShared_520_ = v_isSharedCheck_527_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_status_516_);
lean_dec(v_line_511_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_527_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_522_; 
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 1, v_headers_510_);
v___x_522_ = v___x_519_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_status_516_);
lean_ctor_set(v_reuseFailAlloc_526_, 1, v_headers_510_);
lean_ctor_set_uint8(v_reuseFailAlloc_526_, sizeof(void*)*2, v_version_517_);
v___x_522_ = v_reuseFailAlloc_526_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
lean_object* v___x_524_; 
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 0, v___x_522_);
v___x_524_ = v___x_514_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v___x_522_);
lean_ctor_set(v_reuseFailAlloc_525_, 1, v_extensions_512_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0___redArg(lean_object* v_a_530_, lean_object* v_x_531_){
_start:
{
if (lean_obj_tag(v_x_531_) == 0)
{
uint8_t v___x_532_; 
v___x_532_ = 0;
return v___x_532_;
}
else
{
lean_object* v_key_533_; lean_object* v_tail_534_; uint8_t v___x_535_; 
v_key_533_ = lean_ctor_get(v_x_531_, 0);
v_tail_534_ = lean_ctor_get(v_x_531_, 2);
v___x_535_ = lean_string_dec_eq(v_key_533_, v_a_530_);
if (v___x_535_ == 0)
{
v_x_531_ = v_tail_534_;
goto _start;
}
else
{
return v___x_535_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0___redArg___boxed(lean_object* v_a_537_, lean_object* v_x_538_){
_start:
{
uint8_t v_res_539_; lean_object* v_r_540_; 
v_res_539_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0___redArg(v_a_537_, v_x_538_);
lean_dec(v_x_538_);
lean_dec_ref(v_a_537_);
v_r_540_ = lean_box(v_res_539_);
return v_r_540_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_541_, lean_object* v_x_542_){
_start:
{
if (lean_obj_tag(v_x_542_) == 0)
{
return v_x_541_;
}
else
{
lean_object* v_key_543_; lean_object* v_value_544_; lean_object* v_tail_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_568_; 
v_key_543_ = lean_ctor_get(v_x_542_, 0);
v_value_544_ = lean_ctor_get(v_x_542_, 1);
v_tail_545_ = lean_ctor_get(v_x_542_, 2);
v_isSharedCheck_568_ = !lean_is_exclusive(v_x_542_);
if (v_isSharedCheck_568_ == 0)
{
v___x_547_ = v_x_542_;
v_isShared_548_ = v_isSharedCheck_568_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_tail_545_);
lean_inc(v_value_544_);
lean_inc(v_key_543_);
lean_dec(v_x_542_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_568_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_549_; uint64_t v___x_550_; uint64_t v___x_551_; uint64_t v___x_552_; uint64_t v_fold_553_; uint64_t v___x_554_; uint64_t v___x_555_; uint64_t v___x_556_; size_t v___x_557_; size_t v___x_558_; size_t v___x_559_; size_t v___x_560_; size_t v___x_561_; lean_object* v___x_562_; lean_object* v___x_564_; 
v___x_549_ = lean_array_get_size(v_x_541_);
v___x_550_ = lean_string_hash(v_key_543_);
v___x_551_ = 32ULL;
v___x_552_ = lean_uint64_shift_right(v___x_550_, v___x_551_);
v_fold_553_ = lean_uint64_xor(v___x_550_, v___x_552_);
v___x_554_ = 16ULL;
v___x_555_ = lean_uint64_shift_right(v_fold_553_, v___x_554_);
v___x_556_ = lean_uint64_xor(v_fold_553_, v___x_555_);
v___x_557_ = lean_uint64_to_usize(v___x_556_);
v___x_558_ = lean_usize_of_nat(v___x_549_);
v___x_559_ = ((size_t)1ULL);
v___x_560_ = lean_usize_sub(v___x_558_, v___x_559_);
v___x_561_ = lean_usize_land(v___x_557_, v___x_560_);
v___x_562_ = lean_array_uget_borrowed(v_x_541_, v___x_561_);
lean_inc(v___x_562_);
if (v_isShared_548_ == 0)
{
lean_ctor_set(v___x_547_, 2, v___x_562_);
v___x_564_ = v___x_547_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_key_543_);
lean_ctor_set(v_reuseFailAlloc_567_, 1, v_value_544_);
lean_ctor_set(v_reuseFailAlloc_567_, 2, v___x_562_);
v___x_564_ = v_reuseFailAlloc_567_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
lean_object* v___x_565_; 
v___x_565_ = lean_array_uset(v_x_541_, v___x_561_, v___x_564_);
v_x_541_ = v___x_565_;
v_x_542_ = v_tail_545_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2___redArg(lean_object* v_i_569_, lean_object* v_source_570_, lean_object* v_target_571_){
_start:
{
lean_object* v___x_572_; uint8_t v___x_573_; 
v___x_572_ = lean_array_get_size(v_source_570_);
v___x_573_ = lean_nat_dec_lt(v_i_569_, v___x_572_);
if (v___x_573_ == 0)
{
lean_dec_ref(v_source_570_);
lean_dec(v_i_569_);
return v_target_571_;
}
else
{
lean_object* v_es_574_; lean_object* v___x_575_; lean_object* v_source_576_; lean_object* v_target_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v_es_574_ = lean_array_fget(v_source_570_, v_i_569_);
v___x_575_ = lean_box(0);
v_source_576_ = lean_array_fset(v_source_570_, v_i_569_, v___x_575_);
v_target_577_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2_spec__3___redArg(v_target_571_, v_es_574_);
v___x_578_ = lean_unsigned_to_nat(1u);
v___x_579_ = lean_nat_add(v_i_569_, v___x_578_);
lean_dec(v_i_569_);
v_i_569_ = v___x_579_;
v_source_570_ = v_source_576_;
v_target_571_ = v_target_577_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1___redArg(lean_object* v_data_581_){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v_nbuckets_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_582_ = lean_array_get_size(v_data_581_);
v___x_583_ = lean_unsigned_to_nat(2u);
v_nbuckets_584_ = lean_nat_mul(v___x_582_, v___x_583_);
v___x_585_ = lean_unsigned_to_nat(0u);
v___x_586_ = lean_box(0);
v___x_587_ = lean_mk_array(v_nbuckets_584_, v___x_586_);
v___x_588_ = lean_array_propagate_mark(v_data_581_, v___x_587_);
v___x_589_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2___redArg(v___x_585_, v_data_581_, v___x_588_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__2___lam__0(lean_object* v_i_590_, lean_object* v_x_591_){
_start:
{
if (lean_obj_tag(v_x_591_) == 0)
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_592_ = lean_unsigned_to_nat(1u);
v___x_593_ = lean_mk_empty_array_with_capacity(v___x_592_);
v___x_594_ = lean_array_push(v___x_593_, v_i_590_);
v___x_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_595_, 0, v___x_594_);
return v___x_595_;
}
else
{
lean_object* v_val_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_604_; 
v_val_596_ = lean_ctor_get(v_x_591_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v_x_591_);
if (v_isSharedCheck_604_ == 0)
{
v___x_598_ = v_x_591_;
v_isShared_599_ = v_isSharedCheck_604_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_val_596_);
lean_dec(v_x_591_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_604_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_600_; lean_object* v___x_602_; 
v___x_600_ = lean_array_push(v_val_596_, v_i_590_);
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 0, v___x_600_);
v___x_602_ = v___x_598_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v___x_600_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__2(lean_object* v_i_605_, lean_object* v_a_606_, lean_object* v_x_607_){
_start:
{
if (lean_obj_tag(v_x_607_) == 0)
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v_val_610_; lean_object* v___x_611_; 
v___x_608_ = lean_box(0);
v___x_609_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__2___lam__0(v_i_605_, v___x_608_);
v_val_610_ = lean_ctor_get(v___x_609_, 0);
lean_inc(v_val_610_);
lean_dec(v___x_609_);
v___x_611_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_611_, 0, v_a_606_);
lean_ctor_set(v___x_611_, 1, v_val_610_);
lean_ctor_set(v___x_611_, 2, v_x_607_);
return v___x_611_;
}
else
{
lean_object* v_key_612_; lean_object* v_value_613_; lean_object* v_tail_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_629_; 
v_key_612_ = lean_ctor_get(v_x_607_, 0);
v_value_613_ = lean_ctor_get(v_x_607_, 1);
v_tail_614_ = lean_ctor_get(v_x_607_, 2);
v_isSharedCheck_629_ = !lean_is_exclusive(v_x_607_);
if (v_isSharedCheck_629_ == 0)
{
v___x_616_ = v_x_607_;
v_isShared_617_ = v_isSharedCheck_629_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_tail_614_);
lean_inc(v_value_613_);
lean_inc(v_key_612_);
lean_dec(v_x_607_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_629_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
uint8_t v___x_618_; 
v___x_618_ = lean_string_dec_eq(v_key_612_, v_a_606_);
if (v___x_618_ == 0)
{
lean_object* v_tail_619_; lean_object* v___x_621_; 
v_tail_619_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__2(v_i_605_, v_a_606_, v_tail_614_);
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 2, v_tail_619_);
v___x_621_ = v___x_616_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_key_612_);
lean_ctor_set(v_reuseFailAlloc_622_, 1, v_value_613_);
lean_ctor_set(v_reuseFailAlloc_622_, 2, v_tail_619_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
else
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v_val_625_; lean_object* v___x_627_; 
lean_dec(v_key_612_);
v___x_623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_623_, 0, v_value_613_);
v___x_624_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__2___lam__0(v_i_605_, v___x_623_);
v_val_625_ = lean_ctor_get(v___x_624_, 0);
lean_inc(v_val_625_);
lean_dec(v___x_624_);
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 1, v_val_625_);
lean_ctor_set(v___x_616_, 0, v_a_606_);
v___x_627_ = v___x_616_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_a_606_);
lean_ctor_set(v_reuseFailAlloc_628_, 1, v_val_625_);
lean_ctor_set(v_reuseFailAlloc_628_, 2, v_tail_614_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0(lean_object* v_i_630_, lean_object* v_m_631_, lean_object* v_a_632_){
_start:
{
lean_object* v_size_633_; lean_object* v_buckets_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_684_; 
v_size_633_ = lean_ctor_get(v_m_631_, 0);
v_buckets_634_ = lean_ctor_get(v_m_631_, 1);
v_isSharedCheck_684_ = !lean_is_exclusive(v_m_631_);
if (v_isSharedCheck_684_ == 0)
{
v___x_636_ = v_m_631_;
v_isShared_637_ = v_isSharedCheck_684_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_buckets_634_);
lean_inc(v_size_633_);
lean_dec(v_m_631_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_684_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_638_; uint64_t v___x_639_; uint64_t v___x_640_; uint64_t v___x_641_; uint64_t v_fold_642_; uint64_t v___x_643_; uint64_t v___x_644_; uint64_t v___x_645_; size_t v___x_646_; size_t v___x_647_; size_t v___x_648_; size_t v___x_649_; size_t v___x_650_; lean_object* v_bkt_651_; uint8_t v___x_652_; 
v___x_638_ = lean_array_get_size(v_buckets_634_);
v___x_639_ = lean_string_hash(v_a_632_);
v___x_640_ = 32ULL;
v___x_641_ = lean_uint64_shift_right(v___x_639_, v___x_640_);
v_fold_642_ = lean_uint64_xor(v___x_639_, v___x_641_);
v___x_643_ = 16ULL;
v___x_644_ = lean_uint64_shift_right(v_fold_642_, v___x_643_);
v___x_645_ = lean_uint64_xor(v_fold_642_, v___x_644_);
v___x_646_ = lean_uint64_to_usize(v___x_645_);
v___x_647_ = lean_usize_of_nat(v___x_638_);
v___x_648_ = ((size_t)1ULL);
v___x_649_ = lean_usize_sub(v___x_647_, v___x_648_);
v___x_650_ = lean_usize_land(v___x_646_, v___x_649_);
v_bkt_651_ = lean_array_uget_borrowed(v_buckets_634_, v___x_650_);
v___x_652_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0___redArg(v_a_632_, v_bkt_651_);
if (v___x_652_ == 0)
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v_size_x27_656_; lean_object* v___x_657_; lean_object* v_buckets_x27_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; uint8_t v___x_664_; 
v___x_653_ = lean_unsigned_to_nat(1u);
v___x_654_ = lean_mk_empty_array_with_capacity(v___x_653_);
v___x_655_ = lean_array_push(v___x_654_, v_i_630_);
v_size_x27_656_ = lean_nat_add(v_size_633_, v___x_653_);
lean_dec(v_size_633_);
lean_inc(v_bkt_651_);
v___x_657_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_657_, 0, v_a_632_);
lean_ctor_set(v___x_657_, 1, v___x_655_);
lean_ctor_set(v___x_657_, 2, v_bkt_651_);
v_buckets_x27_658_ = lean_array_uset(v_buckets_634_, v___x_650_, v___x_657_);
v___x_659_ = lean_unsigned_to_nat(4u);
v___x_660_ = lean_nat_mul(v_size_x27_656_, v___x_659_);
v___x_661_ = lean_unsigned_to_nat(3u);
v___x_662_ = lean_nat_div(v___x_660_, v___x_661_);
lean_dec(v___x_660_);
v___x_663_ = lean_array_get_size(v_buckets_x27_658_);
v___x_664_ = lean_nat_dec_le(v___x_662_, v___x_663_);
lean_dec(v___x_662_);
if (v___x_664_ == 0)
{
lean_object* v_val_665_; lean_object* v___x_667_; 
v_val_665_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1___redArg(v_buckets_x27_658_);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 1, v_val_665_);
lean_ctor_set(v___x_636_, 0, v_size_x27_656_);
v___x_667_ = v___x_636_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_size_x27_656_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v_val_665_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
else
{
lean_object* v___x_670_; 
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 1, v_buckets_x27_658_);
lean_ctor_set(v___x_636_, 0, v_size_x27_656_);
v___x_670_ = v___x_636_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_size_x27_656_);
lean_ctor_set(v_reuseFailAlloc_671_, 1, v_buckets_x27_658_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
else
{
lean_object* v___x_672_; lean_object* v_buckets_x27_673_; lean_object* v_bkt_x27_674_; lean_object* v___y_676_; uint8_t v___x_681_; 
lean_inc(v_bkt_651_);
v___x_672_ = lean_box(0);
v_buckets_x27_673_ = lean_array_uset(v_buckets_634_, v___x_650_, v___x_672_);
lean_inc_ref(v_a_632_);
v_bkt_x27_674_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__2(v_i_630_, v_a_632_, v_bkt_651_);
v___x_681_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0___redArg(v_a_632_, v_bkt_x27_674_);
lean_dec_ref(v_a_632_);
if (v___x_681_ == 0)
{
lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_682_ = lean_unsigned_to_nat(1u);
v___x_683_ = lean_nat_sub(v_size_633_, v___x_682_);
lean_dec(v_size_633_);
v___y_676_ = v___x_683_;
goto v___jp_675_;
}
else
{
v___y_676_ = v_size_633_;
goto v___jp_675_;
}
v___jp_675_:
{
lean_object* v___x_677_; lean_object* v___x_679_; 
v___x_677_ = lean_array_uset(v_buckets_x27_673_, v___x_650_, v_bkt_x27_674_);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 1, v___x_677_);
lean_ctor_set(v___x_636_, 0, v___y_676_);
v___x_679_ = v___x_636_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v___y_676_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v___x_677_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_header(lean_object* v_builder_685_, lean_object* v_key_686_, lean_object* v_value_687_){
_start:
{
lean_object* v_line_688_; lean_object* v_headers_689_; lean_object* v_extensions_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_720_; 
v_line_688_ = lean_ctor_get(v_builder_685_, 0);
lean_inc_ref(v_line_688_);
v_headers_689_ = lean_ctor_get(v_line_688_, 1);
lean_inc_ref(v_headers_689_);
v_extensions_690_ = lean_ctor_get(v_builder_685_, 1);
v_isSharedCheck_720_ = !lean_is_exclusive(v_builder_685_);
if (v_isSharedCheck_720_ == 0)
{
lean_object* v_unused_721_; 
v_unused_721_ = lean_ctor_get(v_builder_685_, 0);
lean_dec(v_unused_721_);
v___x_692_ = v_builder_685_;
v_isShared_693_ = v_isSharedCheck_720_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_extensions_690_);
lean_dec(v_builder_685_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_720_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v_status_694_; uint8_t v_version_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_718_; 
v_status_694_ = lean_ctor_get(v_line_688_, 0);
v_version_695_ = lean_ctor_get_uint8(v_line_688_, sizeof(void*)*2);
v_isSharedCheck_718_ = !lean_is_exclusive(v_line_688_);
if (v_isSharedCheck_718_ == 0)
{
lean_object* v_unused_719_; 
v_unused_719_ = lean_ctor_get(v_line_688_, 1);
lean_dec(v_unused_719_);
v___x_697_ = v_line_688_;
v_isShared_698_ = v_isSharedCheck_718_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_status_694_);
lean_dec(v_line_688_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_718_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v_entries_699_; lean_object* v_indexes_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_717_; 
v_entries_699_ = lean_ctor_get(v_headers_689_, 0);
v_indexes_700_ = lean_ctor_get(v_headers_689_, 1);
v_isSharedCheck_717_ = !lean_is_exclusive(v_headers_689_);
if (v_isSharedCheck_717_ == 0)
{
v___x_702_ = v_headers_689_;
v_isShared_703_ = v_isSharedCheck_717_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_indexes_700_);
lean_inc(v_entries_699_);
lean_dec(v_headers_689_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_717_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v_i_704_; lean_object* v___x_705_; lean_object* v_entries_706_; lean_object* v_indexes_707_; lean_object* v___x_709_; 
v_i_704_ = lean_array_get_size(v_entries_699_);
lean_inc_ref(v_key_686_);
v___x_705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_705_, 0, v_key_686_);
lean_ctor_set(v___x_705_, 1, v_value_687_);
v_entries_706_ = lean_array_push(v_entries_699_, v___x_705_);
v_indexes_707_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0(v_i_704_, v_indexes_700_, v_key_686_);
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 1, v_indexes_707_);
lean_ctor_set(v___x_702_, 0, v_entries_706_);
v___x_709_ = v___x_702_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_entries_706_);
lean_ctor_set(v_reuseFailAlloc_716_, 1, v_indexes_707_);
v___x_709_ = v_reuseFailAlloc_716_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
lean_object* v___x_711_; 
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 1, v___x_709_);
v___x_711_ = v___x_697_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_status_694_);
lean_ctor_set(v_reuseFailAlloc_715_, 1, v___x_709_);
lean_ctor_set_uint8(v_reuseFailAlloc_715_, sizeof(void*)*2, v_version_695_);
v___x_711_ = v_reuseFailAlloc_715_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
lean_object* v___x_713_; 
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 0, v___x_711_);
v___x_713_ = v___x_692_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v___x_711_);
lean_ctor_set(v_reuseFailAlloc_714_, 1, v_extensions_690_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0(lean_object* v_00_u03b2_722_, lean_object* v_a_723_, lean_object* v_x_724_){
_start:
{
uint8_t v___x_725_; 
v___x_725_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0___redArg(v_a_723_, v_x_724_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0___boxed(lean_object* v_00_u03b2_726_, lean_object* v_a_727_, lean_object* v_x_728_){
_start:
{
uint8_t v_res_729_; lean_object* v_r_730_; 
v_res_729_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0(v_00_u03b2_726_, v_a_727_, v_x_728_);
lean_dec(v_x_728_);
lean_dec_ref(v_a_727_);
v_r_730_ = lean_box(v_res_729_);
return v_r_730_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1(lean_object* v_00_u03b2_731_, lean_object* v_data_732_){
_start:
{
lean_object* v___x_733_; 
v___x_733_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1___redArg(v_data_732_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_734_, lean_object* v_i_735_, lean_object* v_source_736_, lean_object* v_target_737_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2___redArg(v_i_735_, v_source_736_, v_target_737_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_739_, lean_object* v_x_740_, lean_object* v_x_741_){
_start:
{
lean_object* v___x_742_; 
v___x_742_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2_spec__3___redArg(v_x_740_, v_x_741_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_header_x21(lean_object* v_builder_743_, lean_object* v_key_744_, lean_object* v_value_745_){
_start:
{
lean_object* v_line_746_; lean_object* v_headers_747_; lean_object* v_extensions_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_780_; 
v_line_746_ = lean_ctor_get(v_builder_743_, 0);
lean_inc_ref(v_line_746_);
v_headers_747_ = lean_ctor_get(v_line_746_, 1);
lean_inc_ref(v_headers_747_);
v_extensions_748_ = lean_ctor_get(v_builder_743_, 1);
v_isSharedCheck_780_ = !lean_is_exclusive(v_builder_743_);
if (v_isSharedCheck_780_ == 0)
{
lean_object* v_unused_781_; 
v_unused_781_ = lean_ctor_get(v_builder_743_, 0);
lean_dec(v_unused_781_);
v___x_750_ = v_builder_743_;
v_isShared_751_ = v_isSharedCheck_780_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_extensions_748_);
lean_dec(v_builder_743_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_780_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v_status_752_; uint8_t v_version_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_778_; 
v_status_752_ = lean_ctor_get(v_line_746_, 0);
v_version_753_ = lean_ctor_get_uint8(v_line_746_, sizeof(void*)*2);
v_isSharedCheck_778_ = !lean_is_exclusive(v_line_746_);
if (v_isSharedCheck_778_ == 0)
{
lean_object* v_unused_779_; 
v_unused_779_ = lean_ctor_get(v_line_746_, 1);
lean_dec(v_unused_779_);
v___x_755_ = v_line_746_;
v_isShared_756_ = v_isSharedCheck_778_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_status_752_);
lean_dec(v_line_746_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_778_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v_entries_757_; lean_object* v_indexes_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_777_; 
v_entries_757_ = lean_ctor_get(v_headers_747_, 0);
v_indexes_758_ = lean_ctor_get(v_headers_747_, 1);
v_isSharedCheck_777_ = !lean_is_exclusive(v_headers_747_);
if (v_isSharedCheck_777_ == 0)
{
v___x_760_ = v_headers_747_;
v_isShared_761_ = v_isSharedCheck_777_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_indexes_758_);
lean_inc(v_entries_757_);
lean_dec(v_headers_747_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_777_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v_key_762_; lean_object* v_value_763_; lean_object* v_i_764_; lean_object* v___x_765_; lean_object* v_entries_766_; lean_object* v_indexes_767_; lean_object* v___x_769_; 
v_key_762_ = l_Std_Http_Header_Name_ofString_x21(v_key_744_);
v_value_763_ = l_Std_Http_Header_Value_ofString_x21(v_value_745_);
v_i_764_ = lean_array_get_size(v_entries_757_);
lean_inc_ref(v_key_762_);
v___x_765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_765_, 0, v_key_762_);
lean_ctor_set(v___x_765_, 1, v_value_763_);
v_entries_766_ = lean_array_push(v_entries_757_, v___x_765_);
v_indexes_767_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0(v_i_764_, v_indexes_758_, v_key_762_);
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 1, v_indexes_767_);
lean_ctor_set(v___x_760_, 0, v_entries_766_);
v___x_769_ = v___x_760_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_entries_766_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v_indexes_767_);
v___x_769_ = v_reuseFailAlloc_776_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
lean_object* v___x_771_; 
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 1, v___x_769_);
v___x_771_ = v___x_755_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_status_752_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v___x_769_);
lean_ctor_set_uint8(v_reuseFailAlloc_775_, sizeof(void*)*2, v_version_753_);
v___x_771_ = v_reuseFailAlloc_775_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
lean_object* v___x_773_; 
if (v_isShared_751_ == 0)
{
lean_ctor_set(v___x_750_, 0, v___x_771_);
v___x_773_ = v___x_750_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v___x_771_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v_extensions_748_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_header_x3f(lean_object* v_builder_782_, lean_object* v_key_783_, lean_object* v_value_784_){
_start:
{
lean_object* v___x_785_; 
v___x_785_ = l_Std_Http_Header_Name_ofString_x3f(v_key_783_);
if (lean_obj_tag(v___x_785_) == 0)
{
lean_object* v___x_786_; 
lean_dec_ref(v_value_784_);
lean_dec_ref(v_builder_782_);
v___x_786_ = lean_box(0);
return v___x_786_;
}
else
{
lean_object* v_val_787_; lean_object* v___x_788_; 
v_val_787_ = lean_ctor_get(v___x_785_, 0);
lean_inc(v_val_787_);
lean_dec_ref_known(v___x_785_, 1);
v___x_788_ = l_Std_Http_Header_Value_ofString_x3f(v_value_784_);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v___x_789_; 
lean_dec(v_val_787_);
lean_dec_ref(v_builder_782_);
v___x_789_ = lean_box(0);
return v___x_789_;
}
else
{
lean_object* v_line_790_; lean_object* v_headers_791_; lean_object* v_val_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_831_; 
v_line_790_ = lean_ctor_get(v_builder_782_, 0);
lean_inc_ref(v_line_790_);
v_headers_791_ = lean_ctor_get(v_line_790_, 1);
lean_inc_ref(v_headers_791_);
v_val_792_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_831_ == 0)
{
v___x_794_ = v___x_788_;
v_isShared_795_ = v_isSharedCheck_831_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_val_792_);
lean_dec(v___x_788_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_831_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v_extensions_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_829_; 
v_extensions_796_ = lean_ctor_get(v_builder_782_, 1);
v_isSharedCheck_829_ = !lean_is_exclusive(v_builder_782_);
if (v_isSharedCheck_829_ == 0)
{
lean_object* v_unused_830_; 
v_unused_830_ = lean_ctor_get(v_builder_782_, 0);
lean_dec(v_unused_830_);
v___x_798_ = v_builder_782_;
v_isShared_799_ = v_isSharedCheck_829_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_extensions_796_);
lean_dec(v_builder_782_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_829_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v_status_800_; uint8_t v_version_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_827_; 
v_status_800_ = lean_ctor_get(v_line_790_, 0);
v_version_801_ = lean_ctor_get_uint8(v_line_790_, sizeof(void*)*2);
v_isSharedCheck_827_ = !lean_is_exclusive(v_line_790_);
if (v_isSharedCheck_827_ == 0)
{
lean_object* v_unused_828_; 
v_unused_828_ = lean_ctor_get(v_line_790_, 1);
lean_dec(v_unused_828_);
v___x_803_ = v_line_790_;
v_isShared_804_ = v_isSharedCheck_827_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_status_800_);
lean_dec(v_line_790_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_827_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v_entries_805_; lean_object* v_indexes_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_826_; 
v_entries_805_ = lean_ctor_get(v_headers_791_, 0);
v_indexes_806_ = lean_ctor_get(v_headers_791_, 1);
v_isSharedCheck_826_ = !lean_is_exclusive(v_headers_791_);
if (v_isSharedCheck_826_ == 0)
{
v___x_808_ = v_headers_791_;
v_isShared_809_ = v_isSharedCheck_826_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_indexes_806_);
lean_inc(v_entries_805_);
lean_dec(v_headers_791_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_826_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v_i_810_; lean_object* v___x_811_; lean_object* v_entries_812_; lean_object* v_indexes_813_; lean_object* v___x_815_; 
v_i_810_ = lean_array_get_size(v_entries_805_);
lean_inc(v_val_787_);
v___x_811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_811_, 0, v_val_787_);
lean_ctor_set(v___x_811_, 1, v_val_792_);
v_entries_812_ = lean_array_push(v_entries_805_, v___x_811_);
v_indexes_813_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0(v_i_810_, v_indexes_806_, v_val_787_);
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 1, v_indexes_813_);
lean_ctor_set(v___x_808_, 0, v_entries_812_);
v___x_815_ = v___x_808_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_entries_812_);
lean_ctor_set(v_reuseFailAlloc_825_, 1, v_indexes_813_);
v___x_815_ = v_reuseFailAlloc_825_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
lean_object* v___x_817_; 
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 1, v___x_815_);
v___x_817_ = v___x_803_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_status_800_);
lean_ctor_set(v_reuseFailAlloc_824_, 1, v___x_815_);
lean_ctor_set_uint8(v_reuseFailAlloc_824_, sizeof(void*)*2, v_version_801_);
v___x_817_ = v_reuseFailAlloc_824_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
lean_object* v___x_819_; 
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 0, v___x_817_);
v___x_819_ = v___x_798_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_817_);
lean_ctor_set(v_reuseFailAlloc_823_, 1, v_extensions_796_);
v___x_819_ = v_reuseFailAlloc_823_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
lean_object* v___x_821_; 
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 0, v___x_819_);
v___x_821_ = v___x_794_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_819_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
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
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_extension___redArg(lean_object* v_builder_833_, lean_object* v_inst_834_, lean_object* v_data_835_){
_start:
{
lean_object* v_line_836_; lean_object* v_extensions_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_848_; 
v_line_836_ = lean_ctor_get(v_builder_833_, 0);
v_extensions_837_ = lean_ctor_get(v_builder_833_, 1);
v_isSharedCheck_848_ = !lean_is_exclusive(v_builder_833_);
if (v_isSharedCheck_848_ == 0)
{
v___x_839_ = v_builder_833_;
v_isShared_840_ = v_isSharedCheck_848_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_extensions_837_);
lean_inc(v_line_836_);
lean_dec(v_builder_833_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_848_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v_dyn_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_846_; 
v_dyn_841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_dyn_841_, 0, v_inst_834_);
lean_ctor_set(v_dyn_841_, 1, v_data_835_);
v___x_842_ = ((lean_object*)(l_Std_Http_Response_Builder_extension___redArg___closed__0));
v___x_843_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_dyn_841_);
v___x_844_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_842_, v___x_843_, v_dyn_841_, v_extensions_837_);
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 1, v___x_844_);
v___x_846_ = v___x_839_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_line_836_);
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
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_extension(lean_object* v_00_u03b1_849_, lean_object* v_builder_850_, lean_object* v_inst_851_, lean_object* v_data_852_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = l_Std_Http_Response_Builder_extension___redArg(v_builder_850_, v_inst_851_, v_data_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_body___redArg(lean_object* v_builder_854_, lean_object* v_body_855_){
_start:
{
lean_object* v_line_856_; lean_object* v_extensions_857_; lean_object* v___x_858_; 
v_line_856_ = lean_ctor_get(v_builder_854_, 0);
v_extensions_857_ = lean_ctor_get(v_builder_854_, 1);
lean_inc(v_extensions_857_);
lean_inc_ref(v_line_856_);
v___x_858_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_858_, 0, v_line_856_);
lean_ctor_set(v___x_858_, 1, v_body_855_);
lean_ctor_set(v___x_858_, 2, v_extensions_857_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_body___redArg___boxed(lean_object* v_builder_859_, lean_object* v_body_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_Std_Http_Response_Builder_body___redArg(v_builder_859_, v_body_860_);
lean_dec_ref(v_builder_859_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_body(lean_object* v_t_862_, lean_object* v_builder_863_, lean_object* v_body_864_){
_start:
{
lean_object* v___x_865_; 
v___x_865_ = l_Std_Http_Response_Builder_body___redArg(v_builder_863_, v_body_864_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_body___boxed(lean_object* v_t_866_, lean_object* v_builder_867_, lean_object* v_body_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_Std_Http_Response_Builder_body(v_t_866_, v_builder_867_, v_body_868_);
lean_dec_ref(v_builder_867_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_build___redArg(lean_object* v_inst_870_, lean_object* v_builder_871_){
_start:
{
lean_object* v_line_872_; lean_object* v_extensions_873_; lean_object* v___x_874_; 
v_line_872_ = lean_ctor_get(v_builder_871_, 0);
v_extensions_873_ = lean_ctor_get(v_builder_871_, 1);
lean_inc(v_extensions_873_);
lean_inc_ref(v_line_872_);
v___x_874_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_874_, 0, v_line_872_);
lean_ctor_set(v___x_874_, 1, v_inst_870_);
lean_ctor_set(v___x_874_, 2, v_extensions_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_build___redArg___boxed(lean_object* v_inst_875_, lean_object* v_builder_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l_Std_Http_Response_Builder_build___redArg(v_inst_875_, v_builder_876_);
lean_dec_ref(v_builder_876_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_build(lean_object* v_t_878_, lean_object* v_inst_879_, lean_object* v_builder_880_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l_Std_Http_Response_Builder_build___redArg(v_inst_879_, v_builder_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_build___boxed(lean_object* v_t_882_, lean_object* v_inst_883_, lean_object* v_builder_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l_Std_Http_Response_Builder_build(v_t_882_, v_inst_883_, v_builder_884_);
lean_dec_ref(v_builder_884_);
return v_res_885_;
}
}
static lean_object* _init_l_Std_Http_Response_ok___closed__0(void){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_886_ = lean_box(4);
v___x_887_ = l_Std_Http_Response_Builder_new;
v___x_888_ = l_Std_Http_Response_Builder_status(v___x_887_, v___x_886_);
return v___x_888_;
}
}
static lean_object* _init_l_Std_Http_Response_ok(void){
_start:
{
lean_object* v___x_889_; 
v___x_889_ = lean_obj_once(&l_Std_Http_Response_ok___closed__0, &l_Std_Http_Response_ok___closed__0_once, _init_l_Std_Http_Response_ok___closed__0);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_withStatus(lean_object* v_status_890_){
_start:
{
lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_891_ = l_Std_Http_Response_Builder_new;
v___x_892_ = l_Std_Http_Response_Builder_status(v___x_891_, v_status_890_);
return v___x_892_;
}
}
static lean_object* _init_l_Std_Http_Response_notFound___closed__0(void){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_893_ = lean_box(27);
v___x_894_ = l_Std_Http_Response_Builder_new;
v___x_895_ = l_Std_Http_Response_Builder_status(v___x_894_, v___x_893_);
return v___x_895_;
}
}
static lean_object* _init_l_Std_Http_Response_notFound(void){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = lean_obj_once(&l_Std_Http_Response_notFound___closed__0, &l_Std_Http_Response_notFound___closed__0_once, _init_l_Std_Http_Response_notFound___closed__0);
return v___x_896_;
}
}
static lean_object* _init_l_Std_Http_Response_internalServerError___closed__0(void){
_start:
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_897_ = lean_box(52);
v___x_898_ = l_Std_Http_Response_Builder_new;
v___x_899_ = l_Std_Http_Response_Builder_status(v___x_898_, v___x_897_);
return v___x_899_;
}
}
static lean_object* _init_l_Std_Http_Response_internalServerError(void){
_start:
{
lean_object* v___x_900_; 
v___x_900_ = lean_obj_once(&l_Std_Http_Response_internalServerError___closed__0, &l_Std_Http_Response_internalServerError___closed__0_once, _init_l_Std_Http_Response_internalServerError___closed__0);
return v___x_900_;
}
}
static lean_object* _init_l_Std_Http_Response_badRequest___closed__0(void){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_901_ = lean_box(23);
v___x_902_ = l_Std_Http_Response_Builder_new;
v___x_903_ = l_Std_Http_Response_Builder_status(v___x_902_, v___x_901_);
return v___x_903_;
}
}
static lean_object* _init_l_Std_Http_Response_badRequest(void){
_start:
{
lean_object* v___x_904_; 
v___x_904_ = lean_obj_once(&l_Std_Http_Response_badRequest___closed__0, &l_Std_Http_Response_badRequest___closed__0_once, _init_l_Std_Http_Response_badRequest___closed__0);
return v___x_904_;
}
}
static lean_object* _init_l_Std_Http_Response_created___closed__0(void){
_start:
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_905_ = lean_box(5);
v___x_906_ = l_Std_Http_Response_Builder_new;
v___x_907_ = l_Std_Http_Response_Builder_status(v___x_906_, v___x_905_);
return v___x_907_;
}
}
static lean_object* _init_l_Std_Http_Response_created(void){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = lean_obj_once(&l_Std_Http_Response_created___closed__0, &l_Std_Http_Response_created___closed__0_once, _init_l_Std_Http_Response_created___closed__0);
return v___x_908_;
}
}
static lean_object* _init_l_Std_Http_Response_accepted___closed__0(void){
_start:
{
lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_909_ = lean_box(6);
v___x_910_ = l_Std_Http_Response_Builder_new;
v___x_911_ = l_Std_Http_Response_Builder_status(v___x_910_, v___x_909_);
return v___x_911_;
}
}
static lean_object* _init_l_Std_Http_Response_accepted(void){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = lean_obj_once(&l_Std_Http_Response_accepted___closed__0, &l_Std_Http_Response_accepted___closed__0_once, _init_l_Std_Http_Response_accepted___closed__0);
return v___x_912_;
}
}
static lean_object* _init_l_Std_Http_Response_unauthorized___closed__0(void){
_start:
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_913_ = lean_box(24);
v___x_914_ = l_Std_Http_Response_Builder_new;
v___x_915_ = l_Std_Http_Response_Builder_status(v___x_914_, v___x_913_);
return v___x_915_;
}
}
static lean_object* _init_l_Std_Http_Response_unauthorized(void){
_start:
{
lean_object* v___x_916_; 
v___x_916_ = lean_obj_once(&l_Std_Http_Response_unauthorized___closed__0, &l_Std_Http_Response_unauthorized___closed__0_once, _init_l_Std_Http_Response_unauthorized___closed__0);
return v___x_916_;
}
}
static lean_object* _init_l_Std_Http_Response_forbidden___closed__0(void){
_start:
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_917_ = lean_box(26);
v___x_918_ = l_Std_Http_Response_Builder_new;
v___x_919_ = l_Std_Http_Response_Builder_status(v___x_918_, v___x_917_);
return v___x_919_;
}
}
static lean_object* _init_l_Std_Http_Response_forbidden(void){
_start:
{
lean_object* v___x_920_; 
v___x_920_ = lean_obj_once(&l_Std_Http_Response_forbidden___closed__0, &l_Std_Http_Response_forbidden___closed__0_once, _init_l_Std_Http_Response_forbidden___closed__0);
return v___x_920_;
}
}
static lean_object* _init_l_Std_Http_Response_conflict___closed__0(void){
_start:
{
lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_921_ = lean_box(32);
v___x_922_ = l_Std_Http_Response_Builder_new;
v___x_923_ = l_Std_Http_Response_Builder_status(v___x_922_, v___x_921_);
return v___x_923_;
}
}
static lean_object* _init_l_Std_Http_Response_conflict(void){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = lean_obj_once(&l_Std_Http_Response_conflict___closed__0, &l_Std_Http_Response_conflict___closed__0_once, _init_l_Std_Http_Response_conflict___closed__0);
return v___x_924_;
}
}
static lean_object* _init_l_Std_Http_Response_serviceUnavailable___closed__0(void){
_start:
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_925_ = lean_box(55);
v___x_926_ = l_Std_Http_Response_Builder_new;
v___x_927_ = l_Std_Http_Response_Builder_status(v___x_926_, v___x_925_);
return v___x_927_;
}
}
static lean_object* _init_l_Std_Http_Response_serviceUnavailable(void){
_start:
{
lean_object* v___x_928_; 
v___x_928_ = lean_obj_once(&l_Std_Http_Response_serviceUnavailable___closed__0, &l_Std_Http_Response_serviceUnavailable___closed__0_once, _init_l_Std_Http_Response_serviceUnavailable___closed__0);
return v___x_928_;
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
