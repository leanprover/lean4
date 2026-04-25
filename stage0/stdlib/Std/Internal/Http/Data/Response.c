// Lean compiler output
// Module: Std.Internal.Http.Data.Response
// Imports: public import Std.Internal.Http.Data.Extensions public import Std.Internal.Http.Data.Status public import Std.Internal.Http.Data.Version public import Std.Internal.Http.Data.Headers
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
lean_object* l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___lam__0___boxed(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_splitToSubslice___redArg(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
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
v___x_125_ = lean_string_utf8_extract(v___x_105_, v___x_106_, v___x_107_);
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
v___x_137_ = lean_string_utf8_extract(v_fst_108_, v_startInclusive_135_, v_endExclusive_136_);
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
lean_dec_ref(v___x_211_);
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
v___x_294_ = lean_string_utf8_extract(v___x_274_, v___x_275_, v___x_276_);
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
v___x_306_ = lean_string_utf8_extract(v_name_277_, v_startInclusive_304_, v_endExclusive_305_);
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
lean_dec_ref(v___x_387_);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0___redArg(lean_object* v_a_522_, lean_object* v_x_523_){
_start:
{
if (lean_obj_tag(v_x_523_) == 0)
{
uint8_t v___x_524_; 
v___x_524_ = 0;
return v___x_524_;
}
else
{
lean_object* v_key_525_; lean_object* v_tail_526_; uint8_t v___x_527_; 
v_key_525_ = lean_ctor_get(v_x_523_, 0);
v_tail_526_ = lean_ctor_get(v_x_523_, 2);
v___x_527_ = lean_string_dec_eq(v_key_525_, v_a_522_);
if (v___x_527_ == 0)
{
v_x_523_ = v_tail_526_;
goto _start;
}
else
{
return v___x_527_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0___redArg___boxed(lean_object* v_a_529_, lean_object* v_x_530_){
_start:
{
uint8_t v_res_531_; lean_object* v_r_532_; 
v_res_531_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0___redArg(v_a_529_, v_x_530_);
lean_dec(v_x_530_);
lean_dec_ref(v_a_529_);
v_r_532_ = lean_box(v_res_531_);
return v_r_532_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_533_, lean_object* v_x_534_){
_start:
{
if (lean_obj_tag(v_x_534_) == 0)
{
return v_x_533_;
}
else
{
lean_object* v_key_535_; lean_object* v_value_536_; lean_object* v_tail_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_560_; 
v_key_535_ = lean_ctor_get(v_x_534_, 0);
v_value_536_ = lean_ctor_get(v_x_534_, 1);
v_tail_537_ = lean_ctor_get(v_x_534_, 2);
v_isSharedCheck_560_ = !lean_is_exclusive(v_x_534_);
if (v_isSharedCheck_560_ == 0)
{
v___x_539_ = v_x_534_;
v_isShared_540_ = v_isSharedCheck_560_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_tail_537_);
lean_inc(v_value_536_);
lean_inc(v_key_535_);
lean_dec(v_x_534_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_560_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_541_; uint64_t v___x_542_; uint64_t v___x_543_; uint64_t v___x_544_; uint64_t v_fold_545_; uint64_t v___x_546_; uint64_t v___x_547_; uint64_t v___x_548_; size_t v___x_549_; size_t v___x_550_; size_t v___x_551_; size_t v___x_552_; size_t v___x_553_; lean_object* v___x_554_; lean_object* v___x_556_; 
v___x_541_ = lean_array_get_size(v_x_533_);
v___x_542_ = lean_string_hash(v_key_535_);
v___x_543_ = 32ULL;
v___x_544_ = lean_uint64_shift_right(v___x_542_, v___x_543_);
v_fold_545_ = lean_uint64_xor(v___x_542_, v___x_544_);
v___x_546_ = 16ULL;
v___x_547_ = lean_uint64_shift_right(v_fold_545_, v___x_546_);
v___x_548_ = lean_uint64_xor(v_fold_545_, v___x_547_);
v___x_549_ = lean_uint64_to_usize(v___x_548_);
v___x_550_ = lean_usize_of_nat(v___x_541_);
v___x_551_ = ((size_t)1ULL);
v___x_552_ = lean_usize_sub(v___x_550_, v___x_551_);
v___x_553_ = lean_usize_land(v___x_549_, v___x_552_);
v___x_554_ = lean_array_uget_borrowed(v_x_533_, v___x_553_);
lean_inc(v___x_554_);
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 2, v___x_554_);
v___x_556_ = v___x_539_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_key_535_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v_value_536_);
lean_ctor_set(v_reuseFailAlloc_559_, 2, v___x_554_);
v___x_556_ = v_reuseFailAlloc_559_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
lean_object* v___x_557_; 
v___x_557_ = lean_array_uset(v_x_533_, v___x_553_, v___x_556_);
v_x_533_ = v___x_557_;
v_x_534_ = v_tail_537_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2___redArg(lean_object* v_i_561_, lean_object* v_source_562_, lean_object* v_target_563_){
_start:
{
lean_object* v___x_564_; uint8_t v___x_565_; 
v___x_564_ = lean_array_get_size(v_source_562_);
v___x_565_ = lean_nat_dec_lt(v_i_561_, v___x_564_);
if (v___x_565_ == 0)
{
lean_dec_ref(v_source_562_);
lean_dec(v_i_561_);
return v_target_563_;
}
else
{
lean_object* v_es_566_; lean_object* v___x_567_; lean_object* v_source_568_; lean_object* v_target_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v_es_566_ = lean_array_fget(v_source_562_, v_i_561_);
v___x_567_ = lean_box(0);
v_source_568_ = lean_array_fset(v_source_562_, v_i_561_, v___x_567_);
v_target_569_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2_spec__3___redArg(v_target_563_, v_es_566_);
v___x_570_ = lean_unsigned_to_nat(1u);
v___x_571_ = lean_nat_add(v_i_561_, v___x_570_);
lean_dec(v_i_561_);
v_i_561_ = v___x_571_;
v_source_562_ = v_source_568_;
v_target_563_ = v_target_569_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1___redArg(lean_object* v_data_573_){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v_nbuckets_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_574_ = lean_array_get_size(v_data_573_);
v___x_575_ = lean_unsigned_to_nat(2u);
v_nbuckets_576_ = lean_nat_mul(v___x_574_, v___x_575_);
v___x_577_ = lean_unsigned_to_nat(0u);
v___x_578_ = lean_box(0);
v___x_579_ = lean_mk_array(v_nbuckets_576_, v___x_578_);
v___x_580_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2___redArg(v___x_577_, v_data_573_, v___x_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__2___lam__0(lean_object* v_i_581_, lean_object* v_x_582_){
_start:
{
if (lean_obj_tag(v_x_582_) == 0)
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_583_ = lean_unsigned_to_nat(1u);
v___x_584_ = lean_mk_empty_array_with_capacity(v___x_583_);
v___x_585_ = lean_array_push(v___x_584_, v_i_581_);
v___x_586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_586_, 0, v___x_585_);
return v___x_586_;
}
else
{
lean_object* v_val_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_595_; 
v_val_587_ = lean_ctor_get(v_x_582_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v_x_582_);
if (v_isSharedCheck_595_ == 0)
{
v___x_589_ = v_x_582_;
v_isShared_590_ = v_isSharedCheck_595_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_val_587_);
lean_dec(v_x_582_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_595_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_591_; lean_object* v___x_593_; 
v___x_591_ = lean_array_push(v_val_587_, v_i_581_);
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 0, v___x_591_);
v___x_593_ = v___x_589_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_591_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__2(lean_object* v_i_596_, lean_object* v_a_597_, lean_object* v_x_598_){
_start:
{
if (lean_obj_tag(v_x_598_) == 0)
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v_val_601_; lean_object* v___x_602_; 
v___x_599_ = lean_box(0);
v___x_600_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__2___lam__0(v_i_596_, v___x_599_);
v_val_601_ = lean_ctor_get(v___x_600_, 0);
lean_inc(v_val_601_);
lean_dec(v___x_600_);
v___x_602_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_602_, 0, v_a_597_);
lean_ctor_set(v___x_602_, 1, v_val_601_);
lean_ctor_set(v___x_602_, 2, v_x_598_);
return v___x_602_;
}
else
{
lean_object* v_key_603_; lean_object* v_value_604_; lean_object* v_tail_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_620_; 
v_key_603_ = lean_ctor_get(v_x_598_, 0);
v_value_604_ = lean_ctor_get(v_x_598_, 1);
v_tail_605_ = lean_ctor_get(v_x_598_, 2);
v_isSharedCheck_620_ = !lean_is_exclusive(v_x_598_);
if (v_isSharedCheck_620_ == 0)
{
v___x_607_ = v_x_598_;
v_isShared_608_ = v_isSharedCheck_620_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_tail_605_);
lean_inc(v_value_604_);
lean_inc(v_key_603_);
lean_dec(v_x_598_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_620_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
uint8_t v___x_609_; 
v___x_609_ = lean_string_dec_eq(v_key_603_, v_a_597_);
if (v___x_609_ == 0)
{
lean_object* v_tail_610_; lean_object* v___x_612_; 
v_tail_610_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__2(v_i_596_, v_a_597_, v_tail_605_);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 2, v_tail_610_);
v___x_612_ = v___x_607_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_key_603_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v_value_604_);
lean_ctor_set(v_reuseFailAlloc_613_, 2, v_tail_610_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
else
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v_val_616_; lean_object* v___x_618_; 
lean_dec(v_key_603_);
v___x_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_614_, 0, v_value_604_);
v___x_615_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__2___lam__0(v_i_596_, v___x_614_);
v_val_616_ = lean_ctor_get(v___x_615_, 0);
lean_inc(v_val_616_);
lean_dec(v___x_615_);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 1, v_val_616_);
lean_ctor_set(v___x_607_, 0, v_a_597_);
v___x_618_ = v___x_607_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_a_597_);
lean_ctor_set(v_reuseFailAlloc_619_, 1, v_val_616_);
lean_ctor_set(v_reuseFailAlloc_619_, 2, v_tail_605_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0(lean_object* v_i_621_, lean_object* v_m_622_, lean_object* v_a_623_){
_start:
{
lean_object* v_size_624_; lean_object* v_buckets_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_675_; 
v_size_624_ = lean_ctor_get(v_m_622_, 0);
v_buckets_625_ = lean_ctor_get(v_m_622_, 1);
v_isSharedCheck_675_ = !lean_is_exclusive(v_m_622_);
if (v_isSharedCheck_675_ == 0)
{
v___x_627_ = v_m_622_;
v_isShared_628_ = v_isSharedCheck_675_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_buckets_625_);
lean_inc(v_size_624_);
lean_dec(v_m_622_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_675_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_629_; uint64_t v___x_630_; uint64_t v___x_631_; uint64_t v___x_632_; uint64_t v_fold_633_; uint64_t v___x_634_; uint64_t v___x_635_; uint64_t v___x_636_; size_t v___x_637_; size_t v___x_638_; size_t v___x_639_; size_t v___x_640_; size_t v___x_641_; lean_object* v_bkt_642_; uint8_t v___x_643_; 
v___x_629_ = lean_array_get_size(v_buckets_625_);
v___x_630_ = lean_string_hash(v_a_623_);
v___x_631_ = 32ULL;
v___x_632_ = lean_uint64_shift_right(v___x_630_, v___x_631_);
v_fold_633_ = lean_uint64_xor(v___x_630_, v___x_632_);
v___x_634_ = 16ULL;
v___x_635_ = lean_uint64_shift_right(v_fold_633_, v___x_634_);
v___x_636_ = lean_uint64_xor(v_fold_633_, v___x_635_);
v___x_637_ = lean_uint64_to_usize(v___x_636_);
v___x_638_ = lean_usize_of_nat(v___x_629_);
v___x_639_ = ((size_t)1ULL);
v___x_640_ = lean_usize_sub(v___x_638_, v___x_639_);
v___x_641_ = lean_usize_land(v___x_637_, v___x_640_);
v_bkt_642_ = lean_array_uget_borrowed(v_buckets_625_, v___x_641_);
v___x_643_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0___redArg(v_a_623_, v_bkt_642_);
if (v___x_643_ == 0)
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v_size_x27_647_; lean_object* v___x_648_; lean_object* v_buckets_x27_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; uint8_t v___x_655_; 
v___x_644_ = lean_unsigned_to_nat(1u);
v___x_645_ = lean_mk_empty_array_with_capacity(v___x_644_);
v___x_646_ = lean_array_push(v___x_645_, v_i_621_);
v_size_x27_647_ = lean_nat_add(v_size_624_, v___x_644_);
lean_dec(v_size_624_);
lean_inc(v_bkt_642_);
v___x_648_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_648_, 0, v_a_623_);
lean_ctor_set(v___x_648_, 1, v___x_646_);
lean_ctor_set(v___x_648_, 2, v_bkt_642_);
v_buckets_x27_649_ = lean_array_uset(v_buckets_625_, v___x_641_, v___x_648_);
v___x_650_ = lean_unsigned_to_nat(4u);
v___x_651_ = lean_nat_mul(v_size_x27_647_, v___x_650_);
v___x_652_ = lean_unsigned_to_nat(3u);
v___x_653_ = lean_nat_div(v___x_651_, v___x_652_);
lean_dec(v___x_651_);
v___x_654_ = lean_array_get_size(v_buckets_x27_649_);
v___x_655_ = lean_nat_dec_le(v___x_653_, v___x_654_);
lean_dec(v___x_653_);
if (v___x_655_ == 0)
{
lean_object* v_val_656_; lean_object* v___x_658_; 
v_val_656_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1___redArg(v_buckets_x27_649_);
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 1, v_val_656_);
lean_ctor_set(v___x_627_, 0, v_size_x27_647_);
v___x_658_ = v___x_627_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_size_x27_647_);
lean_ctor_set(v_reuseFailAlloc_659_, 1, v_val_656_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
else
{
lean_object* v___x_661_; 
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 1, v_buckets_x27_649_);
lean_ctor_set(v___x_627_, 0, v_size_x27_647_);
v___x_661_ = v___x_627_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_size_x27_647_);
lean_ctor_set(v_reuseFailAlloc_662_, 1, v_buckets_x27_649_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
else
{
lean_object* v___x_663_; lean_object* v_buckets_x27_664_; lean_object* v_bkt_x27_665_; lean_object* v___y_667_; uint8_t v___x_672_; 
lean_inc(v_bkt_642_);
v___x_663_ = lean_box(0);
v_buckets_x27_664_ = lean_array_uset(v_buckets_625_, v___x_641_, v___x_663_);
lean_inc_ref(v_a_623_);
v_bkt_x27_665_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__2(v_i_621_, v_a_623_, v_bkt_642_);
v___x_672_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0___redArg(v_a_623_, v_bkt_x27_665_);
lean_dec_ref(v_a_623_);
if (v___x_672_ == 0)
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = lean_unsigned_to_nat(1u);
v___x_674_ = lean_nat_sub(v_size_624_, v___x_673_);
lean_dec(v_size_624_);
v___y_667_ = v___x_674_;
goto v___jp_666_;
}
else
{
v___y_667_ = v_size_624_;
goto v___jp_666_;
}
v___jp_666_:
{
lean_object* v___x_668_; lean_object* v___x_670_; 
v___x_668_ = lean_array_uset(v_buckets_x27_664_, v___x_641_, v_bkt_x27_665_);
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 1, v___x_668_);
lean_ctor_set(v___x_627_, 0, v___y_667_);
v___x_670_ = v___x_627_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v___y_667_);
lean_ctor_set(v_reuseFailAlloc_671_, 1, v___x_668_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_header(lean_object* v_builder_676_, lean_object* v_key_677_, lean_object* v_value_678_){
_start:
{
lean_object* v_line_679_; lean_object* v_headers_680_; lean_object* v_extensions_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_711_; 
v_line_679_ = lean_ctor_get(v_builder_676_, 0);
lean_inc_ref(v_line_679_);
v_headers_680_ = lean_ctor_get(v_line_679_, 1);
lean_inc_ref(v_headers_680_);
v_extensions_681_ = lean_ctor_get(v_builder_676_, 1);
v_isSharedCheck_711_ = !lean_is_exclusive(v_builder_676_);
if (v_isSharedCheck_711_ == 0)
{
lean_object* v_unused_712_; 
v_unused_712_ = lean_ctor_get(v_builder_676_, 0);
lean_dec(v_unused_712_);
v___x_683_ = v_builder_676_;
v_isShared_684_ = v_isSharedCheck_711_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_extensions_681_);
lean_dec(v_builder_676_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_711_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v_status_685_; uint8_t v_version_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_709_; 
v_status_685_ = lean_ctor_get(v_line_679_, 0);
v_version_686_ = lean_ctor_get_uint8(v_line_679_, sizeof(void*)*2);
v_isSharedCheck_709_ = !lean_is_exclusive(v_line_679_);
if (v_isSharedCheck_709_ == 0)
{
lean_object* v_unused_710_; 
v_unused_710_ = lean_ctor_get(v_line_679_, 1);
lean_dec(v_unused_710_);
v___x_688_ = v_line_679_;
v_isShared_689_ = v_isSharedCheck_709_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_status_685_);
lean_dec(v_line_679_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_709_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v_entries_690_; lean_object* v_indexes_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_708_; 
v_entries_690_ = lean_ctor_get(v_headers_680_, 0);
v_indexes_691_ = lean_ctor_get(v_headers_680_, 1);
v_isSharedCheck_708_ = !lean_is_exclusive(v_headers_680_);
if (v_isSharedCheck_708_ == 0)
{
v___x_693_ = v_headers_680_;
v_isShared_694_ = v_isSharedCheck_708_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_indexes_691_);
lean_inc(v_entries_690_);
lean_dec(v_headers_680_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_708_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v_i_695_; lean_object* v___x_696_; lean_object* v_entries_697_; lean_object* v_indexes_698_; lean_object* v___x_700_; 
v_i_695_ = lean_array_get_size(v_entries_690_);
lean_inc_ref(v_key_677_);
v___x_696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_696_, 0, v_key_677_);
lean_ctor_set(v___x_696_, 1, v_value_678_);
v_entries_697_ = lean_array_push(v_entries_690_, v___x_696_);
v_indexes_698_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0(v_i_695_, v_indexes_691_, v_key_677_);
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 1, v_indexes_698_);
lean_ctor_set(v___x_693_, 0, v_entries_697_);
v___x_700_ = v___x_693_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_entries_697_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v_indexes_698_);
v___x_700_ = v_reuseFailAlloc_707_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
lean_object* v___x_702_; 
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 1, v___x_700_);
v___x_702_ = v___x_688_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_status_685_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v___x_700_);
lean_ctor_set_uint8(v_reuseFailAlloc_706_, sizeof(void*)*2, v_version_686_);
v___x_702_ = v_reuseFailAlloc_706_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
lean_object* v___x_704_; 
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 0, v___x_702_);
v___x_704_ = v___x_683_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_702_);
lean_ctor_set(v_reuseFailAlloc_705_, 1, v_extensions_681_);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0(lean_object* v_00_u03b2_713_, lean_object* v_a_714_, lean_object* v_x_715_){
_start:
{
uint8_t v___x_716_; 
v___x_716_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0___redArg(v_a_714_, v_x_715_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0___boxed(lean_object* v_00_u03b2_717_, lean_object* v_a_718_, lean_object* v_x_719_){
_start:
{
uint8_t v_res_720_; lean_object* v_r_721_; 
v_res_720_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0(v_00_u03b2_717_, v_a_718_, v_x_719_);
lean_dec(v_x_719_);
lean_dec_ref(v_a_718_);
v_r_721_ = lean_box(v_res_720_);
return v_r_721_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1(lean_object* v_00_u03b2_722_, lean_object* v_data_723_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1___redArg(v_data_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_725_, lean_object* v_i_726_, lean_object* v_source_727_, lean_object* v_target_728_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2___redArg(v_i_726_, v_source_727_, v_target_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_730_, lean_object* v_x_731_, lean_object* v_x_732_){
_start:
{
lean_object* v___x_733_; 
v___x_733_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2_spec__3___redArg(v_x_731_, v_x_732_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_header_x21(lean_object* v_builder_734_, lean_object* v_key_735_, lean_object* v_value_736_){
_start:
{
lean_object* v_line_737_; lean_object* v_headers_738_; lean_object* v_extensions_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_771_; 
v_line_737_ = lean_ctor_get(v_builder_734_, 0);
lean_inc_ref(v_line_737_);
v_headers_738_ = lean_ctor_get(v_line_737_, 1);
lean_inc_ref(v_headers_738_);
v_extensions_739_ = lean_ctor_get(v_builder_734_, 1);
v_isSharedCheck_771_ = !lean_is_exclusive(v_builder_734_);
if (v_isSharedCheck_771_ == 0)
{
lean_object* v_unused_772_; 
v_unused_772_ = lean_ctor_get(v_builder_734_, 0);
lean_dec(v_unused_772_);
v___x_741_ = v_builder_734_;
v_isShared_742_ = v_isSharedCheck_771_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_extensions_739_);
lean_dec(v_builder_734_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_771_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v_status_743_; uint8_t v_version_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_769_; 
v_status_743_ = lean_ctor_get(v_line_737_, 0);
v_version_744_ = lean_ctor_get_uint8(v_line_737_, sizeof(void*)*2);
v_isSharedCheck_769_ = !lean_is_exclusive(v_line_737_);
if (v_isSharedCheck_769_ == 0)
{
lean_object* v_unused_770_; 
v_unused_770_ = lean_ctor_get(v_line_737_, 1);
lean_dec(v_unused_770_);
v___x_746_ = v_line_737_;
v_isShared_747_ = v_isSharedCheck_769_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_status_743_);
lean_dec(v_line_737_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_769_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v_entries_748_; lean_object* v_indexes_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_768_; 
v_entries_748_ = lean_ctor_get(v_headers_738_, 0);
v_indexes_749_ = lean_ctor_get(v_headers_738_, 1);
v_isSharedCheck_768_ = !lean_is_exclusive(v_headers_738_);
if (v_isSharedCheck_768_ == 0)
{
v___x_751_ = v_headers_738_;
v_isShared_752_ = v_isSharedCheck_768_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_indexes_749_);
lean_inc(v_entries_748_);
lean_dec(v_headers_738_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_768_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v_key_753_; lean_object* v_value_754_; lean_object* v_i_755_; lean_object* v___x_756_; lean_object* v_entries_757_; lean_object* v_indexes_758_; lean_object* v___x_760_; 
v_key_753_ = l_Std_Http_Header_Name_ofString_x21(v_key_735_);
v_value_754_ = l_Std_Http_Header_Value_ofString_x21(v_value_736_);
v_i_755_ = lean_array_get_size(v_entries_748_);
lean_inc_ref(v_key_753_);
v___x_756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_756_, 0, v_key_753_);
lean_ctor_set(v___x_756_, 1, v_value_754_);
v_entries_757_ = lean_array_push(v_entries_748_, v___x_756_);
v_indexes_758_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0(v_i_755_, v_indexes_749_, v_key_753_);
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 1, v_indexes_758_);
lean_ctor_set(v___x_751_, 0, v_entries_757_);
v___x_760_ = v___x_751_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_entries_757_);
lean_ctor_set(v_reuseFailAlloc_767_, 1, v_indexes_758_);
v___x_760_ = v_reuseFailAlloc_767_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
lean_object* v___x_762_; 
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 1, v___x_760_);
v___x_762_ = v___x_746_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_status_743_);
lean_ctor_set(v_reuseFailAlloc_766_, 1, v___x_760_);
lean_ctor_set_uint8(v_reuseFailAlloc_766_, sizeof(void*)*2, v_version_744_);
v___x_762_ = v_reuseFailAlloc_766_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
lean_object* v___x_764_; 
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 0, v___x_762_);
v___x_764_ = v___x_741_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v___x_762_);
lean_ctor_set(v_reuseFailAlloc_765_, 1, v_extensions_739_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_header_x3f(lean_object* v_builder_773_, lean_object* v_key_774_, lean_object* v_value_775_){
_start:
{
lean_object* v___x_776_; 
v___x_776_ = l_Std_Http_Header_Name_ofString_x3f(v_key_774_);
if (lean_obj_tag(v___x_776_) == 0)
{
lean_object* v___x_777_; 
lean_dec_ref(v_value_775_);
lean_dec_ref(v_builder_773_);
v___x_777_ = lean_box(0);
return v___x_777_;
}
else
{
lean_object* v_val_778_; lean_object* v___x_779_; 
v_val_778_ = lean_ctor_get(v___x_776_, 0);
lean_inc(v_val_778_);
lean_dec_ref(v___x_776_);
v___x_779_ = l_Std_Http_Header_Value_ofString_x3f(v_value_775_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_object* v___x_780_; 
lean_dec(v_val_778_);
lean_dec_ref(v_builder_773_);
v___x_780_ = lean_box(0);
return v___x_780_;
}
else
{
lean_object* v_line_781_; lean_object* v_headers_782_; lean_object* v_val_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_822_; 
v_line_781_ = lean_ctor_get(v_builder_773_, 0);
lean_inc_ref(v_line_781_);
v_headers_782_ = lean_ctor_get(v_line_781_, 1);
lean_inc_ref(v_headers_782_);
v_val_783_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_822_ == 0)
{
v___x_785_ = v___x_779_;
v_isShared_786_ = v_isSharedCheck_822_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_val_783_);
lean_dec(v___x_779_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_822_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v_extensions_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_820_; 
v_extensions_787_ = lean_ctor_get(v_builder_773_, 1);
v_isSharedCheck_820_ = !lean_is_exclusive(v_builder_773_);
if (v_isSharedCheck_820_ == 0)
{
lean_object* v_unused_821_; 
v_unused_821_ = lean_ctor_get(v_builder_773_, 0);
lean_dec(v_unused_821_);
v___x_789_ = v_builder_773_;
v_isShared_790_ = v_isSharedCheck_820_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_extensions_787_);
lean_dec(v_builder_773_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_820_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v_status_791_; uint8_t v_version_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_818_; 
v_status_791_ = lean_ctor_get(v_line_781_, 0);
v_version_792_ = lean_ctor_get_uint8(v_line_781_, sizeof(void*)*2);
v_isSharedCheck_818_ = !lean_is_exclusive(v_line_781_);
if (v_isSharedCheck_818_ == 0)
{
lean_object* v_unused_819_; 
v_unused_819_ = lean_ctor_get(v_line_781_, 1);
lean_dec(v_unused_819_);
v___x_794_ = v_line_781_;
v_isShared_795_ = v_isSharedCheck_818_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_status_791_);
lean_dec(v_line_781_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_818_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v_entries_796_; lean_object* v_indexes_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_817_; 
v_entries_796_ = lean_ctor_get(v_headers_782_, 0);
v_indexes_797_ = lean_ctor_get(v_headers_782_, 1);
v_isSharedCheck_817_ = !lean_is_exclusive(v_headers_782_);
if (v_isSharedCheck_817_ == 0)
{
v___x_799_ = v_headers_782_;
v_isShared_800_ = v_isSharedCheck_817_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_indexes_797_);
lean_inc(v_entries_796_);
lean_dec(v_headers_782_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_817_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v_i_801_; lean_object* v___x_802_; lean_object* v_entries_803_; lean_object* v_indexes_804_; lean_object* v___x_806_; 
v_i_801_ = lean_array_get_size(v_entries_796_);
lean_inc(v_val_778_);
v___x_802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_802_, 0, v_val_778_);
lean_ctor_set(v___x_802_, 1, v_val_783_);
v_entries_803_ = lean_array_push(v_entries_796_, v___x_802_);
v_indexes_804_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0(v_i_801_, v_indexes_797_, v_val_778_);
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 1, v_indexes_804_);
lean_ctor_set(v___x_799_, 0, v_entries_803_);
v___x_806_ = v___x_799_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_entries_803_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v_indexes_804_);
v___x_806_ = v_reuseFailAlloc_816_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
lean_object* v___x_808_; 
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 1, v___x_806_);
v___x_808_ = v___x_794_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_status_791_);
lean_ctor_set(v_reuseFailAlloc_815_, 1, v___x_806_);
lean_ctor_set_uint8(v_reuseFailAlloc_815_, sizeof(void*)*2, v_version_792_);
v___x_808_ = v_reuseFailAlloc_815_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
lean_object* v___x_810_; 
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 0, v___x_808_);
v___x_810_ = v___x_789_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v___x_808_);
lean_ctor_set(v_reuseFailAlloc_814_, 1, v_extensions_787_);
v___x_810_ = v_reuseFailAlloc_814_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
lean_object* v___x_812_; 
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 0, v___x_810_);
v___x_812_ = v___x_785_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v___x_810_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
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
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_extension___redArg(lean_object* v_builder_824_, lean_object* v_inst_825_, lean_object* v_data_826_){
_start:
{
lean_object* v_line_827_; lean_object* v_extensions_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_839_; 
v_line_827_ = lean_ctor_get(v_builder_824_, 0);
v_extensions_828_ = lean_ctor_get(v_builder_824_, 1);
v_isSharedCheck_839_ = !lean_is_exclusive(v_builder_824_);
if (v_isSharedCheck_839_ == 0)
{
v___x_830_ = v_builder_824_;
v_isShared_831_ = v_isSharedCheck_839_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_extensions_828_);
lean_inc(v_line_827_);
lean_dec(v_builder_824_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_839_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v_dyn_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_837_; 
v_dyn_832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_dyn_832_, 0, v_inst_825_);
lean_ctor_set(v_dyn_832_, 1, v_data_826_);
v___x_833_ = ((lean_object*)(l_Std_Http_Response_Builder_extension___redArg___closed__0));
v___x_834_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_dyn_832_);
v___x_835_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_833_, v___x_834_, v_dyn_832_, v_extensions_828_);
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 1, v___x_835_);
v___x_837_ = v___x_830_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_line_827_);
lean_ctor_set(v_reuseFailAlloc_838_, 1, v___x_835_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_extension(lean_object* v_00_u03b1_840_, lean_object* v_builder_841_, lean_object* v_inst_842_, lean_object* v_data_843_){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = l_Std_Http_Response_Builder_extension___redArg(v_builder_841_, v_inst_842_, v_data_843_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_body___redArg(lean_object* v_builder_845_, lean_object* v_body_846_){
_start:
{
lean_object* v_line_847_; lean_object* v_extensions_848_; lean_object* v___x_849_; 
v_line_847_ = lean_ctor_get(v_builder_845_, 0);
v_extensions_848_ = lean_ctor_get(v_builder_845_, 1);
lean_inc(v_extensions_848_);
lean_inc_ref(v_line_847_);
v___x_849_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_849_, 0, v_line_847_);
lean_ctor_set(v___x_849_, 1, v_body_846_);
lean_ctor_set(v___x_849_, 2, v_extensions_848_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_body___redArg___boxed(lean_object* v_builder_850_, lean_object* v_body_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l_Std_Http_Response_Builder_body___redArg(v_builder_850_, v_body_851_);
lean_dec_ref(v_builder_850_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_body(lean_object* v_t_853_, lean_object* v_builder_854_, lean_object* v_body_855_){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = l_Std_Http_Response_Builder_body___redArg(v_builder_854_, v_body_855_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_body___boxed(lean_object* v_t_857_, lean_object* v_builder_858_, lean_object* v_body_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_Std_Http_Response_Builder_body(v_t_857_, v_builder_858_, v_body_859_);
lean_dec_ref(v_builder_858_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_build___redArg(lean_object* v_inst_861_, lean_object* v_builder_862_){
_start:
{
lean_object* v_line_863_; lean_object* v_extensions_864_; lean_object* v___x_865_; 
v_line_863_ = lean_ctor_get(v_builder_862_, 0);
v_extensions_864_ = lean_ctor_get(v_builder_862_, 1);
lean_inc(v_extensions_864_);
lean_inc_ref(v_line_863_);
v___x_865_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_865_, 0, v_line_863_);
lean_ctor_set(v___x_865_, 1, v_inst_861_);
lean_ctor_set(v___x_865_, 2, v_extensions_864_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_build___redArg___boxed(lean_object* v_inst_866_, lean_object* v_builder_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_Std_Http_Response_Builder_build___redArg(v_inst_866_, v_builder_867_);
lean_dec_ref(v_builder_867_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_build(lean_object* v_t_869_, lean_object* v_inst_870_, lean_object* v_builder_871_){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = l_Std_Http_Response_Builder_build___redArg(v_inst_870_, v_builder_871_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_build___boxed(lean_object* v_t_873_, lean_object* v_inst_874_, lean_object* v_builder_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_Std_Http_Response_Builder_build(v_t_873_, v_inst_874_, v_builder_875_);
lean_dec_ref(v_builder_875_);
return v_res_876_;
}
}
static lean_object* _init_l_Std_Http_Response_ok___closed__0(void){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_877_ = lean_box(4);
v___x_878_ = l_Std_Http_Response_Builder_new;
v___x_879_ = l_Std_Http_Response_Builder_status(v___x_878_, v___x_877_);
return v___x_879_;
}
}
static lean_object* _init_l_Std_Http_Response_ok(void){
_start:
{
lean_object* v___x_880_; 
v___x_880_ = lean_obj_once(&l_Std_Http_Response_ok___closed__0, &l_Std_Http_Response_ok___closed__0_once, _init_l_Std_Http_Response_ok___closed__0);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_withStatus(lean_object* v_status_881_){
_start:
{
lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_882_ = l_Std_Http_Response_Builder_new;
v___x_883_ = l_Std_Http_Response_Builder_status(v___x_882_, v_status_881_);
return v___x_883_;
}
}
static lean_object* _init_l_Std_Http_Response_notFound___closed__0(void){
_start:
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_884_ = lean_box(27);
v___x_885_ = l_Std_Http_Response_Builder_new;
v___x_886_ = l_Std_Http_Response_Builder_status(v___x_885_, v___x_884_);
return v___x_886_;
}
}
static lean_object* _init_l_Std_Http_Response_notFound(void){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = lean_obj_once(&l_Std_Http_Response_notFound___closed__0, &l_Std_Http_Response_notFound___closed__0_once, _init_l_Std_Http_Response_notFound___closed__0);
return v___x_887_;
}
}
static lean_object* _init_l_Std_Http_Response_internalServerError___closed__0(void){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_888_ = lean_box(52);
v___x_889_ = l_Std_Http_Response_Builder_new;
v___x_890_ = l_Std_Http_Response_Builder_status(v___x_889_, v___x_888_);
return v___x_890_;
}
}
static lean_object* _init_l_Std_Http_Response_internalServerError(void){
_start:
{
lean_object* v___x_891_; 
v___x_891_ = lean_obj_once(&l_Std_Http_Response_internalServerError___closed__0, &l_Std_Http_Response_internalServerError___closed__0_once, _init_l_Std_Http_Response_internalServerError___closed__0);
return v___x_891_;
}
}
static lean_object* _init_l_Std_Http_Response_badRequest___closed__0(void){
_start:
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_892_ = lean_box(23);
v___x_893_ = l_Std_Http_Response_Builder_new;
v___x_894_ = l_Std_Http_Response_Builder_status(v___x_893_, v___x_892_);
return v___x_894_;
}
}
static lean_object* _init_l_Std_Http_Response_badRequest(void){
_start:
{
lean_object* v___x_895_; 
v___x_895_ = lean_obj_once(&l_Std_Http_Response_badRequest___closed__0, &l_Std_Http_Response_badRequest___closed__0_once, _init_l_Std_Http_Response_badRequest___closed__0);
return v___x_895_;
}
}
static lean_object* _init_l_Std_Http_Response_created___closed__0(void){
_start:
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_896_ = lean_box(5);
v___x_897_ = l_Std_Http_Response_Builder_new;
v___x_898_ = l_Std_Http_Response_Builder_status(v___x_897_, v___x_896_);
return v___x_898_;
}
}
static lean_object* _init_l_Std_Http_Response_created(void){
_start:
{
lean_object* v___x_899_; 
v___x_899_ = lean_obj_once(&l_Std_Http_Response_created___closed__0, &l_Std_Http_Response_created___closed__0_once, _init_l_Std_Http_Response_created___closed__0);
return v___x_899_;
}
}
static lean_object* _init_l_Std_Http_Response_accepted___closed__0(void){
_start:
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_900_ = lean_box(6);
v___x_901_ = l_Std_Http_Response_Builder_new;
v___x_902_ = l_Std_Http_Response_Builder_status(v___x_901_, v___x_900_);
return v___x_902_;
}
}
static lean_object* _init_l_Std_Http_Response_accepted(void){
_start:
{
lean_object* v___x_903_; 
v___x_903_ = lean_obj_once(&l_Std_Http_Response_accepted___closed__0, &l_Std_Http_Response_accepted___closed__0_once, _init_l_Std_Http_Response_accepted___closed__0);
return v___x_903_;
}
}
static lean_object* _init_l_Std_Http_Response_unauthorized___closed__0(void){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_904_ = lean_box(24);
v___x_905_ = l_Std_Http_Response_Builder_new;
v___x_906_ = l_Std_Http_Response_Builder_status(v___x_905_, v___x_904_);
return v___x_906_;
}
}
static lean_object* _init_l_Std_Http_Response_unauthorized(void){
_start:
{
lean_object* v___x_907_; 
v___x_907_ = lean_obj_once(&l_Std_Http_Response_unauthorized___closed__0, &l_Std_Http_Response_unauthorized___closed__0_once, _init_l_Std_Http_Response_unauthorized___closed__0);
return v___x_907_;
}
}
static lean_object* _init_l_Std_Http_Response_forbidden___closed__0(void){
_start:
{
lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_908_ = lean_box(26);
v___x_909_ = l_Std_Http_Response_Builder_new;
v___x_910_ = l_Std_Http_Response_Builder_status(v___x_909_, v___x_908_);
return v___x_910_;
}
}
static lean_object* _init_l_Std_Http_Response_forbidden(void){
_start:
{
lean_object* v___x_911_; 
v___x_911_ = lean_obj_once(&l_Std_Http_Response_forbidden___closed__0, &l_Std_Http_Response_forbidden___closed__0_once, _init_l_Std_Http_Response_forbidden___closed__0);
return v___x_911_;
}
}
static lean_object* _init_l_Std_Http_Response_conflict___closed__0(void){
_start:
{
lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_912_ = lean_box(32);
v___x_913_ = l_Std_Http_Response_Builder_new;
v___x_914_ = l_Std_Http_Response_Builder_status(v___x_913_, v___x_912_);
return v___x_914_;
}
}
static lean_object* _init_l_Std_Http_Response_conflict(void){
_start:
{
lean_object* v___x_915_; 
v___x_915_ = lean_obj_once(&l_Std_Http_Response_conflict___closed__0, &l_Std_Http_Response_conflict___closed__0_once, _init_l_Std_Http_Response_conflict___closed__0);
return v___x_915_;
}
}
static lean_object* _init_l_Std_Http_Response_serviceUnavailable___closed__0(void){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_916_ = lean_box(55);
v___x_917_ = l_Std_Http_Response_Builder_new;
v___x_918_ = l_Std_Http_Response_Builder_status(v___x_917_, v___x_916_);
return v___x_918_;
}
}
static lean_object* _init_l_Std_Http_Response_serviceUnavailable(void){
_start:
{
lean_object* v___x_919_; 
v___x_919_ = lean_obj_once(&l_Std_Http_Response_serviceUnavailable___closed__0, &l_Std_Http_Response_serviceUnavailable___closed__0_once, _init_l_Std_Http_Response_serviceUnavailable___closed__0);
return v___x_919_;
}
}
lean_object* runtime_initialize_Std_Internal_Http_Data_Extensions(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Http_Data_Status(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Http_Data_Version(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Http_Data_Headers(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_Http_Data_Response(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Internal_Http_Data_Extensions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Data_Status(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Data_Version(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Data_Headers(builtin);
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
LEAN_EXPORT lean_object* meta_initialize_Std_Internal_Http_Data_Response(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Internal_Http_Data_Extensions(uint8_t builtin);
lean_object* initialize_Std_Internal_Http_Data_Status(uint8_t builtin);
lean_object* initialize_Std_Internal_Http_Data_Version(uint8_t builtin);
lean_object* initialize_Std_Internal_Http_Data_Headers(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Http_Data_Response(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Internal_Http_Data_Extensions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Http_Data_Status(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Http_Data_Version(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Http_Data_Headers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Data_Response(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Internal_Http_Data_Response(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Internal_Http_Data_Response(builtin);
}
#ifdef __cplusplus
}
#endif
