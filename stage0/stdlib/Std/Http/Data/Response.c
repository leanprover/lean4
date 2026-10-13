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
static const lean_string_object l_Std_Http_Response_instToStringHead___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_Http_Response_instToStringHead___lam__1___closed__3 = (const lean_object*)&l_Std_Http_Response_instToStringHead___lam__1___closed__3_value;
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
static const lean_sarray_object l_Std_Http_Response_instEncodeV11Head___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_sarray_object) + 1, .m_other = 1, .m_tag = 248}, .m_size = 1, .m_capacity = 1, .m_data = {32}};
static const lean_object* l_Std_Http_Response_instEncodeV11Head___lam__2___closed__0 = (const lean_object*)&l_Std_Http_Response_instEncodeV11Head___lam__2___closed__0_value;
static lean_once_cell_t l_Std_Http_Response_instEncodeV11Head___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_instEncodeV11Head___lam__2___closed__1;
static lean_once_cell_t l_Std_Http_Response_instEncodeV11Head___lam__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_instEncodeV11Head___lam__2___closed__2;
static lean_once_cell_t l_Std_Http_Response_instEncodeV11Head___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_instEncodeV11Head___lam__2___closed__3;
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
uint8_t v_decide_153_; 
v_decide_153_ = lean_nat_dec_eq(v_searcher_149_, v___x_109_);
if (v_decide_153_ == 0)
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
uint32_t v___x_750__boxed_183_; lean_object* v_res_184_; 
v___x_750__boxed_183_ = lean_unbox_uint32(v___x_177_);
lean_dec(v___x_177_);
v_res_184_ = l_Std_Http_Response_instToStringHead___lam__0(v___x_172_, v___x_173_, v___x_174_, v_fst_175_, v___x_176_, v___x_750__boxed_183_, v___x_178_, v_it_179_, v_acc_180_, v_hP_181_, v_recur_182_);
lean_dec_ref(v___x_178_);
lean_dec_ref(v_fst_175_);
lean_dec(v___x_174_);
lean_dec(v___x_173_);
lean_dec_ref(v___x_172_);
return v_res_184_;
}
}
static lean_object* _init_l_Std_Http_Response_instToStringHead___lam__1___boxed__const__1(void){
_start:
{
uint32_t v___x_189_; lean_object* v___x_190_; 
v___x_189_ = 45;
v___x_190_ = lean_box_uint32(v___x_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instToStringHead___lam__1(lean_object* v_x_191_){
_start:
{
lean_object* v_fst_192_; lean_object* v_snd_193_; lean_object* v___y_195_; lean_object* v___f_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v_it_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___f_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v_fst_192_ = lean_ctor_get(v_x_191_, 0);
lean_inc_n(v_fst_192_, 2);
v_snd_193_ = lean_ctor_get(v_x_191_, 1);
lean_inc(v_snd_193_);
lean_dec_ref(v_x_191_);
v___f_199_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__1___closed__1));
v___x_200_ = lean_unsigned_to_nat(0u);
v___x_201_ = lean_string_utf8_byte_size(v_fst_192_);
v___x_202_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_202_, 0, v_fst_192_);
lean_ctor_set(v___x_202_, 1, v___x_200_);
lean_ctor_set(v___x_202_, 2, v___x_201_);
lean_inc_ref(v___x_202_);
v_it_203_ = l_String_Slice_splitToSubslice___redArg(v___x_202_, v___f_199_);
v___x_204_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__1___closed__2));
v___x_205_ = lean_unsigned_to_nat(1u);
v___x_206_ = l_Std_Http_Response_instToStringHead___lam__1___boxed__const__1;
v___f_207_ = lean_alloc_closure((void*)(l_Std_Http_Response_instToStringHead___lam__0___boxed), 11, 7);
lean_closure_set(v___f_207_, 0, v___x_204_);
lean_closure_set(v___f_207_, 1, v___x_200_);
lean_closure_set(v___f_207_, 2, v___x_205_);
lean_closure_set(v___f_207_, 3, v_fst_192_);
lean_closure_set(v___f_207_, 4, v___x_201_);
lean_closure_set(v___f_207_, 5, v___x_206_);
lean_closure_set(v___f_207_, 6, v___x_202_);
v___x_208_ = lean_box(0);
v___x_209_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_207_, v_it_203_, v___x_208_, lean_box(0));
if (lean_obj_tag(v___x_209_) == 0)
{
lean_object* v___x_210_; 
v___x_210_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__1___closed__3));
v___y_195_ = v___x_210_;
goto v___jp_194_;
}
else
{
lean_object* v_val_211_; 
v_val_211_ = lean_ctor_get(v___x_209_, 0);
lean_inc(v_val_211_);
lean_dec_ref_known(v___x_209_, 1);
v___y_195_ = v_val_211_;
goto v___jp_194_;
}
v___jp_194_:
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_196_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__1___closed__0));
v___x_197_ = lean_string_append(v___y_195_, v___x_196_);
v___x_198_ = lean_string_append(v___x_197_, v_snd_193_);
lean_dec(v_snd_193_);
return v___x_198_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instToStringHead___lam__2(lean_object* v___f_237_, lean_object* v_r_238_){
_start:
{
lean_object* v_status_239_; uint8_t v_version_240_; lean_object* v_headers_241_; lean_object* v___y_243_; 
v_status_239_ = lean_ctor_get(v_r_238_, 0);
lean_inc(v_status_239_);
v_version_240_ = lean_ctor_get_uint8(v_r_238_, sizeof(void*)*2);
v_headers_241_ = lean_ctor_get(v_r_238_, 1);
lean_inc_ref(v_headers_241_);
lean_dec_ref(v_r_238_);
switch(v_version_240_)
{
case 0:
{
lean_object* v___x_264_; 
v___x_264_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__12));
v___y_243_ = v___x_264_;
goto v___jp_242_;
}
case 1:
{
lean_object* v___x_265_; 
v___x_265_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__13));
v___y_243_ = v___x_265_;
goto v___jp_242_;
}
case 2:
{
lean_object* v___x_266_; 
v___x_266_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__14));
v___y_243_ = v___x_266_;
goto v___jp_242_;
}
default: 
{
lean_object* v___x_267_; 
v___x_267_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__15));
v___y_243_ = v___x_267_;
goto v___jp_242_;
}
}
v___jp_242_:
{
lean_object* v_entries_244_; lean_object* v___x_245_; lean_object* v___x_246_; uint16_t v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; size_t v_sz_257_; size_t v___x_258_; lean_object* v_pairs_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v_entries_244_ = lean_ctor_get(v_headers_241_, 0);
lean_inc_ref(v_entries_244_);
lean_dec_ref(v_headers_241_);
v___x_245_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__0));
lean_inc_ref(v___y_243_);
v___x_246_ = lean_string_append(v___y_243_, v___x_245_);
v___x_247_ = l_Std_Http_Status_toCode(v_status_239_);
v___x_248_ = lean_uint16_to_nat(v___x_247_);
v___x_249_ = l_Nat_reprFast(v___x_248_);
v___x_250_ = lean_string_append(v___x_246_, v___x_249_);
lean_dec_ref(v___x_249_);
v___x_251_ = lean_string_append(v___x_250_, v___x_245_);
v___x_252_ = l_Std_Http_Status_reasonPhrase(v_status_239_);
lean_dec(v_status_239_);
v___x_253_ = lean_string_append(v___x_251_, v___x_252_);
lean_dec_ref(v___x_252_);
v___x_254_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__1));
v___x_255_ = lean_string_append(v___x_253_, v___x_254_);
v___x_256_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__11));
v_sz_257_ = lean_array_size(v_entries_244_);
v___x_258_ = ((size_t)0ULL);
v_pairs_259_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_256_, v___f_237_, v_sz_257_, v___x_258_, v_entries_244_);
v___x_260_ = lean_array_to_list(v_pairs_259_);
v___x_261_ = l_String_intercalate(v___x_254_, v___x_260_);
v___x_262_ = lean_string_append(v___x_255_, v___x_261_);
lean_dec_ref(v___x_261_);
v___x_263_ = lean_string_append(v___x_262_, v___x_254_);
return v___x_263_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instEncodeV11Head___lam__0(lean_object* v___x_272_, lean_object* v___x_273_, lean_object* v___x_274_, lean_object* v_name_275_, lean_object* v___x_276_, uint32_t v___x_277_, lean_object* v___x_278_, lean_object* v_it_279_, lean_object* v_acc_280_, lean_object* v_hP_281_, lean_object* v_recur_282_){
_start:
{
lean_object* v_it_284_; lean_object* v_out_285_; lean_object* v_it_301_; lean_object* v_startInclusive_302_; lean_object* v_endExclusive_303_; 
if (lean_obj_tag(v_it_279_) == 0)
{
lean_object* v_currPos_315_; lean_object* v_searcher_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_338_; 
v_currPos_315_ = lean_ctor_get(v_it_279_, 0);
v_searcher_316_ = lean_ctor_get(v_it_279_, 1);
v_isSharedCheck_338_ = !lean_is_exclusive(v_it_279_);
if (v_isSharedCheck_338_ == 0)
{
v___x_318_ = v_it_279_;
v_isShared_319_ = v_isSharedCheck_338_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_searcher_316_);
lean_inc(v_currPos_315_);
lean_dec(v_it_279_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_338_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
uint8_t v_decide_320_; 
v_decide_320_ = lean_nat_dec_eq(v_searcher_316_, v___x_276_);
if (v_decide_320_ == 0)
{
uint32_t v___x_321_; uint8_t v___x_322_; 
lean_dec(v___x_276_);
v___x_321_ = lean_string_utf8_get_fast(v_name_275_, v_searcher_316_);
v___x_322_ = lean_uint32_dec_eq(v___x_321_, v___x_277_);
if (v___x_322_ == 0)
{
lean_object* v___x_323_; lean_object* v___x_325_; 
v___x_323_ = lean_string_utf8_next_fast(v_name_275_, v_searcher_316_);
lean_dec(v_searcher_316_);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 1, v___x_323_);
v___x_325_ = v___x_318_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_currPos_315_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v___x_323_);
v___x_325_ = v_reuseFailAlloc_327_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
lean_object* v___x_326_; 
v___x_326_ = lean_apply_4(v_recur_282_, v___x_325_, v_acc_280_, lean_box(0), lean_box(0));
return v___x_326_;
}
}
else
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v_slice_331_; lean_object* v_nextIt_333_; 
v___x_328_ = lean_string_utf8_next_fast(v_name_275_, v_searcher_316_);
v___x_329_ = lean_nat_sub(v___x_328_, v_searcher_316_);
v___x_330_ = lean_nat_add(v_searcher_316_, v___x_329_);
lean_dec(v___x_329_);
v_slice_331_ = l_String_Slice_subslice_x21(v___x_278_, v_currPos_315_, v_searcher_316_);
lean_inc(v___x_330_);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 1, v___x_330_);
lean_ctor_set(v___x_318_, 0, v___x_330_);
v_nextIt_333_ = v___x_318_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v___x_330_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v___x_330_);
v_nextIt_333_ = v_reuseFailAlloc_336_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
lean_object* v_startInclusive_334_; lean_object* v_endExclusive_335_; 
v_startInclusive_334_ = lean_ctor_get(v_slice_331_, 0);
lean_inc(v_startInclusive_334_);
v_endExclusive_335_ = lean_ctor_get(v_slice_331_, 1);
lean_inc(v_endExclusive_335_);
lean_dec_ref(v_slice_331_);
v_it_301_ = v_nextIt_333_;
v_startInclusive_302_ = v_startInclusive_334_;
v_endExclusive_303_ = v_endExclusive_335_;
goto v___jp_300_;
}
}
}
else
{
lean_object* v___x_337_; 
lean_del_object(v___x_318_);
lean_dec(v_searcher_316_);
v___x_337_ = lean_box(1);
v_it_301_ = v___x_337_;
v_startInclusive_302_ = v_currPos_315_;
v_endExclusive_303_ = v___x_276_;
goto v___jp_300_;
}
}
}
else
{
lean_dec_ref(v_recur_282_);
lean_dec(v___x_276_);
return v_acc_280_;
}
v___jp_283_:
{
if (lean_obj_tag(v_acc_280_) == 0)
{
lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_286_, 0, v_out_285_);
v___x_287_ = lean_apply_4(v_recur_282_, v_it_284_, v___x_286_, lean_box(0), lean_box(0));
return v___x_287_;
}
else
{
lean_object* v_val_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_299_; 
v_val_288_ = lean_ctor_get(v_acc_280_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v_acc_280_);
if (v_isSharedCheck_299_ == 0)
{
v___x_290_ = v_acc_280_;
v_isShared_291_ = v_isSharedCheck_299_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_val_288_);
lean_dec(v_acc_280_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_299_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_296_; 
v___x_292_ = lean_string_utf8_extract_fast(v___x_272_, v___x_273_, v___x_274_);
v___x_293_ = lean_string_append(v_val_288_, v___x_292_);
lean_dec_ref(v___x_292_);
v___x_294_ = lean_string_append(v___x_293_, v_out_285_);
lean_dec_ref(v_out_285_);
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 0, v___x_294_);
v___x_296_ = v___x_290_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v___x_294_);
v___x_296_ = v_reuseFailAlloc_298_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
lean_object* v___x_297_; 
v___x_297_ = lean_apply_4(v_recur_282_, v_it_284_, v___x_296_, lean_box(0), lean_box(0));
return v___x_297_;
}
}
}
}
v___jp_300_:
{
lean_object* v___x_304_; uint32_t v___x_305_; uint32_t v___x_306_; uint8_t v___x_307_; 
v___x_304_ = lean_string_utf8_extract_fast(v_name_275_, v_startInclusive_302_, v_endExclusive_303_);
lean_dec(v_endExclusive_303_);
lean_dec(v_startInclusive_302_);
v___x_305_ = lean_string_utf8_get(v___x_304_, v___x_273_);
v___x_306_ = 97;
v___x_307_ = lean_uint32_dec_le(v___x_306_, v___x_305_);
if (v___x_307_ == 0)
{
lean_object* v___x_308_; 
v___x_308_ = lean_string_utf8_set(v___x_304_, v___x_273_, v___x_305_);
v_it_284_ = v_it_301_;
v_out_285_ = v___x_308_;
goto v___jp_283_;
}
else
{
uint32_t v___x_309_; uint8_t v___x_310_; 
v___x_309_ = 122;
v___x_310_ = lean_uint32_dec_le(v___x_305_, v___x_309_);
if (v___x_310_ == 0)
{
lean_object* v___x_311_; 
v___x_311_ = lean_string_utf8_set(v___x_304_, v___x_273_, v___x_305_);
v_it_284_ = v_it_301_;
v_out_285_ = v___x_311_;
goto v___jp_283_;
}
else
{
uint32_t v___x_312_; uint32_t v___x_313_; lean_object* v___x_314_; 
v___x_312_ = 4294967264;
v___x_313_ = lean_uint32_add(v___x_305_, v___x_312_);
v___x_314_ = lean_string_utf8_set(v___x_304_, v___x_273_, v___x_313_);
v_it_284_ = v_it_301_;
v_out_285_ = v___x_314_;
goto v___jp_283_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instEncodeV11Head___lam__0___boxed(lean_object* v___x_339_, lean_object* v___x_340_, lean_object* v___x_341_, lean_object* v_name_342_, lean_object* v___x_343_, lean_object* v___x_344_, lean_object* v___x_345_, lean_object* v_it_346_, lean_object* v_acc_347_, lean_object* v_hP_348_, lean_object* v_recur_349_){
_start:
{
uint32_t v___x_1212__boxed_350_; lean_object* v_res_351_; 
v___x_1212__boxed_350_ = lean_unbox_uint32(v___x_344_);
lean_dec(v___x_344_);
v_res_351_ = l_Std_Http_Response_instEncodeV11Head___lam__0(v___x_339_, v___x_340_, v___x_341_, v_name_342_, v___x_343_, v___x_1212__boxed_350_, v___x_345_, v_it_346_, v_acc_347_, v_hP_348_, v_recur_349_);
lean_dec_ref(v___x_345_);
lean_dec_ref(v_name_342_);
lean_dec(v___x_341_);
lean_dec(v___x_340_);
lean_dec_ref(v___x_339_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instEncodeV11Head___lam__1(lean_object* v_buf_352_, lean_object* v_name_353_, lean_object* v_value_354_){
_start:
{
lean_object* v___y_356_; lean_object* v___f_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v_it_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___f_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v___f_375_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__1___closed__1));
v___x_376_ = lean_unsigned_to_nat(0u);
v___x_377_ = lean_string_utf8_byte_size(v_name_353_);
lean_inc_ref(v_name_353_);
v___x_378_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_378_, 0, v_name_353_);
lean_ctor_set(v___x_378_, 1, v___x_376_);
lean_ctor_set(v___x_378_, 2, v___x_377_);
lean_inc_ref(v___x_378_);
v_it_379_ = l_String_Slice_splitToSubslice___redArg(v___x_378_, v___f_375_);
v___x_380_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__1___closed__2));
v___x_381_ = lean_unsigned_to_nat(1u);
v___x_382_ = l_Std_Http_Response_instToStringHead___lam__1___boxed__const__1;
v___f_383_ = lean_alloc_closure((void*)(l_Std_Http_Response_instEncodeV11Head___lam__0___boxed), 11, 7);
lean_closure_set(v___f_383_, 0, v___x_380_);
lean_closure_set(v___f_383_, 1, v___x_376_);
lean_closure_set(v___f_383_, 2, v___x_381_);
lean_closure_set(v___f_383_, 3, v_name_353_);
lean_closure_set(v___f_383_, 4, v___x_377_);
lean_closure_set(v___f_383_, 5, v___x_382_);
lean_closure_set(v___f_383_, 6, v___x_378_);
v___x_384_ = lean_box(0);
v___x_385_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_383_, v_it_379_, v___x_384_, lean_box(0));
if (lean_obj_tag(v___x_385_) == 0)
{
lean_object* v___x_386_; 
v___x_386_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__1___closed__3));
v___y_356_ = v___x_386_;
goto v___jp_355_;
}
else
{
lean_object* v_val_387_; 
v_val_387_ = lean_ctor_get(v___x_385_, 0);
lean_inc(v_val_387_);
lean_dec_ref_known(v___x_385_, 1);
v___y_356_ = v_val_387_;
goto v___jp_355_;
}
v___jp_355_:
{
lean_object* v_data_357_; lean_object* v_size_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_374_; 
v_data_357_ = lean_ctor_get(v_buf_352_, 0);
v_size_358_ = lean_ctor_get(v_buf_352_, 1);
v_isSharedCheck_374_ = !lean_is_exclusive(v_buf_352_);
if (v_isSharedCheck_374_ == 0)
{
v___x_360_ = v_buf_352_;
v_isShared_361_ = v_isSharedCheck_374_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_size_358_);
lean_inc(v_data_357_);
lean_dec(v_buf_352_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_374_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_372_; 
v___x_362_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__1___closed__0));
v___x_363_ = lean_string_append(v___y_356_, v___x_362_);
v___x_364_ = lean_string_append(v___x_363_, v_value_354_);
v___x_365_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__1));
v___x_366_ = lean_string_append(v___x_364_, v___x_365_);
v___x_367_ = lean_string_to_utf8(v___x_366_);
lean_dec_ref(v___x_366_);
lean_inc_ref(v___x_367_);
v___x_368_ = lean_array_push(v_data_357_, v___x_367_);
v___x_369_ = lean_byte_array_size(v___x_367_);
lean_dec_ref(v___x_367_);
v___x_370_ = lean_nat_add(v_size_358_, v___x_369_);
lean_dec(v_size_358_);
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 1, v___x_370_);
lean_ctor_set(v___x_360_, 0, v___x_368_);
v___x_372_ = v___x_360_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v___x_368_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v___x_370_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instEncodeV11Head___lam__1___boxed(lean_object* v_buf_388_, lean_object* v_name_389_, lean_object* v_value_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_Std_Http_Response_instEncodeV11Head___lam__1(v_buf_388_, v_name_389_, v_value_390_);
lean_dec_ref(v_value_390_);
return v_res_391_;
}
}
static lean_object* _init_l_Std_Http_Response_instEncodeV11Head___lam__2___closed__1(void){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_398_ = ((lean_object*)(l_Std_Http_Response_instEncodeV11Head___lam__2___closed__0));
v___x_399_ = lean_byte_array_size(v___x_398_);
return v___x_399_;
}
}
static lean_object* _init_l_Std_Http_Response_instEncodeV11Head___lam__2___closed__2(void){
_start:
{
lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_400_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__1));
v___x_401_ = lean_string_to_utf8(v___x_400_);
return v___x_401_;
}
}
static lean_object* _init_l_Std_Http_Response_instEncodeV11Head___lam__2___closed__3(void){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_402_ = lean_obj_once(&l_Std_Http_Response_instEncodeV11Head___lam__2___closed__2, &l_Std_Http_Response_instEncodeV11Head___lam__2___closed__2_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__2___closed__2);
v___x_403_ = lean_byte_array_size(v___x_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instEncodeV11Head___lam__2(lean_object* v___f_404_, lean_object* v_buffer_405_, lean_object* v_r_406_){
_start:
{
lean_object* v_status_407_; uint8_t v_version_408_; lean_object* v_headers_409_; lean_object* v___y_411_; 
v_status_407_ = lean_ctor_get(v_r_406_, 0);
v_version_408_ = lean_ctor_get_uint8(v_r_406_, sizeof(void*)*2);
v_headers_409_ = lean_ctor_get(v_r_406_, 1);
switch(v_version_408_)
{
case 0:
{
lean_object* v___x_459_; 
v___x_459_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__12));
v___y_411_ = v___x_459_;
goto v___jp_410_;
}
case 1:
{
lean_object* v___x_460_; 
v___x_460_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__13));
v___y_411_ = v___x_460_;
goto v___jp_410_;
}
case 2:
{
lean_object* v___x_461_; 
v___x_461_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__14));
v___y_411_ = v___x_461_;
goto v___jp_410_;
}
default: 
{
lean_object* v___x_462_; 
v___x_462_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__15));
v___y_411_ = v___x_462_;
goto v___jp_410_;
}
}
v___jp_410_:
{
lean_object* v_data_412_; lean_object* v_size_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_458_; 
v_data_412_ = lean_ctor_get(v_buffer_405_, 0);
v_size_413_ = lean_ctor_get(v_buffer_405_, 1);
v_isSharedCheck_458_ = !lean_is_exclusive(v_buffer_405_);
if (v_isSharedCheck_458_ == 0)
{
v___x_415_ = v_buffer_405_;
v_isShared_416_ = v_isSharedCheck_458_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_size_413_);
lean_inc(v_data_412_);
lean_dec(v_buffer_405_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_458_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; uint16_t v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v_buffer_444_; 
v___x_417_ = lean_string_to_utf8(v___y_411_);
lean_inc_ref(v___x_417_);
v___x_418_ = lean_array_push(v_data_412_, v___x_417_);
v___x_419_ = lean_byte_array_size(v___x_417_);
lean_dec_ref(v___x_417_);
v___x_420_ = lean_nat_add(v_size_413_, v___x_419_);
lean_dec(v_size_413_);
v___x_421_ = ((lean_object*)(l_Std_Http_Response_instEncodeV11Head___lam__2___closed__0));
v___x_422_ = lean_array_push(v___x_418_, v___x_421_);
v___x_423_ = lean_obj_once(&l_Std_Http_Response_instEncodeV11Head___lam__2___closed__1, &l_Std_Http_Response_instEncodeV11Head___lam__2___closed__1_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__2___closed__1);
v___x_424_ = lean_nat_add(v___x_420_, v___x_423_);
lean_dec(v___x_420_);
v___x_425_ = l_Std_Http_Status_toCode(v_status_407_);
v___x_426_ = lean_uint16_to_nat(v___x_425_);
v___x_427_ = l_Nat_reprFast(v___x_426_);
v___x_428_ = lean_string_to_utf8(v___x_427_);
lean_dec_ref(v___x_427_);
lean_inc_ref(v___x_428_);
v___x_429_ = lean_array_push(v___x_422_, v___x_428_);
v___x_430_ = lean_byte_array_size(v___x_428_);
lean_dec_ref(v___x_428_);
v___x_431_ = lean_nat_add(v___x_424_, v___x_430_);
lean_dec(v___x_424_);
v___x_432_ = lean_array_push(v___x_429_, v___x_421_);
v___x_433_ = lean_nat_add(v___x_431_, v___x_423_);
lean_dec(v___x_431_);
v___x_434_ = l_Std_Http_Status_reasonPhrase(v_status_407_);
v___x_435_ = lean_string_to_utf8(v___x_434_);
lean_dec_ref(v___x_434_);
lean_inc_ref(v___x_435_);
v___x_436_ = lean_array_push(v___x_432_, v___x_435_);
v___x_437_ = lean_byte_array_size(v___x_435_);
lean_dec_ref(v___x_435_);
v___x_438_ = lean_nat_add(v___x_433_, v___x_437_);
lean_dec(v___x_433_);
v___x_439_ = lean_obj_once(&l_Std_Http_Response_instEncodeV11Head___lam__2___closed__2, &l_Std_Http_Response_instEncodeV11Head___lam__2___closed__2_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__2___closed__2);
v___x_440_ = lean_array_push(v___x_436_, v___x_439_);
v___x_441_ = lean_obj_once(&l_Std_Http_Response_instEncodeV11Head___lam__2___closed__3, &l_Std_Http_Response_instEncodeV11Head___lam__2___closed__3_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__2___closed__3);
v___x_442_ = lean_nat_add(v___x_438_, v___x_441_);
lean_dec(v___x_438_);
if (v_isShared_416_ == 0)
{
lean_ctor_set(v___x_415_, 1, v___x_442_);
lean_ctor_set(v___x_415_, 0, v___x_440_);
v_buffer_444_ = v___x_415_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v___x_440_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v___x_442_);
v_buffer_444_ = v_reuseFailAlloc_457_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
lean_object* v_buffer_445_; lean_object* v_data_446_; lean_object* v_size_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_456_; 
v_buffer_445_ = l_Std_Http_Headers_fold___redArg(v_headers_409_, v_buffer_444_, v___f_404_);
v_data_446_ = lean_ctor_get(v_buffer_445_, 0);
v_size_447_ = lean_ctor_get(v_buffer_445_, 1);
v_isSharedCheck_456_ = !lean_is_exclusive(v_buffer_445_);
if (v_isSharedCheck_456_ == 0)
{
v___x_449_ = v_buffer_445_;
v_isShared_450_ = v_isSharedCheck_456_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_size_447_);
lean_inc(v_data_446_);
lean_dec(v_buffer_445_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_456_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_454_; 
v___x_451_ = lean_array_push(v_data_446_, v___x_439_);
v___x_452_ = lean_nat_add(v_size_447_, v___x_441_);
lean_dec(v_size_447_);
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 1, v___x_452_);
lean_ctor_set(v___x_449_, 0, v___x_451_);
v___x_454_ = v___x_449_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v___x_451_);
lean_ctor_set(v_reuseFailAlloc_455_, 1, v___x_452_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instEncodeV11Head___lam__2___boxed(lean_object* v___f_463_, lean_object* v_buffer_464_, lean_object* v_r_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Std_Http_Response_instEncodeV11Head___lam__2(v___f_463_, v_buffer_464_, v_r_465_);
lean_dec_ref(v_r_465_);
return v_res_466_;
}
}
static lean_object* _init_l_Std_Http_Response_new___closed__0(void){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_471_ = l_Std_Http_Extensions_empty;
v___x_472_ = lean_obj_once(&l_Std_Http_Response_instInhabitedHead_default___closed__0, &l_Std_Http_Response_instInhabitedHead_default___closed__0_once, _init_l_Std_Http_Response_instInhabitedHead_default___closed__0);
v___x_473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_473_, 0, v___x_472_);
lean_ctor_set(v___x_473_, 1, v___x_471_);
return v___x_473_;
}
}
static lean_object* _init_l_Std_Http_Response_new(void){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = lean_obj_once(&l_Std_Http_Response_new___closed__0, &l_Std_Http_Response_new___closed__0_once, _init_l_Std_Http_Response_new___closed__0);
return v___x_474_;
}
}
static lean_object* _init_l_Std_Http_Response_Builder_new(void){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = lean_obj_once(&l_Std_Http_Response_new___closed__0, &l_Std_Http_Response_new___closed__0_once, _init_l_Std_Http_Response_new___closed__0);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_status(lean_object* v_builder_476_, lean_object* v_status_477_){
_start:
{
lean_object* v_line_478_; lean_object* v_extensions_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_496_; 
v_line_478_ = lean_ctor_get(v_builder_476_, 0);
v_extensions_479_ = lean_ctor_get(v_builder_476_, 1);
v_isSharedCheck_496_ = !lean_is_exclusive(v_builder_476_);
if (v_isSharedCheck_496_ == 0)
{
v___x_481_ = v_builder_476_;
v_isShared_482_ = v_isSharedCheck_496_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_extensions_479_);
lean_inc(v_line_478_);
lean_dec(v_builder_476_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_496_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
uint8_t v_version_483_; lean_object* v_headers_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_494_; 
v_version_483_ = lean_ctor_get_uint8(v_line_478_, sizeof(void*)*2);
v_headers_484_ = lean_ctor_get(v_line_478_, 1);
v_isSharedCheck_494_ = !lean_is_exclusive(v_line_478_);
if (v_isSharedCheck_494_ == 0)
{
lean_object* v_unused_495_; 
v_unused_495_ = lean_ctor_get(v_line_478_, 0);
lean_dec(v_unused_495_);
v___x_486_ = v_line_478_;
v_isShared_487_ = v_isSharedCheck_494_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_headers_484_);
lean_dec(v_line_478_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_494_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_489_; 
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 0, v_status_477_);
v___x_489_ = v___x_486_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_status_477_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v_headers_484_);
lean_ctor_set_uint8(v_reuseFailAlloc_493_, sizeof(void*)*2, v_version_483_);
v___x_489_ = v_reuseFailAlloc_493_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
lean_object* v___x_491_; 
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 0, v___x_489_);
v___x_491_ = v___x_481_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v___x_489_);
lean_ctor_set(v_reuseFailAlloc_492_, 1, v_extensions_479_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_headers(lean_object* v_builder_497_, lean_object* v_headers_498_){
_start:
{
lean_object* v_line_499_; lean_object* v_extensions_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_517_; 
v_line_499_ = lean_ctor_get(v_builder_497_, 0);
v_extensions_500_ = lean_ctor_get(v_builder_497_, 1);
v_isSharedCheck_517_ = !lean_is_exclusive(v_builder_497_);
if (v_isSharedCheck_517_ == 0)
{
v___x_502_ = v_builder_497_;
v_isShared_503_ = v_isSharedCheck_517_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_extensions_500_);
lean_inc(v_line_499_);
lean_dec(v_builder_497_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_517_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v_status_504_; uint8_t v_version_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_515_; 
v_status_504_ = lean_ctor_get(v_line_499_, 0);
v_version_505_ = lean_ctor_get_uint8(v_line_499_, sizeof(void*)*2);
v_isSharedCheck_515_ = !lean_is_exclusive(v_line_499_);
if (v_isSharedCheck_515_ == 0)
{
lean_object* v_unused_516_; 
v_unused_516_ = lean_ctor_get(v_line_499_, 1);
lean_dec(v_unused_516_);
v___x_507_ = v_line_499_;
v_isShared_508_ = v_isSharedCheck_515_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_status_504_);
lean_dec(v_line_499_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_515_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_510_; 
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 1, v_headers_498_);
v___x_510_ = v___x_507_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_status_504_);
lean_ctor_set(v_reuseFailAlloc_514_, 1, v_headers_498_);
lean_ctor_set_uint8(v_reuseFailAlloc_514_, sizeof(void*)*2, v_version_505_);
v___x_510_ = v_reuseFailAlloc_514_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
lean_object* v___x_512_; 
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 0, v___x_510_);
v___x_512_ = v___x_502_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v___x_510_);
lean_ctor_set(v_reuseFailAlloc_513_, 1, v_extensions_500_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0___redArg(lean_object* v_a_518_, lean_object* v_x_519_){
_start:
{
if (lean_obj_tag(v_x_519_) == 0)
{
uint8_t v___x_520_; 
v___x_520_ = 0;
return v___x_520_;
}
else
{
lean_object* v_key_521_; lean_object* v_tail_522_; uint8_t v___x_523_; 
v_key_521_ = lean_ctor_get(v_x_519_, 0);
v_tail_522_ = lean_ctor_get(v_x_519_, 2);
v___x_523_ = lean_string_dec_eq(v_key_521_, v_a_518_);
if (v___x_523_ == 0)
{
v_x_519_ = v_tail_522_;
goto _start;
}
else
{
return v___x_523_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0___redArg___boxed(lean_object* v_a_525_, lean_object* v_x_526_){
_start:
{
uint8_t v_res_527_; lean_object* v_r_528_; 
v_res_527_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0___redArg(v_a_525_, v_x_526_);
lean_dec(v_x_526_);
lean_dec_ref(v_a_525_);
v_r_528_ = lean_box(v_res_527_);
return v_r_528_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_529_, lean_object* v_x_530_){
_start:
{
if (lean_obj_tag(v_x_530_) == 0)
{
return v_x_529_;
}
else
{
lean_object* v_key_531_; lean_object* v_value_532_; lean_object* v_tail_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_556_; 
v_key_531_ = lean_ctor_get(v_x_530_, 0);
v_value_532_ = lean_ctor_get(v_x_530_, 1);
v_tail_533_ = lean_ctor_get(v_x_530_, 2);
v_isSharedCheck_556_ = !lean_is_exclusive(v_x_530_);
if (v_isSharedCheck_556_ == 0)
{
v___x_535_ = v_x_530_;
v_isShared_536_ = v_isSharedCheck_556_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_tail_533_);
lean_inc(v_value_532_);
lean_inc(v_key_531_);
lean_dec(v_x_530_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_556_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_537_; uint64_t v___x_538_; uint64_t v___x_539_; uint64_t v___x_540_; uint64_t v_fold_541_; uint64_t v___x_542_; uint64_t v___x_543_; uint64_t v___x_544_; size_t v___x_545_; size_t v___x_546_; size_t v___x_547_; size_t v___x_548_; size_t v___x_549_; lean_object* v___x_550_; lean_object* v___x_552_; 
v___x_537_ = lean_array_get_size(v_x_529_);
v___x_538_ = lean_string_hash(v_key_531_);
v___x_539_ = 32ULL;
v___x_540_ = lean_uint64_shift_right(v___x_538_, v___x_539_);
v_fold_541_ = lean_uint64_xor(v___x_538_, v___x_540_);
v___x_542_ = 16ULL;
v___x_543_ = lean_uint64_shift_right(v_fold_541_, v___x_542_);
v___x_544_ = lean_uint64_xor(v_fold_541_, v___x_543_);
v___x_545_ = lean_uint64_to_usize(v___x_544_);
v___x_546_ = lean_usize_of_nat(v___x_537_);
v___x_547_ = ((size_t)1ULL);
v___x_548_ = lean_usize_sub(v___x_546_, v___x_547_);
v___x_549_ = lean_usize_land(v___x_545_, v___x_548_);
v___x_550_ = lean_array_uget_borrowed(v_x_529_, v___x_549_);
lean_inc(v___x_550_);
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 2, v___x_550_);
v___x_552_ = v___x_535_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_key_531_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v_value_532_);
lean_ctor_set(v_reuseFailAlloc_555_, 2, v___x_550_);
v___x_552_ = v_reuseFailAlloc_555_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
lean_object* v___x_553_; 
v___x_553_ = lean_array_uset(v_x_529_, v___x_549_, v___x_552_);
v_x_529_ = v___x_553_;
v_x_530_ = v_tail_533_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2___redArg(lean_object* v_i_557_, lean_object* v_source_558_, lean_object* v_target_559_){
_start:
{
lean_object* v___x_560_; uint8_t v___x_561_; 
v___x_560_ = lean_array_get_size(v_source_558_);
v___x_561_ = lean_nat_dec_lt(v_i_557_, v___x_560_);
if (v___x_561_ == 0)
{
lean_dec_ref(v_source_558_);
lean_dec(v_i_557_);
return v_target_559_;
}
else
{
lean_object* v_es_562_; lean_object* v___x_563_; lean_object* v_source_564_; lean_object* v_target_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v_es_562_ = lean_array_fget(v_source_558_, v_i_557_);
v___x_563_ = lean_box(0);
v_source_564_ = lean_array_fset(v_source_558_, v_i_557_, v___x_563_);
v_target_565_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2_spec__3___redArg(v_target_559_, v_es_562_);
v___x_566_ = lean_unsigned_to_nat(1u);
v___x_567_ = lean_nat_add(v_i_557_, v___x_566_);
lean_dec(v_i_557_);
v_i_557_ = v___x_567_;
v_source_558_ = v_source_564_;
v_target_559_ = v_target_565_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1___redArg(lean_object* v_data_569_){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v_nbuckets_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_570_ = lean_array_get_size(v_data_569_);
v___x_571_ = lean_unsigned_to_nat(2u);
v_nbuckets_572_ = lean_nat_mul(v___x_570_, v___x_571_);
v___x_573_ = lean_unsigned_to_nat(0u);
v___x_574_ = lean_box(0);
v___x_575_ = lean_mk_array(v_nbuckets_572_, v___x_574_);
v___x_576_ = lean_array_propagate_mark(v_data_569_, v___x_575_);
v___x_577_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2___redArg(v___x_573_, v_data_569_, v___x_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__2___lam__0(lean_object* v_i_578_, lean_object* v_x_579_){
_start:
{
if (lean_obj_tag(v_x_579_) == 0)
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_580_ = lean_unsigned_to_nat(1u);
v___x_581_ = lean_mk_empty_array_with_capacity(v___x_580_);
v___x_582_ = lean_array_push(v___x_581_, v_i_578_);
v___x_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_583_, 0, v___x_582_);
return v___x_583_;
}
else
{
lean_object* v_val_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_592_; 
v_val_584_ = lean_ctor_get(v_x_579_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v_x_579_);
if (v_isSharedCheck_592_ == 0)
{
v___x_586_ = v_x_579_;
v_isShared_587_ = v_isSharedCheck_592_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_val_584_);
lean_dec(v_x_579_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_592_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_588_; lean_object* v___x_590_; 
v___x_588_ = lean_array_push(v_val_584_, v_i_578_);
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 0, v___x_588_);
v___x_590_ = v___x_586_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v___x_588_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__2(lean_object* v_i_593_, lean_object* v_a_594_, lean_object* v_x_595_){
_start:
{
if (lean_obj_tag(v_x_595_) == 0)
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v_val_598_; lean_object* v___x_599_; 
v___x_596_ = lean_box(0);
v___x_597_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__2___lam__0(v_i_593_, v___x_596_);
v_val_598_ = lean_ctor_get(v___x_597_, 0);
lean_inc(v_val_598_);
lean_dec(v___x_597_);
v___x_599_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_599_, 0, v_a_594_);
lean_ctor_set(v___x_599_, 1, v_val_598_);
lean_ctor_set(v___x_599_, 2, v_x_595_);
return v___x_599_;
}
else
{
lean_object* v_key_600_; lean_object* v_value_601_; lean_object* v_tail_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_617_; 
v_key_600_ = lean_ctor_get(v_x_595_, 0);
v_value_601_ = lean_ctor_get(v_x_595_, 1);
v_tail_602_ = lean_ctor_get(v_x_595_, 2);
v_isSharedCheck_617_ = !lean_is_exclusive(v_x_595_);
if (v_isSharedCheck_617_ == 0)
{
v___x_604_ = v_x_595_;
v_isShared_605_ = v_isSharedCheck_617_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_tail_602_);
lean_inc(v_value_601_);
lean_inc(v_key_600_);
lean_dec(v_x_595_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_617_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
uint8_t v___x_606_; 
v___x_606_ = lean_string_dec_eq(v_key_600_, v_a_594_);
if (v___x_606_ == 0)
{
lean_object* v_tail_607_; lean_object* v___x_609_; 
v_tail_607_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__2(v_i_593_, v_a_594_, v_tail_602_);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 2, v_tail_607_);
v___x_609_ = v___x_604_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_key_600_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v_value_601_);
lean_ctor_set(v_reuseFailAlloc_610_, 2, v_tail_607_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
else
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v_val_613_; lean_object* v___x_615_; 
lean_dec(v_key_600_);
v___x_611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_611_, 0, v_value_601_);
v___x_612_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__2___lam__0(v_i_593_, v___x_611_);
v_val_613_ = lean_ctor_get(v___x_612_, 0);
lean_inc(v_val_613_);
lean_dec(v___x_612_);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 1, v_val_613_);
lean_ctor_set(v___x_604_, 0, v_a_594_);
v___x_615_ = v___x_604_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_a_594_);
lean_ctor_set(v_reuseFailAlloc_616_, 1, v_val_613_);
lean_ctor_set(v_reuseFailAlloc_616_, 2, v_tail_602_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0(lean_object* v_i_618_, lean_object* v_m_619_, lean_object* v_a_620_){
_start:
{
lean_object* v_size_621_; lean_object* v_buckets_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_672_; 
v_size_621_ = lean_ctor_get(v_m_619_, 0);
v_buckets_622_ = lean_ctor_get(v_m_619_, 1);
v_isSharedCheck_672_ = !lean_is_exclusive(v_m_619_);
if (v_isSharedCheck_672_ == 0)
{
v___x_624_ = v_m_619_;
v_isShared_625_ = v_isSharedCheck_672_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_buckets_622_);
lean_inc(v_size_621_);
lean_dec(v_m_619_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_672_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_626_; uint64_t v___x_627_; uint64_t v___x_628_; uint64_t v___x_629_; uint64_t v_fold_630_; uint64_t v___x_631_; uint64_t v___x_632_; uint64_t v___x_633_; size_t v___x_634_; size_t v___x_635_; size_t v___x_636_; size_t v___x_637_; size_t v___x_638_; lean_object* v_bkt_639_; uint8_t v___x_640_; 
v___x_626_ = lean_array_get_size(v_buckets_622_);
v___x_627_ = lean_string_hash(v_a_620_);
v___x_628_ = 32ULL;
v___x_629_ = lean_uint64_shift_right(v___x_627_, v___x_628_);
v_fold_630_ = lean_uint64_xor(v___x_627_, v___x_629_);
v___x_631_ = 16ULL;
v___x_632_ = lean_uint64_shift_right(v_fold_630_, v___x_631_);
v___x_633_ = lean_uint64_xor(v_fold_630_, v___x_632_);
v___x_634_ = lean_uint64_to_usize(v___x_633_);
v___x_635_ = lean_usize_of_nat(v___x_626_);
v___x_636_ = ((size_t)1ULL);
v___x_637_ = lean_usize_sub(v___x_635_, v___x_636_);
v___x_638_ = lean_usize_land(v___x_634_, v___x_637_);
v_bkt_639_ = lean_array_uget_borrowed(v_buckets_622_, v___x_638_);
v___x_640_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0___redArg(v_a_620_, v_bkt_639_);
if (v___x_640_ == 0)
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v_size_x27_644_; lean_object* v___x_645_; lean_object* v_buckets_x27_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; uint8_t v___x_652_; 
v___x_641_ = lean_unsigned_to_nat(1u);
v___x_642_ = lean_mk_empty_array_with_capacity(v___x_641_);
v___x_643_ = lean_array_push(v___x_642_, v_i_618_);
v_size_x27_644_ = lean_nat_add(v_size_621_, v___x_641_);
lean_dec(v_size_621_);
lean_inc(v_bkt_639_);
v___x_645_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_645_, 0, v_a_620_);
lean_ctor_set(v___x_645_, 1, v___x_643_);
lean_ctor_set(v___x_645_, 2, v_bkt_639_);
v_buckets_x27_646_ = lean_array_uset(v_buckets_622_, v___x_638_, v___x_645_);
v___x_647_ = lean_unsigned_to_nat(4u);
v___x_648_ = lean_nat_mul(v_size_x27_644_, v___x_647_);
v___x_649_ = lean_unsigned_to_nat(3u);
v___x_650_ = lean_nat_div(v___x_648_, v___x_649_);
lean_dec(v___x_648_);
v___x_651_ = lean_array_get_size(v_buckets_x27_646_);
v___x_652_ = lean_nat_dec_le(v___x_650_, v___x_651_);
lean_dec(v___x_650_);
if (v___x_652_ == 0)
{
lean_object* v_val_653_; lean_object* v___x_655_; 
v_val_653_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1___redArg(v_buckets_x27_646_);
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 1, v_val_653_);
lean_ctor_set(v___x_624_, 0, v_size_x27_644_);
v___x_655_ = v___x_624_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_size_x27_644_);
lean_ctor_set(v_reuseFailAlloc_656_, 1, v_val_653_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
else
{
lean_object* v___x_658_; 
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 1, v_buckets_x27_646_);
lean_ctor_set(v___x_624_, 0, v_size_x27_644_);
v___x_658_ = v___x_624_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_size_x27_644_);
lean_ctor_set(v_reuseFailAlloc_659_, 1, v_buckets_x27_646_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
else
{
lean_object* v___x_660_; lean_object* v_buckets_x27_661_; lean_object* v_bkt_x27_662_; lean_object* v___y_664_; uint8_t v___x_669_; 
lean_inc(v_bkt_639_);
v___x_660_ = lean_box(0);
v_buckets_x27_661_ = lean_array_uset(v_buckets_622_, v___x_638_, v___x_660_);
lean_inc_ref(v_a_620_);
v_bkt_x27_662_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__2(v_i_618_, v_a_620_, v_bkt_639_);
v___x_669_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0___redArg(v_a_620_, v_bkt_x27_662_);
lean_dec_ref(v_a_620_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_670_ = lean_unsigned_to_nat(1u);
v___x_671_ = lean_nat_sub(v_size_621_, v___x_670_);
lean_dec(v_size_621_);
v___y_664_ = v___x_671_;
goto v___jp_663_;
}
else
{
v___y_664_ = v_size_621_;
goto v___jp_663_;
}
v___jp_663_:
{
lean_object* v___x_665_; lean_object* v___x_667_; 
v___x_665_ = lean_array_uset(v_buckets_x27_661_, v___x_638_, v_bkt_x27_662_);
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 1, v___x_665_);
lean_ctor_set(v___x_624_, 0, v___y_664_);
v___x_667_ = v___x_624_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v___y_664_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v___x_665_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_header(lean_object* v_builder_673_, lean_object* v_key_674_, lean_object* v_value_675_){
_start:
{
lean_object* v_line_676_; lean_object* v_headers_677_; lean_object* v_extensions_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_708_; 
v_line_676_ = lean_ctor_get(v_builder_673_, 0);
lean_inc_ref(v_line_676_);
v_headers_677_ = lean_ctor_get(v_line_676_, 1);
lean_inc_ref(v_headers_677_);
v_extensions_678_ = lean_ctor_get(v_builder_673_, 1);
v_isSharedCheck_708_ = !lean_is_exclusive(v_builder_673_);
if (v_isSharedCheck_708_ == 0)
{
lean_object* v_unused_709_; 
v_unused_709_ = lean_ctor_get(v_builder_673_, 0);
lean_dec(v_unused_709_);
v___x_680_ = v_builder_673_;
v_isShared_681_ = v_isSharedCheck_708_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_extensions_678_);
lean_dec(v_builder_673_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_708_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v_status_682_; uint8_t v_version_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_706_; 
v_status_682_ = lean_ctor_get(v_line_676_, 0);
v_version_683_ = lean_ctor_get_uint8(v_line_676_, sizeof(void*)*2);
v_isSharedCheck_706_ = !lean_is_exclusive(v_line_676_);
if (v_isSharedCheck_706_ == 0)
{
lean_object* v_unused_707_; 
v_unused_707_ = lean_ctor_get(v_line_676_, 1);
lean_dec(v_unused_707_);
v___x_685_ = v_line_676_;
v_isShared_686_ = v_isSharedCheck_706_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_status_682_);
lean_dec(v_line_676_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_706_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v_entries_687_; lean_object* v_indexes_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_705_; 
v_entries_687_ = lean_ctor_get(v_headers_677_, 0);
v_indexes_688_ = lean_ctor_get(v_headers_677_, 1);
v_isSharedCheck_705_ = !lean_is_exclusive(v_headers_677_);
if (v_isSharedCheck_705_ == 0)
{
v___x_690_ = v_headers_677_;
v_isShared_691_ = v_isSharedCheck_705_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_indexes_688_);
lean_inc(v_entries_687_);
lean_dec(v_headers_677_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_705_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v_i_692_; lean_object* v___x_693_; lean_object* v_entries_694_; lean_object* v_indexes_695_; lean_object* v___x_697_; 
v_i_692_ = lean_array_get_size(v_entries_687_);
lean_inc_ref(v_key_674_);
v___x_693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_693_, 0, v_key_674_);
lean_ctor_set(v___x_693_, 1, v_value_675_);
v_entries_694_ = lean_array_push(v_entries_687_, v___x_693_);
v_indexes_695_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0(v_i_692_, v_indexes_688_, v_key_674_);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 1, v_indexes_695_);
lean_ctor_set(v___x_690_, 0, v_entries_694_);
v___x_697_ = v___x_690_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_entries_694_);
lean_ctor_set(v_reuseFailAlloc_704_, 1, v_indexes_695_);
v___x_697_ = v_reuseFailAlloc_704_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
lean_object* v___x_699_; 
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 1, v___x_697_);
v___x_699_ = v___x_685_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_status_682_);
lean_ctor_set(v_reuseFailAlloc_703_, 1, v___x_697_);
lean_ctor_set_uint8(v_reuseFailAlloc_703_, sizeof(void*)*2, v_version_683_);
v___x_699_ = v_reuseFailAlloc_703_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
lean_object* v___x_701_; 
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 0, v___x_699_);
v___x_701_ = v___x_680_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v___x_699_);
lean_ctor_set(v_reuseFailAlloc_702_, 1, v_extensions_678_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0(lean_object* v_00_u03b2_710_, lean_object* v_a_711_, lean_object* v_x_712_){
_start:
{
uint8_t v___x_713_; 
v___x_713_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0___redArg(v_a_711_, v_x_712_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0___boxed(lean_object* v_00_u03b2_714_, lean_object* v_a_715_, lean_object* v_x_716_){
_start:
{
uint8_t v_res_717_; lean_object* v_r_718_; 
v_res_717_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0(v_00_u03b2_714_, v_a_715_, v_x_716_);
lean_dec(v_x_716_);
lean_dec_ref(v_a_715_);
v_r_718_ = lean_box(v_res_717_);
return v_r_718_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1(lean_object* v_00_u03b2_719_, lean_object* v_data_720_){
_start:
{
lean_object* v___x_721_; 
v___x_721_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1___redArg(v_data_720_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_722_, lean_object* v_i_723_, lean_object* v_source_724_, lean_object* v_target_725_){
_start:
{
lean_object* v___x_726_; 
v___x_726_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2___redArg(v_i_723_, v_source_724_, v_target_725_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_727_, lean_object* v_x_728_, lean_object* v_x_729_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2_spec__3___redArg(v_x_728_, v_x_729_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_header_x21(lean_object* v_builder_731_, lean_object* v_key_732_, lean_object* v_value_733_){
_start:
{
lean_object* v_line_734_; lean_object* v_headers_735_; lean_object* v_extensions_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_768_; 
v_line_734_ = lean_ctor_get(v_builder_731_, 0);
lean_inc_ref(v_line_734_);
v_headers_735_ = lean_ctor_get(v_line_734_, 1);
lean_inc_ref(v_headers_735_);
v_extensions_736_ = lean_ctor_get(v_builder_731_, 1);
v_isSharedCheck_768_ = !lean_is_exclusive(v_builder_731_);
if (v_isSharedCheck_768_ == 0)
{
lean_object* v_unused_769_; 
v_unused_769_ = lean_ctor_get(v_builder_731_, 0);
lean_dec(v_unused_769_);
v___x_738_ = v_builder_731_;
v_isShared_739_ = v_isSharedCheck_768_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_extensions_736_);
lean_dec(v_builder_731_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_768_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v_status_740_; uint8_t v_version_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_766_; 
v_status_740_ = lean_ctor_get(v_line_734_, 0);
v_version_741_ = lean_ctor_get_uint8(v_line_734_, sizeof(void*)*2);
v_isSharedCheck_766_ = !lean_is_exclusive(v_line_734_);
if (v_isSharedCheck_766_ == 0)
{
lean_object* v_unused_767_; 
v_unused_767_ = lean_ctor_get(v_line_734_, 1);
lean_dec(v_unused_767_);
v___x_743_ = v_line_734_;
v_isShared_744_ = v_isSharedCheck_766_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_status_740_);
lean_dec(v_line_734_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_766_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v_entries_745_; lean_object* v_indexes_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_765_; 
v_entries_745_ = lean_ctor_get(v_headers_735_, 0);
v_indexes_746_ = lean_ctor_get(v_headers_735_, 1);
v_isSharedCheck_765_ = !lean_is_exclusive(v_headers_735_);
if (v_isSharedCheck_765_ == 0)
{
v___x_748_ = v_headers_735_;
v_isShared_749_ = v_isSharedCheck_765_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_indexes_746_);
lean_inc(v_entries_745_);
lean_dec(v_headers_735_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_765_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v_key_750_; lean_object* v_value_751_; lean_object* v_i_752_; lean_object* v___x_753_; lean_object* v_entries_754_; lean_object* v_indexes_755_; lean_object* v___x_757_; 
v_key_750_ = l_Std_Http_Header_Name_ofString_x21(v_key_732_);
v_value_751_ = l_Std_Http_Header_Value_ofString_x21(v_value_733_);
v_i_752_ = lean_array_get_size(v_entries_745_);
lean_inc_ref(v_key_750_);
v___x_753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_753_, 0, v_key_750_);
lean_ctor_set(v___x_753_, 1, v_value_751_);
v_entries_754_ = lean_array_push(v_entries_745_, v___x_753_);
v_indexes_755_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0(v_i_752_, v_indexes_746_, v_key_750_);
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 1, v_indexes_755_);
lean_ctor_set(v___x_748_, 0, v_entries_754_);
v___x_757_ = v___x_748_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_entries_754_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v_indexes_755_);
v___x_757_ = v_reuseFailAlloc_764_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
lean_object* v___x_759_; 
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 1, v___x_757_);
v___x_759_ = v___x_743_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_status_740_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v___x_757_);
lean_ctor_set_uint8(v_reuseFailAlloc_763_, sizeof(void*)*2, v_version_741_);
v___x_759_ = v_reuseFailAlloc_763_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
lean_object* v___x_761_; 
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 0, v___x_759_);
v___x_761_ = v___x_738_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v___x_759_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v_extensions_736_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_header_x3f(lean_object* v_builder_770_, lean_object* v_key_771_, lean_object* v_value_772_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = l_Std_Http_Header_Name_ofString_x3f(v_key_771_);
if (lean_obj_tag(v___x_773_) == 0)
{
lean_object* v___x_774_; 
lean_dec_ref(v_value_772_);
lean_dec_ref(v_builder_770_);
v___x_774_ = lean_box(0);
return v___x_774_;
}
else
{
lean_object* v_val_775_; lean_object* v___x_776_; 
v_val_775_ = lean_ctor_get(v___x_773_, 0);
lean_inc(v_val_775_);
lean_dec_ref_known(v___x_773_, 1);
v___x_776_ = l_Std_Http_Header_Value_ofString_x3f(v_value_772_);
if (lean_obj_tag(v___x_776_) == 0)
{
lean_object* v___x_777_; 
lean_dec(v_val_775_);
lean_dec_ref(v_builder_770_);
v___x_777_ = lean_box(0);
return v___x_777_;
}
else
{
lean_object* v_line_778_; lean_object* v_headers_779_; lean_object* v_val_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_819_; 
v_line_778_ = lean_ctor_get(v_builder_770_, 0);
lean_inc_ref(v_line_778_);
v_headers_779_ = lean_ctor_get(v_line_778_, 1);
lean_inc_ref(v_headers_779_);
v_val_780_ = lean_ctor_get(v___x_776_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_776_);
if (v_isSharedCheck_819_ == 0)
{
v___x_782_ = v___x_776_;
v_isShared_783_ = v_isSharedCheck_819_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_val_780_);
lean_dec(v___x_776_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_819_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v_extensions_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_817_; 
v_extensions_784_ = lean_ctor_get(v_builder_770_, 1);
v_isSharedCheck_817_ = !lean_is_exclusive(v_builder_770_);
if (v_isSharedCheck_817_ == 0)
{
lean_object* v_unused_818_; 
v_unused_818_ = lean_ctor_get(v_builder_770_, 0);
lean_dec(v_unused_818_);
v___x_786_ = v_builder_770_;
v_isShared_787_ = v_isSharedCheck_817_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_extensions_784_);
lean_dec(v_builder_770_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_817_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v_status_788_; uint8_t v_version_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_815_; 
v_status_788_ = lean_ctor_get(v_line_778_, 0);
v_version_789_ = lean_ctor_get_uint8(v_line_778_, sizeof(void*)*2);
v_isSharedCheck_815_ = !lean_is_exclusive(v_line_778_);
if (v_isSharedCheck_815_ == 0)
{
lean_object* v_unused_816_; 
v_unused_816_ = lean_ctor_get(v_line_778_, 1);
lean_dec(v_unused_816_);
v___x_791_ = v_line_778_;
v_isShared_792_ = v_isSharedCheck_815_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_status_788_);
lean_dec(v_line_778_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_815_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v_entries_793_; lean_object* v_indexes_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_814_; 
v_entries_793_ = lean_ctor_get(v_headers_779_, 0);
v_indexes_794_ = lean_ctor_get(v_headers_779_, 1);
v_isSharedCheck_814_ = !lean_is_exclusive(v_headers_779_);
if (v_isSharedCheck_814_ == 0)
{
v___x_796_ = v_headers_779_;
v_isShared_797_ = v_isSharedCheck_814_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_indexes_794_);
lean_inc(v_entries_793_);
lean_dec(v_headers_779_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_814_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v_i_798_; lean_object* v___x_799_; lean_object* v_entries_800_; lean_object* v_indexes_801_; lean_object* v___x_803_; 
v_i_798_ = lean_array_get_size(v_entries_793_);
lean_inc(v_val_775_);
v___x_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_799_, 0, v_val_775_);
lean_ctor_set(v___x_799_, 1, v_val_780_);
v_entries_800_ = lean_array_push(v_entries_793_, v___x_799_);
v_indexes_801_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0(v_i_798_, v_indexes_794_, v_val_775_);
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 1, v_indexes_801_);
lean_ctor_set(v___x_796_, 0, v_entries_800_);
v___x_803_ = v___x_796_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_entries_800_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v_indexes_801_);
v___x_803_ = v_reuseFailAlloc_813_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
lean_object* v___x_805_; 
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 1, v___x_803_);
v___x_805_ = v___x_791_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_status_788_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v___x_803_);
lean_ctor_set_uint8(v_reuseFailAlloc_812_, sizeof(void*)*2, v_version_789_);
v___x_805_ = v_reuseFailAlloc_812_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
lean_object* v___x_807_; 
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 0, v___x_805_);
v___x_807_ = v___x_786_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v___x_805_);
lean_ctor_set(v_reuseFailAlloc_811_, 1, v_extensions_784_);
v___x_807_ = v_reuseFailAlloc_811_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
lean_object* v___x_809_; 
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 0, v___x_807_);
v___x_809_ = v___x_782_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v___x_807_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
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
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_extension___redArg(lean_object* v_builder_821_, lean_object* v_inst_822_, lean_object* v_data_823_){
_start:
{
lean_object* v_line_824_; lean_object* v_extensions_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_836_; 
v_line_824_ = lean_ctor_get(v_builder_821_, 0);
v_extensions_825_ = lean_ctor_get(v_builder_821_, 1);
v_isSharedCheck_836_ = !lean_is_exclusive(v_builder_821_);
if (v_isSharedCheck_836_ == 0)
{
v___x_827_ = v_builder_821_;
v_isShared_828_ = v_isSharedCheck_836_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_extensions_825_);
lean_inc(v_line_824_);
lean_dec(v_builder_821_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_836_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v_dyn_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_834_; 
v_dyn_829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_dyn_829_, 0, v_inst_822_);
lean_ctor_set(v_dyn_829_, 1, v_data_823_);
v___x_830_ = ((lean_object*)(l_Std_Http_Response_Builder_extension___redArg___closed__0));
v___x_831_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_dyn_829_);
v___x_832_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_830_, v___x_831_, v_dyn_829_, v_extensions_825_);
if (v_isShared_828_ == 0)
{
lean_ctor_set(v___x_827_, 1, v___x_832_);
v___x_834_ = v___x_827_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_line_824_);
lean_ctor_set(v_reuseFailAlloc_835_, 1, v___x_832_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_extension(lean_object* v_00_u03b1_837_, lean_object* v_builder_838_, lean_object* v_inst_839_, lean_object* v_data_840_){
_start:
{
lean_object* v___x_841_; 
v___x_841_ = l_Std_Http_Response_Builder_extension___redArg(v_builder_838_, v_inst_839_, v_data_840_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_body___redArg(lean_object* v_builder_842_, lean_object* v_body_843_){
_start:
{
lean_object* v_line_844_; lean_object* v_extensions_845_; lean_object* v___x_846_; 
v_line_844_ = lean_ctor_get(v_builder_842_, 0);
v_extensions_845_ = lean_ctor_get(v_builder_842_, 1);
lean_inc(v_extensions_845_);
lean_inc_ref(v_line_844_);
v___x_846_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_846_, 0, v_line_844_);
lean_ctor_set(v___x_846_, 1, v_body_843_);
lean_ctor_set(v___x_846_, 2, v_extensions_845_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_body___redArg___boxed(lean_object* v_builder_847_, lean_object* v_body_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Std_Http_Response_Builder_body___redArg(v_builder_847_, v_body_848_);
lean_dec_ref(v_builder_847_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_body(lean_object* v_t_850_, lean_object* v_builder_851_, lean_object* v_body_852_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = l_Std_Http_Response_Builder_body___redArg(v_builder_851_, v_body_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_body___boxed(lean_object* v_t_854_, lean_object* v_builder_855_, lean_object* v_body_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_Std_Http_Response_Builder_body(v_t_854_, v_builder_855_, v_body_856_);
lean_dec_ref(v_builder_855_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_build___redArg(lean_object* v_inst_858_, lean_object* v_builder_859_){
_start:
{
lean_object* v_line_860_; lean_object* v_extensions_861_; lean_object* v___x_862_; 
v_line_860_ = lean_ctor_get(v_builder_859_, 0);
v_extensions_861_ = lean_ctor_get(v_builder_859_, 1);
lean_inc(v_extensions_861_);
lean_inc_ref(v_line_860_);
v___x_862_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_862_, 0, v_line_860_);
lean_ctor_set(v___x_862_, 1, v_inst_858_);
lean_ctor_set(v___x_862_, 2, v_extensions_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_build___redArg___boxed(lean_object* v_inst_863_, lean_object* v_builder_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l_Std_Http_Response_Builder_build___redArg(v_inst_863_, v_builder_864_);
lean_dec_ref(v_builder_864_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_build(lean_object* v_t_866_, lean_object* v_inst_867_, lean_object* v_builder_868_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = l_Std_Http_Response_Builder_build___redArg(v_inst_867_, v_builder_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_build___boxed(lean_object* v_t_870_, lean_object* v_inst_871_, lean_object* v_builder_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l_Std_Http_Response_Builder_build(v_t_870_, v_inst_871_, v_builder_872_);
lean_dec_ref(v_builder_872_);
return v_res_873_;
}
}
static lean_object* _init_l_Std_Http_Response_ok___closed__0(void){
_start:
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_874_ = lean_box(4);
v___x_875_ = l_Std_Http_Response_Builder_new;
v___x_876_ = l_Std_Http_Response_Builder_status(v___x_875_, v___x_874_);
return v___x_876_;
}
}
static lean_object* _init_l_Std_Http_Response_ok(void){
_start:
{
lean_object* v___x_877_; 
v___x_877_ = lean_obj_once(&l_Std_Http_Response_ok___closed__0, &l_Std_Http_Response_ok___closed__0_once, _init_l_Std_Http_Response_ok___closed__0);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_withStatus(lean_object* v_status_878_){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_879_ = l_Std_Http_Response_Builder_new;
v___x_880_ = l_Std_Http_Response_Builder_status(v___x_879_, v_status_878_);
return v___x_880_;
}
}
static lean_object* _init_l_Std_Http_Response_notFound___closed__0(void){
_start:
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_881_ = lean_box(27);
v___x_882_ = l_Std_Http_Response_Builder_new;
v___x_883_ = l_Std_Http_Response_Builder_status(v___x_882_, v___x_881_);
return v___x_883_;
}
}
static lean_object* _init_l_Std_Http_Response_notFound(void){
_start:
{
lean_object* v___x_884_; 
v___x_884_ = lean_obj_once(&l_Std_Http_Response_notFound___closed__0, &l_Std_Http_Response_notFound___closed__0_once, _init_l_Std_Http_Response_notFound___closed__0);
return v___x_884_;
}
}
static lean_object* _init_l_Std_Http_Response_internalServerError___closed__0(void){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_885_ = lean_box(52);
v___x_886_ = l_Std_Http_Response_Builder_new;
v___x_887_ = l_Std_Http_Response_Builder_status(v___x_886_, v___x_885_);
return v___x_887_;
}
}
static lean_object* _init_l_Std_Http_Response_internalServerError(void){
_start:
{
lean_object* v___x_888_; 
v___x_888_ = lean_obj_once(&l_Std_Http_Response_internalServerError___closed__0, &l_Std_Http_Response_internalServerError___closed__0_once, _init_l_Std_Http_Response_internalServerError___closed__0);
return v___x_888_;
}
}
static lean_object* _init_l_Std_Http_Response_badRequest___closed__0(void){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_889_ = lean_box(23);
v___x_890_ = l_Std_Http_Response_Builder_new;
v___x_891_ = l_Std_Http_Response_Builder_status(v___x_890_, v___x_889_);
return v___x_891_;
}
}
static lean_object* _init_l_Std_Http_Response_badRequest(void){
_start:
{
lean_object* v___x_892_; 
v___x_892_ = lean_obj_once(&l_Std_Http_Response_badRequest___closed__0, &l_Std_Http_Response_badRequest___closed__0_once, _init_l_Std_Http_Response_badRequest___closed__0);
return v___x_892_;
}
}
static lean_object* _init_l_Std_Http_Response_created___closed__0(void){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_893_ = lean_box(5);
v___x_894_ = l_Std_Http_Response_Builder_new;
v___x_895_ = l_Std_Http_Response_Builder_status(v___x_894_, v___x_893_);
return v___x_895_;
}
}
static lean_object* _init_l_Std_Http_Response_created(void){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = lean_obj_once(&l_Std_Http_Response_created___closed__0, &l_Std_Http_Response_created___closed__0_once, _init_l_Std_Http_Response_created___closed__0);
return v___x_896_;
}
}
static lean_object* _init_l_Std_Http_Response_accepted___closed__0(void){
_start:
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_897_ = lean_box(6);
v___x_898_ = l_Std_Http_Response_Builder_new;
v___x_899_ = l_Std_Http_Response_Builder_status(v___x_898_, v___x_897_);
return v___x_899_;
}
}
static lean_object* _init_l_Std_Http_Response_accepted(void){
_start:
{
lean_object* v___x_900_; 
v___x_900_ = lean_obj_once(&l_Std_Http_Response_accepted___closed__0, &l_Std_Http_Response_accepted___closed__0_once, _init_l_Std_Http_Response_accepted___closed__0);
return v___x_900_;
}
}
static lean_object* _init_l_Std_Http_Response_unauthorized___closed__0(void){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_901_ = lean_box(24);
v___x_902_ = l_Std_Http_Response_Builder_new;
v___x_903_ = l_Std_Http_Response_Builder_status(v___x_902_, v___x_901_);
return v___x_903_;
}
}
static lean_object* _init_l_Std_Http_Response_unauthorized(void){
_start:
{
lean_object* v___x_904_; 
v___x_904_ = lean_obj_once(&l_Std_Http_Response_unauthorized___closed__0, &l_Std_Http_Response_unauthorized___closed__0_once, _init_l_Std_Http_Response_unauthorized___closed__0);
return v___x_904_;
}
}
static lean_object* _init_l_Std_Http_Response_forbidden___closed__0(void){
_start:
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_905_ = lean_box(26);
v___x_906_ = l_Std_Http_Response_Builder_new;
v___x_907_ = l_Std_Http_Response_Builder_status(v___x_906_, v___x_905_);
return v___x_907_;
}
}
static lean_object* _init_l_Std_Http_Response_forbidden(void){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = lean_obj_once(&l_Std_Http_Response_forbidden___closed__0, &l_Std_Http_Response_forbidden___closed__0_once, _init_l_Std_Http_Response_forbidden___closed__0);
return v___x_908_;
}
}
static lean_object* _init_l_Std_Http_Response_conflict___closed__0(void){
_start:
{
lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_909_ = lean_box(32);
v___x_910_ = l_Std_Http_Response_Builder_new;
v___x_911_ = l_Std_Http_Response_Builder_status(v___x_910_, v___x_909_);
return v___x_911_;
}
}
static lean_object* _init_l_Std_Http_Response_conflict(void){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = lean_obj_once(&l_Std_Http_Response_conflict___closed__0, &l_Std_Http_Response_conflict___closed__0_once, _init_l_Std_Http_Response_conflict___closed__0);
return v___x_912_;
}
}
static lean_object* _init_l_Std_Http_Response_serviceUnavailable___closed__0(void){
_start:
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_913_ = lean_box(55);
v___x_914_ = l_Std_Http_Response_Builder_new;
v___x_915_ = l_Std_Http_Response_Builder_status(v___x_914_, v___x_913_);
return v___x_915_;
}
}
static lean_object* _init_l_Std_Http_Response_serviceUnavailable(void){
_start:
{
lean_object* v___x_916_; 
v___x_916_ = lean_obj_once(&l_Std_Http_Response_serviceUnavailable___closed__0, &l_Std_Http_Response_serviceUnavailable___closed__0_once, _init_l_Std_Http_Response_serviceUnavailable___closed__0);
return v___x_916_;
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
