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
lean_object* l_Std_Http_Response_instToStringHead___lam__0(lean_object* v___x_105_, lean_object* v___x_106_, lean_object* v___x_107_, lean_object* v_fst_108_, lean_object* v___x_109_, uint32_t v___x_110_, lean_object* v___x_111_, lean_object* v_it_112_, lean_object* v_acc_113_, lean_object* v_hP_114_, lean_object* v_recur_115_){
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
LEAN_EXPORT void l_Std_Http_Response_instToStringHead___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_105_ = stack[0].m_obj;
lean_object* v___x_106_ = stack[1].m_obj;
lean_object* v___x_107_ = stack[2].m_obj;
lean_object* v_fst_108_ = stack[3].m_obj;
lean_object* v___x_109_ = stack[4].m_obj;
uint32_t v___x_110_ = stack[5].m_num;
lean_object* v___x_111_ = stack[6].m_obj;
lean_object* v_it_112_ = stack[7].m_obj;
lean_object* v_acc_113_ = stack[8].m_obj;
lean_object* v_recur_115_ = stack[10].m_obj;
lean_object* v_res_172_;
v_res_172_ = l_Std_Http_Response_instToStringHead___lam__0(v___x_105_, v___x_106_, v___x_107_, v_fst_108_, v___x_109_, v___x_110_, v___x_111_, v_it_112_, v_acc_113_, lean_box(0), v_recur_115_);
stack->m_obj
 = v_res_172_;
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instToStringHead___lam__0___boxed(lean_object* v___x_173_, lean_object* v___x_174_, lean_object* v___x_175_, lean_object* v_fst_176_, lean_object* v___x_177_, lean_object* v___x_178_, lean_object* v___x_179_, lean_object* v_it_180_, lean_object* v_acc_181_, lean_object* v_hP_182_, lean_object* v_recur_183_){
_start:
{
uint32_t v___x_750__boxed_184_; lean_object* v_res_185_; 
v___x_750__boxed_184_ = lean_unbox_uint32(v___x_178_);
lean_dec(v___x_178_);
v_res_185_ = l_Std_Http_Response_instToStringHead___lam__0(v___x_173_, v___x_174_, v___x_175_, v_fst_176_, v___x_177_, v___x_750__boxed_184_, v___x_179_, v_it_180_, v_acc_181_, v_hP_182_, v_recur_183_);
lean_dec_ref(v___x_179_);
lean_dec_ref(v_fst_176_);
lean_dec(v___x_175_);
lean_dec(v___x_174_);
lean_dec_ref(v___x_173_);
return v_res_185_;
}
}
static lean_object* _init_l_Std_Http_Response_instToStringHead___lam__1___boxed__const__1(void){
_start:
{
uint32_t v___x_190_; lean_object* v___x_191_; 
v___x_190_ = 45;
v___x_191_ = lean_box_uint32(v___x_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instToStringHead___lam__1(lean_object* v_x_192_){
_start:
{
lean_object* v_fst_193_; lean_object* v_snd_194_; lean_object* v___y_196_; lean_object* v___f_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v_it_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___f_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v_fst_193_ = lean_ctor_get(v_x_192_, 0);
lean_inc_n(v_fst_193_, 2);
v_snd_194_ = lean_ctor_get(v_x_192_, 1);
lean_inc(v_snd_194_);
lean_dec_ref(v_x_192_);
v___f_200_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__1___closed__1));
v___x_201_ = lean_unsigned_to_nat(0u);
v___x_202_ = lean_string_utf8_byte_size(v_fst_193_);
v___x_203_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_203_, 0, v_fst_193_);
lean_ctor_set(v___x_203_, 1, v___x_201_);
lean_ctor_set(v___x_203_, 2, v___x_202_);
lean_inc_ref(v___x_203_);
v_it_204_ = l_String_Slice_splitToSubslice___redArg(v___x_203_, v___f_200_);
v___x_205_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__1___closed__2));
v___x_206_ = lean_unsigned_to_nat(1u);
v___x_207_ = l_Std_Http_Response_instToStringHead___lam__1___boxed__const__1;
v___f_208_ = lean_alloc_closure((void*)(l_Std_Http_Response_instToStringHead___lam__0___boxed), 11, 7);
lean_closure_set(v___f_208_, 0, v___x_205_);
lean_closure_set(v___f_208_, 1, v___x_201_);
lean_closure_set(v___f_208_, 2, v___x_206_);
lean_closure_set(v___f_208_, 3, v_fst_193_);
lean_closure_set(v___f_208_, 4, v___x_202_);
lean_closure_set(v___f_208_, 5, v___x_207_);
lean_closure_set(v___f_208_, 6, v___x_203_);
v___x_209_ = lean_box(0);
v___x_210_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_208_, v_it_204_, v___x_209_, lean_box(0));
if (lean_obj_tag(v___x_210_) == 0)
{
lean_object* v___x_211_; 
v___x_211_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__1___closed__3));
v___y_196_ = v___x_211_;
goto v___jp_195_;
}
else
{
lean_object* v_val_212_; 
v_val_212_ = lean_ctor_get(v___x_210_, 0);
lean_inc(v_val_212_);
lean_dec_ref_known(v___x_210_, 1);
v___y_196_ = v_val_212_;
goto v___jp_195_;
}
v___jp_195_:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_197_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__1___closed__0));
v___x_198_ = lean_string_append(v___y_196_, v___x_197_);
v___x_199_ = lean_string_append(v___x_198_, v_snd_194_);
lean_dec(v_snd_194_);
return v___x_199_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instToStringHead___lam__2(lean_object* v___f_238_, lean_object* v_r_239_){
_start:
{
lean_object* v_status_240_; uint8_t v_version_241_; lean_object* v_headers_242_; lean_object* v___y_244_; 
v_status_240_ = lean_ctor_get(v_r_239_, 0);
lean_inc(v_status_240_);
v_version_241_ = lean_ctor_get_uint8(v_r_239_, sizeof(void*)*2);
v_headers_242_ = lean_ctor_get(v_r_239_, 1);
lean_inc_ref(v_headers_242_);
lean_dec_ref(v_r_239_);
switch(v_version_241_)
{
case 0:
{
lean_object* v___x_265_; 
v___x_265_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__12));
v___y_244_ = v___x_265_;
goto v___jp_243_;
}
case 1:
{
lean_object* v___x_266_; 
v___x_266_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__13));
v___y_244_ = v___x_266_;
goto v___jp_243_;
}
case 2:
{
lean_object* v___x_267_; 
v___x_267_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__14));
v___y_244_ = v___x_267_;
goto v___jp_243_;
}
default: 
{
lean_object* v___x_268_; 
v___x_268_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__15));
v___y_244_ = v___x_268_;
goto v___jp_243_;
}
}
v___jp_243_:
{
lean_object* v_entries_245_; lean_object* v___x_246_; lean_object* v___x_247_; uint16_t v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; size_t v_sz_258_; size_t v___x_259_; lean_object* v_pairs_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v_entries_245_ = lean_ctor_get(v_headers_242_, 0);
lean_inc_ref(v_entries_245_);
lean_dec_ref(v_headers_242_);
v___x_246_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__0));
lean_inc_ref(v___y_244_);
v___x_247_ = lean_string_append(v___y_244_, v___x_246_);
v___x_248_ = l_Std_Http_Status_toCode(v_status_240_);
v___x_249_ = lean_uint16_to_nat(v___x_248_);
v___x_250_ = l_Nat_reprFast(v___x_249_);
v___x_251_ = lean_string_append(v___x_247_, v___x_250_);
lean_dec_ref(v___x_250_);
v___x_252_ = lean_string_append(v___x_251_, v___x_246_);
v___x_253_ = l_Std_Http_Status_reasonPhrase(v_status_240_);
lean_dec(v_status_240_);
v___x_254_ = lean_string_append(v___x_252_, v___x_253_);
lean_dec_ref(v___x_253_);
v___x_255_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__1));
v___x_256_ = lean_string_append(v___x_254_, v___x_255_);
v___x_257_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__11));
v_sz_258_ = lean_array_size(v_entries_245_);
v___x_259_ = ((size_t)0ULL);
v_pairs_260_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_257_, v___f_238_, v_sz_258_, v___x_259_, v_entries_245_);
v___x_261_ = lean_array_to_list(v_pairs_260_);
v___x_262_ = l_String_intercalate(v___x_255_, v___x_261_);
v___x_263_ = lean_string_append(v___x_256_, v___x_262_);
lean_dec_ref(v___x_262_);
v___x_264_ = lean_string_append(v___x_263_, v___x_255_);
return v___x_264_;
}
}
}
lean_object* l_Std_Http_Response_instEncodeV11Head___lam__0(lean_object* v___x_273_, lean_object* v___x_274_, lean_object* v___x_275_, lean_object* v_name_276_, lean_object* v___x_277_, uint32_t v___x_278_, lean_object* v___x_279_, lean_object* v_it_280_, lean_object* v_acc_281_, lean_object* v_hP_282_, lean_object* v_recur_283_){
_start:
{
lean_object* v_it_285_; lean_object* v_out_286_; lean_object* v_it_302_; lean_object* v_startInclusive_303_; lean_object* v_endExclusive_304_; 
if (lean_obj_tag(v_it_280_) == 0)
{
lean_object* v_currPos_316_; lean_object* v_searcher_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_339_; 
v_currPos_316_ = lean_ctor_get(v_it_280_, 0);
v_searcher_317_ = lean_ctor_get(v_it_280_, 1);
v_isSharedCheck_339_ = !lean_is_exclusive(v_it_280_);
if (v_isSharedCheck_339_ == 0)
{
v___x_319_ = v_it_280_;
v_isShared_320_ = v_isSharedCheck_339_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_searcher_317_);
lean_inc(v_currPos_316_);
lean_dec(v_it_280_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_339_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
uint8_t v_decide_321_; 
v_decide_321_ = lean_nat_dec_eq(v_searcher_317_, v___x_277_);
if (v_decide_321_ == 0)
{
uint32_t v___x_322_; uint8_t v___x_323_; 
lean_dec(v___x_277_);
v___x_322_ = lean_string_utf8_get_fast(v_name_276_, v_searcher_317_);
v___x_323_ = lean_uint32_dec_eq(v___x_322_, v___x_278_);
if (v___x_323_ == 0)
{
lean_object* v___x_324_; lean_object* v___x_326_; 
v___x_324_ = lean_string_utf8_next_fast(v_name_276_, v_searcher_317_);
lean_dec(v_searcher_317_);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 1, v___x_324_);
v___x_326_ = v___x_319_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_currPos_316_);
lean_ctor_set(v_reuseFailAlloc_328_, 1, v___x_324_);
v___x_326_ = v_reuseFailAlloc_328_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
lean_object* v___x_327_; 
v___x_327_ = lean_apply_4(v_recur_283_, v___x_326_, v_acc_281_, lean_box(0), lean_box(0));
return v___x_327_;
}
}
else
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v_slice_332_; lean_object* v_nextIt_334_; 
v___x_329_ = lean_string_utf8_next_fast(v_name_276_, v_searcher_317_);
v___x_330_ = lean_nat_sub(v___x_329_, v_searcher_317_);
v___x_331_ = lean_nat_add(v_searcher_317_, v___x_330_);
lean_dec(v___x_330_);
v_slice_332_ = l_String_Slice_subslice_x21(v___x_279_, v_currPos_316_, v_searcher_317_);
lean_inc(v___x_331_);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 1, v___x_331_);
lean_ctor_set(v___x_319_, 0, v___x_331_);
v_nextIt_334_ = v___x_319_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v___x_331_);
lean_ctor_set(v_reuseFailAlloc_337_, 1, v___x_331_);
v_nextIt_334_ = v_reuseFailAlloc_337_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
lean_object* v_startInclusive_335_; lean_object* v_endExclusive_336_; 
v_startInclusive_335_ = lean_ctor_get(v_slice_332_, 0);
lean_inc(v_startInclusive_335_);
v_endExclusive_336_ = lean_ctor_get(v_slice_332_, 1);
lean_inc(v_endExclusive_336_);
lean_dec_ref(v_slice_332_);
v_it_302_ = v_nextIt_334_;
v_startInclusive_303_ = v_startInclusive_335_;
v_endExclusive_304_ = v_endExclusive_336_;
goto v___jp_301_;
}
}
}
else
{
lean_object* v___x_338_; 
lean_del_object(v___x_319_);
lean_dec(v_searcher_317_);
v___x_338_ = lean_box(1);
v_it_302_ = v___x_338_;
v_startInclusive_303_ = v_currPos_316_;
v_endExclusive_304_ = v___x_277_;
goto v___jp_301_;
}
}
}
else
{
lean_dec_ref(v_recur_283_);
lean_dec(v___x_277_);
return v_acc_281_;
}
v___jp_284_:
{
if (lean_obj_tag(v_acc_281_) == 0)
{
lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_287_, 0, v_out_286_);
v___x_288_ = lean_apply_4(v_recur_283_, v_it_285_, v___x_287_, lean_box(0), lean_box(0));
return v___x_288_;
}
else
{
lean_object* v_val_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_300_; 
v_val_289_ = lean_ctor_get(v_acc_281_, 0);
v_isSharedCheck_300_ = !lean_is_exclusive(v_acc_281_);
if (v_isSharedCheck_300_ == 0)
{
v___x_291_ = v_acc_281_;
v_isShared_292_ = v_isSharedCheck_300_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_val_289_);
lean_dec(v_acc_281_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_300_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_297_; 
v___x_293_ = lean_string_utf8_extract_fast(v___x_273_, v___x_274_, v___x_275_);
v___x_294_ = lean_string_append(v_val_289_, v___x_293_);
lean_dec_ref(v___x_293_);
v___x_295_ = lean_string_append(v___x_294_, v_out_286_);
lean_dec_ref(v_out_286_);
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 0, v___x_295_);
v___x_297_ = v___x_291_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v___x_295_);
v___x_297_ = v_reuseFailAlloc_299_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
lean_object* v___x_298_; 
v___x_298_ = lean_apply_4(v_recur_283_, v_it_285_, v___x_297_, lean_box(0), lean_box(0));
return v___x_298_;
}
}
}
}
v___jp_301_:
{
lean_object* v___x_305_; uint32_t v___x_306_; uint32_t v___x_307_; uint8_t v___x_308_; 
v___x_305_ = lean_string_utf8_extract_fast(v_name_276_, v_startInclusive_303_, v_endExclusive_304_);
lean_dec(v_endExclusive_304_);
lean_dec(v_startInclusive_303_);
v___x_306_ = lean_string_utf8_get(v___x_305_, v___x_274_);
v___x_307_ = 97;
v___x_308_ = lean_uint32_dec_le(v___x_307_, v___x_306_);
if (v___x_308_ == 0)
{
lean_object* v___x_309_; 
v___x_309_ = lean_string_utf8_set(v___x_305_, v___x_274_, v___x_306_);
v_it_285_ = v_it_302_;
v_out_286_ = v___x_309_;
goto v___jp_284_;
}
else
{
uint32_t v___x_310_; uint8_t v___x_311_; 
v___x_310_ = 122;
v___x_311_ = lean_uint32_dec_le(v___x_306_, v___x_310_);
if (v___x_311_ == 0)
{
lean_object* v___x_312_; 
v___x_312_ = lean_string_utf8_set(v___x_305_, v___x_274_, v___x_306_);
v_it_285_ = v_it_302_;
v_out_286_ = v___x_312_;
goto v___jp_284_;
}
else
{
uint32_t v___x_313_; uint32_t v___x_314_; lean_object* v___x_315_; 
v___x_313_ = 4294967264;
v___x_314_ = lean_uint32_add(v___x_306_, v___x_313_);
v___x_315_ = lean_string_utf8_set(v___x_305_, v___x_274_, v___x_314_);
v_it_285_ = v_it_302_;
v_out_286_ = v___x_315_;
goto v___jp_284_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Response_instEncodeV11Head___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_273_ = stack[0].m_obj;
lean_object* v___x_274_ = stack[1].m_obj;
lean_object* v___x_275_ = stack[2].m_obj;
lean_object* v_name_276_ = stack[3].m_obj;
lean_object* v___x_277_ = stack[4].m_obj;
uint32_t v___x_278_ = stack[5].m_num;
lean_object* v___x_279_ = stack[6].m_obj;
lean_object* v_it_280_ = stack[7].m_obj;
lean_object* v_acc_281_ = stack[8].m_obj;
lean_object* v_recur_283_ = stack[10].m_obj;
lean_object* v_res_340_;
v_res_340_ = l_Std_Http_Response_instEncodeV11Head___lam__0(v___x_273_, v___x_274_, v___x_275_, v_name_276_, v___x_277_, v___x_278_, v___x_279_, v_it_280_, v_acc_281_, lean_box(0), v_recur_283_);
stack->m_obj
 = v_res_340_;
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instEncodeV11Head___lam__0___boxed(lean_object* v___x_341_, lean_object* v___x_342_, lean_object* v___x_343_, lean_object* v_name_344_, lean_object* v___x_345_, lean_object* v___x_346_, lean_object* v___x_347_, lean_object* v_it_348_, lean_object* v_acc_349_, lean_object* v_hP_350_, lean_object* v_recur_351_){
_start:
{
uint32_t v___x_1212__boxed_352_; lean_object* v_res_353_; 
v___x_1212__boxed_352_ = lean_unbox_uint32(v___x_346_);
lean_dec(v___x_346_);
v_res_353_ = l_Std_Http_Response_instEncodeV11Head___lam__0(v___x_341_, v___x_342_, v___x_343_, v_name_344_, v___x_345_, v___x_1212__boxed_352_, v___x_347_, v_it_348_, v_acc_349_, v_hP_350_, v_recur_351_);
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
v___x_383_ = lean_unsigned_to_nat(1u);
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
v___x_388_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__1___closed__3));
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
static lean_object* _init_l_Std_Http_Response_instEncodeV11Head___lam__2___closed__1(void){
_start:
{
lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_400_ = ((lean_object*)(l_Std_Http_Response_instEncodeV11Head___lam__2___closed__0));
v___x_401_ = lean_byte_array_size(v___x_400_);
return v___x_401_;
}
}
static lean_object* _init_l_Std_Http_Response_instEncodeV11Head___lam__2___closed__2(void){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_402_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__1));
v___x_403_ = lean_string_to_utf8(v___x_402_);
return v___x_403_;
}
}
static lean_object* _init_l_Std_Http_Response_instEncodeV11Head___lam__2___closed__3(void){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_404_ = lean_obj_once(&l_Std_Http_Response_instEncodeV11Head___lam__2___closed__2, &l_Std_Http_Response_instEncodeV11Head___lam__2___closed__2_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__2___closed__2);
v___x_405_ = lean_byte_array_size(v___x_404_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instEncodeV11Head___lam__2(lean_object* v___f_406_, lean_object* v_buffer_407_, lean_object* v_r_408_){
_start:
{
lean_object* v_status_409_; uint8_t v_version_410_; lean_object* v_headers_411_; lean_object* v___y_413_; 
v_status_409_ = lean_ctor_get(v_r_408_, 0);
v_version_410_ = lean_ctor_get_uint8(v_r_408_, sizeof(void*)*2);
v_headers_411_ = lean_ctor_get(v_r_408_, 1);
switch(v_version_410_)
{
case 0:
{
lean_object* v___x_461_; 
v___x_461_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__12));
v___y_413_ = v___x_461_;
goto v___jp_412_;
}
case 1:
{
lean_object* v___x_462_; 
v___x_462_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__13));
v___y_413_ = v___x_462_;
goto v___jp_412_;
}
case 2:
{
lean_object* v___x_463_; 
v___x_463_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__14));
v___y_413_ = v___x_463_;
goto v___jp_412_;
}
default: 
{
lean_object* v___x_464_; 
v___x_464_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__15));
v___y_413_ = v___x_464_;
goto v___jp_412_;
}
}
v___jp_412_:
{
lean_object* v_data_414_; lean_object* v_size_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_460_; 
v_data_414_ = lean_ctor_get(v_buffer_407_, 0);
v_size_415_ = lean_ctor_get(v_buffer_407_, 1);
v_isSharedCheck_460_ = !lean_is_exclusive(v_buffer_407_);
if (v_isSharedCheck_460_ == 0)
{
v___x_417_ = v_buffer_407_;
v_isShared_418_ = v_isSharedCheck_460_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_size_415_);
lean_inc(v_data_414_);
lean_dec(v_buffer_407_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_460_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; uint16_t v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v_buffer_446_; 
v___x_419_ = lean_string_to_utf8(v___y_413_);
lean_inc_ref(v___x_419_);
v___x_420_ = lean_array_push(v_data_414_, v___x_419_);
v___x_421_ = lean_byte_array_size(v___x_419_);
lean_dec_ref(v___x_419_);
v___x_422_ = lean_nat_add(v_size_415_, v___x_421_);
lean_dec(v_size_415_);
v___x_423_ = ((lean_object*)(l_Std_Http_Response_instEncodeV11Head___lam__2___closed__0));
v___x_424_ = lean_array_push(v___x_420_, v___x_423_);
v___x_425_ = lean_obj_once(&l_Std_Http_Response_instEncodeV11Head___lam__2___closed__1, &l_Std_Http_Response_instEncodeV11Head___lam__2___closed__1_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__2___closed__1);
v___x_426_ = lean_nat_add(v___x_422_, v___x_425_);
lean_dec(v___x_422_);
v___x_427_ = l_Std_Http_Status_toCode(v_status_409_);
v___x_428_ = lean_uint16_to_nat(v___x_427_);
v___x_429_ = l_Nat_reprFast(v___x_428_);
v___x_430_ = lean_string_to_utf8(v___x_429_);
lean_dec_ref(v___x_429_);
lean_inc_ref(v___x_430_);
v___x_431_ = lean_array_push(v___x_424_, v___x_430_);
v___x_432_ = lean_byte_array_size(v___x_430_);
lean_dec_ref(v___x_430_);
v___x_433_ = lean_nat_add(v___x_426_, v___x_432_);
lean_dec(v___x_426_);
v___x_434_ = lean_array_push(v___x_431_, v___x_423_);
v___x_435_ = lean_nat_add(v___x_433_, v___x_425_);
lean_dec(v___x_433_);
v___x_436_ = l_Std_Http_Status_reasonPhrase(v_status_409_);
v___x_437_ = lean_string_to_utf8(v___x_436_);
lean_dec_ref(v___x_436_);
lean_inc_ref(v___x_437_);
v___x_438_ = lean_array_push(v___x_434_, v___x_437_);
v___x_439_ = lean_byte_array_size(v___x_437_);
lean_dec_ref(v___x_437_);
v___x_440_ = lean_nat_add(v___x_435_, v___x_439_);
lean_dec(v___x_435_);
v___x_441_ = lean_obj_once(&l_Std_Http_Response_instEncodeV11Head___lam__2___closed__2, &l_Std_Http_Response_instEncodeV11Head___lam__2___closed__2_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__2___closed__2);
v___x_442_ = lean_array_push(v___x_438_, v___x_441_);
v___x_443_ = lean_obj_once(&l_Std_Http_Response_instEncodeV11Head___lam__2___closed__3, &l_Std_Http_Response_instEncodeV11Head___lam__2___closed__3_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__2___closed__3);
v___x_444_ = lean_nat_add(v___x_440_, v___x_443_);
lean_dec(v___x_440_);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 1, v___x_444_);
lean_ctor_set(v___x_417_, 0, v___x_442_);
v_buffer_446_ = v___x_417_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v___x_442_);
lean_ctor_set(v_reuseFailAlloc_459_, 1, v___x_444_);
v_buffer_446_ = v_reuseFailAlloc_459_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
lean_object* v_buffer_447_; lean_object* v_data_448_; lean_object* v_size_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_458_; 
v_buffer_447_ = l_Std_Http_Headers_fold___redArg(v_headers_411_, v_buffer_446_, v___f_406_);
v_data_448_ = lean_ctor_get(v_buffer_447_, 0);
v_size_449_ = lean_ctor_get(v_buffer_447_, 1);
v_isSharedCheck_458_ = !lean_is_exclusive(v_buffer_447_);
if (v_isSharedCheck_458_ == 0)
{
v___x_451_ = v_buffer_447_;
v_isShared_452_ = v_isSharedCheck_458_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_size_449_);
lean_inc(v_data_448_);
lean_dec(v_buffer_447_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_458_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_456_; 
v___x_453_ = lean_array_push(v_data_448_, v___x_441_);
v___x_454_ = lean_nat_add(v_size_449_, v___x_443_);
lean_dec(v_size_449_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 1, v___x_454_);
lean_ctor_set(v___x_451_, 0, v___x_453_);
v___x_456_ = v___x_451_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v___x_453_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v___x_454_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instEncodeV11Head___lam__2___boxed(lean_object* v___f_465_, lean_object* v_buffer_466_, lean_object* v_r_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Std_Http_Response_instEncodeV11Head___lam__2(v___f_465_, v_buffer_466_, v_r_467_);
lean_dec_ref(v_r_467_);
return v_res_468_;
}
}
static lean_object* _init_l_Std_Http_Response_new___closed__0(void){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_473_ = l_Std_Http_Extensions_empty;
v___x_474_ = lean_obj_once(&l_Std_Http_Response_instInhabitedHead_default___closed__0, &l_Std_Http_Response_instInhabitedHead_default___closed__0_once, _init_l_Std_Http_Response_instInhabitedHead_default___closed__0);
v___x_475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_475_, 0, v___x_474_);
lean_ctor_set(v___x_475_, 1, v___x_473_);
return v___x_475_;
}
}
static lean_object* _init_l_Std_Http_Response_new(void){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = lean_obj_once(&l_Std_Http_Response_new___closed__0, &l_Std_Http_Response_new___closed__0_once, _init_l_Std_Http_Response_new___closed__0);
return v___x_476_;
}
}
static lean_object* _init_l_Std_Http_Response_Builder_new(void){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = lean_obj_once(&l_Std_Http_Response_new___closed__0, &l_Std_Http_Response_new___closed__0_once, _init_l_Std_Http_Response_new___closed__0);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_status(lean_object* v_builder_478_, lean_object* v_status_479_){
_start:
{
lean_object* v_line_480_; lean_object* v_extensions_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_498_; 
v_line_480_ = lean_ctor_get(v_builder_478_, 0);
v_extensions_481_ = lean_ctor_get(v_builder_478_, 1);
v_isSharedCheck_498_ = !lean_is_exclusive(v_builder_478_);
if (v_isSharedCheck_498_ == 0)
{
v___x_483_ = v_builder_478_;
v_isShared_484_ = v_isSharedCheck_498_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_extensions_481_);
lean_inc(v_line_480_);
lean_dec(v_builder_478_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_498_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
uint8_t v_version_485_; lean_object* v_headers_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_496_; 
v_version_485_ = lean_ctor_get_uint8(v_line_480_, sizeof(void*)*2);
v_headers_486_ = lean_ctor_get(v_line_480_, 1);
v_isSharedCheck_496_ = !lean_is_exclusive(v_line_480_);
if (v_isSharedCheck_496_ == 0)
{
lean_object* v_unused_497_; 
v_unused_497_ = lean_ctor_get(v_line_480_, 0);
lean_dec(v_unused_497_);
v___x_488_ = v_line_480_;
v_isShared_489_ = v_isSharedCheck_496_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_headers_486_);
lean_dec(v_line_480_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_496_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_491_; 
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 0, v_status_479_);
v___x_491_ = v___x_488_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_status_479_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v_headers_486_);
lean_ctor_set_uint8(v_reuseFailAlloc_495_, sizeof(void*)*2, v_version_485_);
v___x_491_ = v_reuseFailAlloc_495_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
lean_object* v___x_493_; 
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 0, v___x_491_);
v___x_493_ = v___x_483_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v___x_491_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v_extensions_481_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_headers(lean_object* v_builder_499_, lean_object* v_headers_500_){
_start:
{
lean_object* v_line_501_; lean_object* v_extensions_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_519_; 
v_line_501_ = lean_ctor_get(v_builder_499_, 0);
v_extensions_502_ = lean_ctor_get(v_builder_499_, 1);
v_isSharedCheck_519_ = !lean_is_exclusive(v_builder_499_);
if (v_isSharedCheck_519_ == 0)
{
v___x_504_ = v_builder_499_;
v_isShared_505_ = v_isSharedCheck_519_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_extensions_502_);
lean_inc(v_line_501_);
lean_dec(v_builder_499_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_519_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v_status_506_; uint8_t v_version_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_517_; 
v_status_506_ = lean_ctor_get(v_line_501_, 0);
v_version_507_ = lean_ctor_get_uint8(v_line_501_, sizeof(void*)*2);
v_isSharedCheck_517_ = !lean_is_exclusive(v_line_501_);
if (v_isSharedCheck_517_ == 0)
{
lean_object* v_unused_518_; 
v_unused_518_ = lean_ctor_get(v_line_501_, 1);
lean_dec(v_unused_518_);
v___x_509_ = v_line_501_;
v_isShared_510_ = v_isSharedCheck_517_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_status_506_);
lean_dec(v_line_501_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_517_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_512_; 
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 1, v_headers_500_);
v___x_512_ = v___x_509_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_status_506_);
lean_ctor_set(v_reuseFailAlloc_516_, 1, v_headers_500_);
lean_ctor_set_uint8(v_reuseFailAlloc_516_, sizeof(void*)*2, v_version_507_);
v___x_512_ = v_reuseFailAlloc_516_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
lean_object* v___x_514_; 
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 0, v___x_512_);
v___x_514_ = v___x_504_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v___x_512_);
lean_ctor_set(v_reuseFailAlloc_515_, 1, v_extensions_502_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
}
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0___redArg(lean_object* v_a_520_, lean_object* v_x_521_){
_start:
{
if (lean_obj_tag(v_x_521_) == 0)
{
uint8_t v___x_522_; 
v___x_522_ = 0;
return v___x_522_;
}
else
{
lean_object* v_key_523_; lean_object* v_tail_524_; uint8_t v___x_525_; 
v_key_523_ = lean_ctor_get(v_x_521_, 0);
v_tail_524_ = lean_ctor_get(v_x_521_, 2);
v___x_525_ = lean_string_dec_eq(v_key_523_, v_a_520_);
if (v___x_525_ == 0)
{
v_x_521_ = v_tail_524_;
goto _start;
}
else
{
return v___x_525_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_520_ = stack[0].m_obj;
lean_object* v_x_521_ = stack[1].m_obj;
uint8_t v_res_527_;
v_res_527_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0___redArg(v_a_520_, v_x_521_);
stack->m_num = v_res_527_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0___redArg___boxed(lean_object* v_a_528_, lean_object* v_x_529_){
_start:
{
uint8_t v_res_530_; lean_object* v_r_531_; 
v_res_530_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0___redArg(v_a_528_, v_x_529_);
lean_dec(v_x_529_);
lean_dec_ref(v_a_528_);
v_r_531_ = lean_box(v_res_530_);
return v_r_531_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_532_, lean_object* v_x_533_){
_start:
{
if (lean_obj_tag(v_x_533_) == 0)
{
return v_x_532_;
}
else
{
lean_object* v_key_534_; lean_object* v_value_535_; lean_object* v_tail_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_559_; 
v_key_534_ = lean_ctor_get(v_x_533_, 0);
v_value_535_ = lean_ctor_get(v_x_533_, 1);
v_tail_536_ = lean_ctor_get(v_x_533_, 2);
v_isSharedCheck_559_ = !lean_is_exclusive(v_x_533_);
if (v_isSharedCheck_559_ == 0)
{
v___x_538_ = v_x_533_;
v_isShared_539_ = v_isSharedCheck_559_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_tail_536_);
lean_inc(v_value_535_);
lean_inc(v_key_534_);
lean_dec(v_x_533_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_559_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_540_; uint64_t v___x_541_; uint64_t v___x_542_; uint64_t v___x_543_; uint64_t v_fold_544_; uint64_t v___x_545_; uint64_t v___x_546_; uint64_t v___x_547_; size_t v___x_548_; size_t v___x_549_; size_t v___x_550_; size_t v___x_551_; size_t v___x_552_; lean_object* v___x_553_; lean_object* v___x_555_; 
v___x_540_ = lean_array_get_size(v_x_532_);
v___x_541_ = lean_string_hash(v_key_534_);
v___x_542_ = 32ULL;
v___x_543_ = lean_uint64_shift_right(v___x_541_, v___x_542_);
v_fold_544_ = lean_uint64_xor(v___x_541_, v___x_543_);
v___x_545_ = 16ULL;
v___x_546_ = lean_uint64_shift_right(v_fold_544_, v___x_545_);
v___x_547_ = lean_uint64_xor(v_fold_544_, v___x_546_);
v___x_548_ = lean_uint64_to_usize(v___x_547_);
v___x_549_ = lean_usize_of_nat(v___x_540_);
v___x_550_ = ((size_t)1ULL);
v___x_551_ = lean_usize_sub(v___x_549_, v___x_550_);
v___x_552_ = lean_usize_land(v___x_548_, v___x_551_);
v___x_553_ = lean_array_uget_borrowed(v_x_532_, v___x_552_);
lean_inc(v___x_553_);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 2, v___x_553_);
v___x_555_ = v___x_538_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_key_534_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v_value_535_);
lean_ctor_set(v_reuseFailAlloc_558_, 2, v___x_553_);
v___x_555_ = v_reuseFailAlloc_558_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
lean_object* v___x_556_; 
v___x_556_ = lean_array_uset(v_x_532_, v___x_552_, v___x_555_);
v_x_532_ = v___x_556_;
v_x_533_ = v_tail_536_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2___redArg(lean_object* v_i_560_, lean_object* v_source_561_, lean_object* v_target_562_){
_start:
{
lean_object* v___x_563_; uint8_t v___x_564_; 
v___x_563_ = lean_array_get_size(v_source_561_);
v___x_564_ = lean_nat_dec_lt(v_i_560_, v___x_563_);
if (v___x_564_ == 0)
{
lean_dec_ref(v_source_561_);
lean_dec(v_i_560_);
return v_target_562_;
}
else
{
lean_object* v_es_565_; lean_object* v___x_566_; lean_object* v_source_567_; lean_object* v_target_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v_es_565_ = lean_array_fget(v_source_561_, v_i_560_);
v___x_566_ = lean_box(0);
v_source_567_ = lean_array_fset(v_source_561_, v_i_560_, v___x_566_);
v_target_568_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2_spec__3___redArg(v_target_562_, v_es_565_);
v___x_569_ = lean_unsigned_to_nat(1u);
v___x_570_ = lean_nat_add(v_i_560_, v___x_569_);
lean_dec(v_i_560_);
v_i_560_ = v___x_570_;
v_source_561_ = v_source_567_;
v_target_562_ = v_target_568_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1___redArg(lean_object* v_data_572_){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v_nbuckets_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_573_ = lean_array_get_size(v_data_572_);
v___x_574_ = lean_unsigned_to_nat(2u);
v_nbuckets_575_ = lean_nat_mul(v___x_573_, v___x_574_);
v___x_576_ = lean_unsigned_to_nat(0u);
v___x_577_ = lean_box(0);
v___x_578_ = lean_mk_array(v_nbuckets_575_, v___x_577_);
v___x_579_ = lean_array_propagate_mark(v_data_572_, v___x_578_);
v___x_580_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2___redArg(v___x_576_, v_data_572_, v___x_579_);
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
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0(lean_object* v_00_u03b2_713_, lean_object* v_a_714_, lean_object* v_x_715_){
_start:
{
uint8_t v___x_716_; 
v___x_716_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0___redArg(v_a_714_, v_x_715_);
return v___x_716_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_714_ = stack[1].m_obj;
lean_object* v_x_715_ = stack[2].m_obj;
uint8_t v_res_717_;
v_res_717_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0(lean_box(0), v_a_714_, v_x_715_);
stack->m_num = v_res_717_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0___boxed(lean_object* v_00_u03b2_718_, lean_object* v_a_719_, lean_object* v_x_720_){
_start:
{
uint8_t v_res_721_; lean_object* v_r_722_; 
v_res_721_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0(v_00_u03b2_718_, v_a_719_, v_x_720_);
lean_dec(v_x_720_);
lean_dec_ref(v_a_719_);
v_r_722_ = lean_box(v_res_721_);
return v_r_722_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1(lean_object* v_00_u03b2_723_, lean_object* v_data_724_){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1___redArg(v_data_724_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_726_, lean_object* v_i_727_, lean_object* v_source_728_, lean_object* v_target_729_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2___redArg(v_i_727_, v_source_728_, v_target_729_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_731_, lean_object* v_x_732_, lean_object* v_x_733_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2_spec__3___redArg(v_x_732_, v_x_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_header_x21(lean_object* v_builder_735_, lean_object* v_key_736_, lean_object* v_value_737_){
_start:
{
lean_object* v_line_738_; lean_object* v_headers_739_; lean_object* v_extensions_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_772_; 
v_line_738_ = lean_ctor_get(v_builder_735_, 0);
lean_inc_ref(v_line_738_);
v_headers_739_ = lean_ctor_get(v_line_738_, 1);
lean_inc_ref(v_headers_739_);
v_extensions_740_ = lean_ctor_get(v_builder_735_, 1);
v_isSharedCheck_772_ = !lean_is_exclusive(v_builder_735_);
if (v_isSharedCheck_772_ == 0)
{
lean_object* v_unused_773_; 
v_unused_773_ = lean_ctor_get(v_builder_735_, 0);
lean_dec(v_unused_773_);
v___x_742_ = v_builder_735_;
v_isShared_743_ = v_isSharedCheck_772_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_extensions_740_);
lean_dec(v_builder_735_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_772_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v_status_744_; uint8_t v_version_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_770_; 
v_status_744_ = lean_ctor_get(v_line_738_, 0);
v_version_745_ = lean_ctor_get_uint8(v_line_738_, sizeof(void*)*2);
v_isSharedCheck_770_ = !lean_is_exclusive(v_line_738_);
if (v_isSharedCheck_770_ == 0)
{
lean_object* v_unused_771_; 
v_unused_771_ = lean_ctor_get(v_line_738_, 1);
lean_dec(v_unused_771_);
v___x_747_ = v_line_738_;
v_isShared_748_ = v_isSharedCheck_770_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_status_744_);
lean_dec(v_line_738_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_770_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v_entries_749_; lean_object* v_indexes_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_769_; 
v_entries_749_ = lean_ctor_get(v_headers_739_, 0);
v_indexes_750_ = lean_ctor_get(v_headers_739_, 1);
v_isSharedCheck_769_ = !lean_is_exclusive(v_headers_739_);
if (v_isSharedCheck_769_ == 0)
{
v___x_752_ = v_headers_739_;
v_isShared_753_ = v_isSharedCheck_769_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_indexes_750_);
lean_inc(v_entries_749_);
lean_dec(v_headers_739_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_769_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v_key_754_; lean_object* v_value_755_; lean_object* v_i_756_; lean_object* v___x_757_; lean_object* v_entries_758_; lean_object* v_indexes_759_; lean_object* v___x_761_; 
v_key_754_ = l_Std_Http_Header_Name_ofString_x21(v_key_736_);
v_value_755_ = l_Std_Http_Header_Value_ofString_x21(v_value_737_);
v_i_756_ = lean_array_get_size(v_entries_749_);
lean_inc_ref(v_key_754_);
v___x_757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_757_, 0, v_key_754_);
lean_ctor_set(v___x_757_, 1, v_value_755_);
v_entries_758_ = lean_array_push(v_entries_749_, v___x_757_);
v_indexes_759_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0(v_i_756_, v_indexes_750_, v_key_754_);
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 1, v_indexes_759_);
lean_ctor_set(v___x_752_, 0, v_entries_758_);
v___x_761_ = v___x_752_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_entries_758_);
lean_ctor_set(v_reuseFailAlloc_768_, 1, v_indexes_759_);
v___x_761_ = v_reuseFailAlloc_768_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
lean_object* v___x_763_; 
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 1, v___x_761_);
v___x_763_ = v___x_747_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_status_744_);
lean_ctor_set(v_reuseFailAlloc_767_, 1, v___x_761_);
lean_ctor_set_uint8(v_reuseFailAlloc_767_, sizeof(void*)*2, v_version_745_);
v___x_763_ = v_reuseFailAlloc_767_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
lean_object* v___x_765_; 
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 0, v___x_763_);
v___x_765_ = v___x_742_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v___x_763_);
lean_ctor_set(v_reuseFailAlloc_766_, 1, v_extensions_740_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_header_x3f(lean_object* v_builder_774_, lean_object* v_key_775_, lean_object* v_value_776_){
_start:
{
lean_object* v___x_777_; 
v___x_777_ = l_Std_Http_Header_Name_ofString_x3f(v_key_775_);
if (lean_obj_tag(v___x_777_) == 0)
{
lean_object* v___x_778_; 
lean_dec_ref(v_value_776_);
lean_dec_ref(v_builder_774_);
v___x_778_ = lean_box(0);
return v___x_778_;
}
else
{
lean_object* v_val_779_; lean_object* v___x_780_; 
v_val_779_ = lean_ctor_get(v___x_777_, 0);
lean_inc(v_val_779_);
lean_dec_ref_known(v___x_777_, 1);
v___x_780_ = l_Std_Http_Header_Value_ofString_x3f(v_value_776_);
if (lean_obj_tag(v___x_780_) == 0)
{
lean_object* v___x_781_; 
lean_dec(v_val_779_);
lean_dec_ref(v_builder_774_);
v___x_781_ = lean_box(0);
return v___x_781_;
}
else
{
lean_object* v_line_782_; lean_object* v_headers_783_; lean_object* v_val_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_823_; 
v_line_782_ = lean_ctor_get(v_builder_774_, 0);
lean_inc_ref(v_line_782_);
v_headers_783_ = lean_ctor_get(v_line_782_, 1);
lean_inc_ref(v_headers_783_);
v_val_784_ = lean_ctor_get(v___x_780_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_823_ == 0)
{
v___x_786_ = v___x_780_;
v_isShared_787_ = v_isSharedCheck_823_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_val_784_);
lean_dec(v___x_780_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_823_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v_extensions_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_821_; 
v_extensions_788_ = lean_ctor_get(v_builder_774_, 1);
v_isSharedCheck_821_ = !lean_is_exclusive(v_builder_774_);
if (v_isSharedCheck_821_ == 0)
{
lean_object* v_unused_822_; 
v_unused_822_ = lean_ctor_get(v_builder_774_, 0);
lean_dec(v_unused_822_);
v___x_790_ = v_builder_774_;
v_isShared_791_ = v_isSharedCheck_821_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_extensions_788_);
lean_dec(v_builder_774_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_821_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v_status_792_; uint8_t v_version_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_819_; 
v_status_792_ = lean_ctor_get(v_line_782_, 0);
v_version_793_ = lean_ctor_get_uint8(v_line_782_, sizeof(void*)*2);
v_isSharedCheck_819_ = !lean_is_exclusive(v_line_782_);
if (v_isSharedCheck_819_ == 0)
{
lean_object* v_unused_820_; 
v_unused_820_ = lean_ctor_get(v_line_782_, 1);
lean_dec(v_unused_820_);
v___x_795_ = v_line_782_;
v_isShared_796_ = v_isSharedCheck_819_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_status_792_);
lean_dec(v_line_782_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_819_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v_entries_797_; lean_object* v_indexes_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_818_; 
v_entries_797_ = lean_ctor_get(v_headers_783_, 0);
v_indexes_798_ = lean_ctor_get(v_headers_783_, 1);
v_isSharedCheck_818_ = !lean_is_exclusive(v_headers_783_);
if (v_isSharedCheck_818_ == 0)
{
v___x_800_ = v_headers_783_;
v_isShared_801_ = v_isSharedCheck_818_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_indexes_798_);
lean_inc(v_entries_797_);
lean_dec(v_headers_783_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_818_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v_i_802_; lean_object* v___x_803_; lean_object* v_entries_804_; lean_object* v_indexes_805_; lean_object* v___x_807_; 
v_i_802_ = lean_array_get_size(v_entries_797_);
lean_inc(v_val_779_);
v___x_803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_803_, 0, v_val_779_);
lean_ctor_set(v___x_803_, 1, v_val_784_);
v_entries_804_ = lean_array_push(v_entries_797_, v___x_803_);
v_indexes_805_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0(v_i_802_, v_indexes_798_, v_val_779_);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 1, v_indexes_805_);
lean_ctor_set(v___x_800_, 0, v_entries_804_);
v___x_807_ = v___x_800_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_entries_804_);
lean_ctor_set(v_reuseFailAlloc_817_, 1, v_indexes_805_);
v___x_807_ = v_reuseFailAlloc_817_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
lean_object* v___x_809_; 
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 1, v___x_807_);
v___x_809_ = v___x_795_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_status_792_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v___x_807_);
lean_ctor_set_uint8(v_reuseFailAlloc_816_, sizeof(void*)*2, v_version_793_);
v___x_809_ = v_reuseFailAlloc_816_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
lean_object* v___x_811_; 
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 0, v___x_809_);
v___x_811_ = v___x_790_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v___x_809_);
lean_ctor_set(v_reuseFailAlloc_815_, 1, v_extensions_788_);
v___x_811_ = v_reuseFailAlloc_815_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
lean_object* v___x_813_; 
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 0, v___x_811_);
v___x_813_ = v___x_786_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v___x_811_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
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
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_extension___redArg(lean_object* v_builder_825_, lean_object* v_inst_826_, lean_object* v_data_827_){
_start:
{
lean_object* v_line_828_; lean_object* v_extensions_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_840_; 
v_line_828_ = lean_ctor_get(v_builder_825_, 0);
v_extensions_829_ = lean_ctor_get(v_builder_825_, 1);
v_isSharedCheck_840_ = !lean_is_exclusive(v_builder_825_);
if (v_isSharedCheck_840_ == 0)
{
v___x_831_ = v_builder_825_;
v_isShared_832_ = v_isSharedCheck_840_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_extensions_829_);
lean_inc(v_line_828_);
lean_dec(v_builder_825_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_840_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v_dyn_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_838_; 
v_dyn_833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_dyn_833_, 0, v_inst_826_);
lean_ctor_set(v_dyn_833_, 1, v_data_827_);
v___x_834_ = ((lean_object*)(l_Std_Http_Response_Builder_extension___redArg___closed__0));
v___x_835_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_dyn_833_);
v___x_836_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_834_, v___x_835_, v_dyn_833_, v_extensions_829_);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 1, v___x_836_);
v___x_838_ = v___x_831_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_line_828_);
lean_ctor_set(v_reuseFailAlloc_839_, 1, v___x_836_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_extension(lean_object* v_00_u03b1_841_, lean_object* v_builder_842_, lean_object* v_inst_843_, lean_object* v_data_844_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = l_Std_Http_Response_Builder_extension___redArg(v_builder_842_, v_inst_843_, v_data_844_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_body___redArg(lean_object* v_builder_846_, lean_object* v_body_847_){
_start:
{
lean_object* v_line_848_; lean_object* v_extensions_849_; lean_object* v___x_850_; 
v_line_848_ = lean_ctor_get(v_builder_846_, 0);
v_extensions_849_ = lean_ctor_get(v_builder_846_, 1);
lean_inc(v_extensions_849_);
lean_inc_ref(v_line_848_);
v___x_850_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_850_, 0, v_line_848_);
lean_ctor_set(v___x_850_, 1, v_body_847_);
lean_ctor_set(v___x_850_, 2, v_extensions_849_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_body___redArg___boxed(lean_object* v_builder_851_, lean_object* v_body_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Std_Http_Response_Builder_body___redArg(v_builder_851_, v_body_852_);
lean_dec_ref(v_builder_851_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_body(lean_object* v_t_854_, lean_object* v_builder_855_, lean_object* v_body_856_){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = l_Std_Http_Response_Builder_body___redArg(v_builder_855_, v_body_856_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_body___boxed(lean_object* v_t_858_, lean_object* v_builder_859_, lean_object* v_body_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_Std_Http_Response_Builder_body(v_t_858_, v_builder_859_, v_body_860_);
lean_dec_ref(v_builder_859_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_build___redArg(lean_object* v_inst_862_, lean_object* v_builder_863_){
_start:
{
lean_object* v_line_864_; lean_object* v_extensions_865_; lean_object* v___x_866_; 
v_line_864_ = lean_ctor_get(v_builder_863_, 0);
v_extensions_865_ = lean_ctor_get(v_builder_863_, 1);
lean_inc(v_extensions_865_);
lean_inc_ref(v_line_864_);
v___x_866_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_866_, 0, v_line_864_);
lean_ctor_set(v___x_866_, 1, v_inst_862_);
lean_ctor_set(v___x_866_, 2, v_extensions_865_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_build___redArg___boxed(lean_object* v_inst_867_, lean_object* v_builder_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_Std_Http_Response_Builder_build___redArg(v_inst_867_, v_builder_868_);
lean_dec_ref(v_builder_868_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_build(lean_object* v_t_870_, lean_object* v_inst_871_, lean_object* v_builder_872_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = l_Std_Http_Response_Builder_build___redArg(v_inst_871_, v_builder_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_build___boxed(lean_object* v_t_874_, lean_object* v_inst_875_, lean_object* v_builder_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l_Std_Http_Response_Builder_build(v_t_874_, v_inst_875_, v_builder_876_);
lean_dec_ref(v_builder_876_);
return v_res_877_;
}
}
static lean_object* _init_l_Std_Http_Response_ok___closed__0(void){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_878_ = lean_box(4);
v___x_879_ = l_Std_Http_Response_Builder_new;
v___x_880_ = l_Std_Http_Response_Builder_status(v___x_879_, v___x_878_);
return v___x_880_;
}
}
static lean_object* _init_l_Std_Http_Response_ok(void){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = lean_obj_once(&l_Std_Http_Response_ok___closed__0, &l_Std_Http_Response_ok___closed__0_once, _init_l_Std_Http_Response_ok___closed__0);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_withStatus(lean_object* v_status_882_){
_start:
{
lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_883_ = l_Std_Http_Response_Builder_new;
v___x_884_ = l_Std_Http_Response_Builder_status(v___x_883_, v_status_882_);
return v___x_884_;
}
}
static lean_object* _init_l_Std_Http_Response_notFound___closed__0(void){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_885_ = lean_box(27);
v___x_886_ = l_Std_Http_Response_Builder_new;
v___x_887_ = l_Std_Http_Response_Builder_status(v___x_886_, v___x_885_);
return v___x_887_;
}
}
static lean_object* _init_l_Std_Http_Response_notFound(void){
_start:
{
lean_object* v___x_888_; 
v___x_888_ = lean_obj_once(&l_Std_Http_Response_notFound___closed__0, &l_Std_Http_Response_notFound___closed__0_once, _init_l_Std_Http_Response_notFound___closed__0);
return v___x_888_;
}
}
static lean_object* _init_l_Std_Http_Response_internalServerError___closed__0(void){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_889_ = lean_box(52);
v___x_890_ = l_Std_Http_Response_Builder_new;
v___x_891_ = l_Std_Http_Response_Builder_status(v___x_890_, v___x_889_);
return v___x_891_;
}
}
static lean_object* _init_l_Std_Http_Response_internalServerError(void){
_start:
{
lean_object* v___x_892_; 
v___x_892_ = lean_obj_once(&l_Std_Http_Response_internalServerError___closed__0, &l_Std_Http_Response_internalServerError___closed__0_once, _init_l_Std_Http_Response_internalServerError___closed__0);
return v___x_892_;
}
}
static lean_object* _init_l_Std_Http_Response_badRequest___closed__0(void){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_893_ = lean_box(23);
v___x_894_ = l_Std_Http_Response_Builder_new;
v___x_895_ = l_Std_Http_Response_Builder_status(v___x_894_, v___x_893_);
return v___x_895_;
}
}
static lean_object* _init_l_Std_Http_Response_badRequest(void){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = lean_obj_once(&l_Std_Http_Response_badRequest___closed__0, &l_Std_Http_Response_badRequest___closed__0_once, _init_l_Std_Http_Response_badRequest___closed__0);
return v___x_896_;
}
}
static lean_object* _init_l_Std_Http_Response_created___closed__0(void){
_start:
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_897_ = lean_box(5);
v___x_898_ = l_Std_Http_Response_Builder_new;
v___x_899_ = l_Std_Http_Response_Builder_status(v___x_898_, v___x_897_);
return v___x_899_;
}
}
static lean_object* _init_l_Std_Http_Response_created(void){
_start:
{
lean_object* v___x_900_; 
v___x_900_ = lean_obj_once(&l_Std_Http_Response_created___closed__0, &l_Std_Http_Response_created___closed__0_once, _init_l_Std_Http_Response_created___closed__0);
return v___x_900_;
}
}
static lean_object* _init_l_Std_Http_Response_accepted___closed__0(void){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_901_ = lean_box(6);
v___x_902_ = l_Std_Http_Response_Builder_new;
v___x_903_ = l_Std_Http_Response_Builder_status(v___x_902_, v___x_901_);
return v___x_903_;
}
}
static lean_object* _init_l_Std_Http_Response_accepted(void){
_start:
{
lean_object* v___x_904_; 
v___x_904_ = lean_obj_once(&l_Std_Http_Response_accepted___closed__0, &l_Std_Http_Response_accepted___closed__0_once, _init_l_Std_Http_Response_accepted___closed__0);
return v___x_904_;
}
}
static lean_object* _init_l_Std_Http_Response_unauthorized___closed__0(void){
_start:
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_905_ = lean_box(24);
v___x_906_ = l_Std_Http_Response_Builder_new;
v___x_907_ = l_Std_Http_Response_Builder_status(v___x_906_, v___x_905_);
return v___x_907_;
}
}
static lean_object* _init_l_Std_Http_Response_unauthorized(void){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = lean_obj_once(&l_Std_Http_Response_unauthorized___closed__0, &l_Std_Http_Response_unauthorized___closed__0_once, _init_l_Std_Http_Response_unauthorized___closed__0);
return v___x_908_;
}
}
static lean_object* _init_l_Std_Http_Response_forbidden___closed__0(void){
_start:
{
lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_909_ = lean_box(26);
v___x_910_ = l_Std_Http_Response_Builder_new;
v___x_911_ = l_Std_Http_Response_Builder_status(v___x_910_, v___x_909_);
return v___x_911_;
}
}
static lean_object* _init_l_Std_Http_Response_forbidden(void){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = lean_obj_once(&l_Std_Http_Response_forbidden___closed__0, &l_Std_Http_Response_forbidden___closed__0_once, _init_l_Std_Http_Response_forbidden___closed__0);
return v___x_912_;
}
}
static lean_object* _init_l_Std_Http_Response_conflict___closed__0(void){
_start:
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_913_ = lean_box(32);
v___x_914_ = l_Std_Http_Response_Builder_new;
v___x_915_ = l_Std_Http_Response_Builder_status(v___x_914_, v___x_913_);
return v___x_915_;
}
}
static lean_object* _init_l_Std_Http_Response_conflict(void){
_start:
{
lean_object* v___x_916_; 
v___x_916_ = lean_obj_once(&l_Std_Http_Response_conflict___closed__0, &l_Std_Http_Response_conflict___closed__0_once, _init_l_Std_Http_Response_conflict___closed__0);
return v___x_916_;
}
}
static lean_object* _init_l_Std_Http_Response_serviceUnavailable___closed__0(void){
_start:
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_917_ = lean_box(55);
v___x_918_ = l_Std_Http_Response_Builder_new;
v___x_919_ = l_Std_Http_Response_Builder_status(v___x_918_, v___x_917_);
return v___x_919_;
}
}
static lean_object* _init_l_Std_Http_Response_serviceUnavailable(void){
_start:
{
lean_object* v___x_920_; 
v___x_920_ = lean_obj_once(&l_Std_Http_Response_serviceUnavailable___closed__0, &l_Std_Http_Response_serviceUnavailable___closed__0_once, _init_l_Std_Http_Response_serviceUnavailable___closed__0);
return v___x_920_;
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
