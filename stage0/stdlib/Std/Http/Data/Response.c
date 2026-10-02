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
lean_object* v_it_117_; lean_object* v_out_118_; uint32_t v___y_134_; lean_object* v___y_135_; lean_object* v___y_136_; uint8_t v___y_137_; lean_object* v_it_143_; lean_object* v_startInclusive_144_; lean_object* v_endExclusive_145_; 
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
v___x_138_ = lean_string_utf8_set(v___y_135_, v___x_106_, v___y_134_);
v_it_117_ = v___y_136_;
v_out_118_ = v___x_138_;
goto v___jp_116_;
}
else
{
uint32_t v___x_139_; uint32_t v___x_140_; lean_object* v___x_141_; 
v___x_139_ = 4294967264;
v___x_140_ = lean_uint32_add(v___y_134_, v___x_139_);
v___x_141_ = lean_string_utf8_set(v___y_135_, v___x_106_, v___x_140_);
v_it_117_ = v___y_136_;
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
v___y_134_ = v___x_147_;
v___y_135_ = v___x_146_;
v___y_136_ = v_it_143_;
v___y_137_ = v___x_149_;
goto v___jp_133_;
}
else
{
uint32_t v___x_150_; uint8_t v___x_151_; 
v___x_150_ = 122;
v___x_151_ = lean_uint32_dec_le(v___x_147_, v___x_150_);
v___y_134_ = v___x_147_;
v___y_135_ = v___x_146_;
v___y_136_ = v_it_143_;
v___y_137_ = v___x_151_;
goto v___jp_133_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instToStringHead___lam__0___boxed(lean_object* v___x_176_, lean_object* v___x_177_, lean_object* v___x_178_, lean_object* v_fst_179_, lean_object* v___x_180_, lean_object* v___x_181_, lean_object* v___x_182_, lean_object* v_it_183_, lean_object* v_acc_184_, lean_object* v_hP_185_, lean_object* v_recur_186_){
_start:
{
uint32_t v___x_792__boxed_187_; lean_object* v_res_188_; 
v___x_792__boxed_187_ = lean_unbox_uint32(v___x_181_);
lean_dec(v___x_181_);
v_res_188_ = l_Std_Http_Response_instToStringHead___lam__0(v___x_176_, v___x_177_, v___x_178_, v_fst_179_, v___x_180_, v___x_792__boxed_187_, v___x_182_, v_it_183_, v_acc_184_, v_hP_185_, v_recur_186_);
lean_dec_ref(v___x_182_);
lean_dec_ref(v_fst_179_);
lean_dec(v___x_178_);
lean_dec(v___x_177_);
lean_dec_ref(v___x_176_);
return v_res_188_;
}
}
static lean_object* _init_l_Std_Http_Response_instToStringHead___lam__1___boxed__const__1(void){
_start:
{
uint32_t v___x_193_; lean_object* v___x_194_; 
v___x_193_ = 45;
v___x_194_ = lean_box_uint32(v___x_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instToStringHead___lam__1(lean_object* v_x_195_){
_start:
{
lean_object* v_fst_196_; lean_object* v_snd_197_; lean_object* v___y_199_; lean_object* v___f_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v_it_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___f_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v_fst_196_ = lean_ctor_get(v_x_195_, 0);
lean_inc_n(v_fst_196_, 2);
v_snd_197_ = lean_ctor_get(v_x_195_, 1);
lean_inc(v_snd_197_);
lean_dec_ref(v_x_195_);
v___f_203_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__1___closed__1));
v___x_204_ = lean_unsigned_to_nat(0u);
v___x_205_ = lean_string_utf8_byte_size(v_fst_196_);
v___x_206_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_206_, 0, v_fst_196_);
lean_ctor_set(v___x_206_, 1, v___x_204_);
lean_ctor_set(v___x_206_, 2, v___x_205_);
lean_inc_ref(v___x_206_);
v_it_207_ = l_String_Slice_splitToSubslice___redArg(v___x_206_, v___f_203_);
v___x_208_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__1___closed__2));
v___x_209_ = lean_unsigned_to_nat(1u);
v___x_210_ = l_Std_Http_Response_instToStringHead___lam__1___boxed__const__1;
v___f_211_ = lean_alloc_closure((void*)(l_Std_Http_Response_instToStringHead___lam__0___boxed), 11, 7);
lean_closure_set(v___f_211_, 0, v___x_208_);
lean_closure_set(v___f_211_, 1, v___x_204_);
lean_closure_set(v___f_211_, 2, v___x_209_);
lean_closure_set(v___f_211_, 3, v_fst_196_);
lean_closure_set(v___f_211_, 4, v___x_205_);
lean_closure_set(v___f_211_, 5, v___x_210_);
lean_closure_set(v___f_211_, 6, v___x_206_);
v___x_212_ = lean_box(0);
v___x_213_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_211_, v_it_207_, v___x_212_, lean_box(0));
if (lean_obj_tag(v___x_213_) == 0)
{
lean_object* v___x_214_; 
v___x_214_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__1___closed__3));
v___y_199_ = v___x_214_;
goto v___jp_198_;
}
else
{
lean_object* v_val_215_; 
v_val_215_ = lean_ctor_get(v___x_213_, 0);
lean_inc(v_val_215_);
lean_dec_ref_known(v___x_213_, 1);
v___y_199_ = v_val_215_;
goto v___jp_198_;
}
v___jp_198_:
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_200_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__1___closed__0));
v___x_201_ = lean_string_append(v___y_199_, v___x_200_);
v___x_202_ = lean_string_append(v___x_201_, v_snd_197_);
lean_dec(v_snd_197_);
return v___x_202_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instToStringHead___lam__2(lean_object* v___f_241_, lean_object* v_r_242_){
_start:
{
lean_object* v_status_243_; uint8_t v_version_244_; lean_object* v_headers_245_; lean_object* v___y_247_; 
v_status_243_ = lean_ctor_get(v_r_242_, 0);
lean_inc(v_status_243_);
v_version_244_ = lean_ctor_get_uint8(v_r_242_, sizeof(void*)*2);
v_headers_245_ = lean_ctor_get(v_r_242_, 1);
lean_inc_ref(v_headers_245_);
lean_dec_ref(v_r_242_);
switch(v_version_244_)
{
case 0:
{
lean_object* v___x_268_; 
v___x_268_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__12));
v___y_247_ = v___x_268_;
goto v___jp_246_;
}
case 1:
{
lean_object* v___x_269_; 
v___x_269_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__13));
v___y_247_ = v___x_269_;
goto v___jp_246_;
}
case 2:
{
lean_object* v___x_270_; 
v___x_270_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__14));
v___y_247_ = v___x_270_;
goto v___jp_246_;
}
default: 
{
lean_object* v___x_271_; 
v___x_271_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__15));
v___y_247_ = v___x_271_;
goto v___jp_246_;
}
}
v___jp_246_:
{
lean_object* v_entries_248_; lean_object* v___x_249_; lean_object* v___x_250_; uint16_t v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; size_t v_sz_261_; size_t v___x_262_; lean_object* v_pairs_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v_entries_248_ = lean_ctor_get(v_headers_245_, 0);
lean_inc_ref(v_entries_248_);
lean_dec_ref(v_headers_245_);
v___x_249_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__0));
lean_inc_ref(v___y_247_);
v___x_250_ = lean_string_append(v___y_247_, v___x_249_);
v___x_251_ = l_Std_Http_Status_toCode(v_status_243_);
v___x_252_ = lean_uint16_to_nat(v___x_251_);
v___x_253_ = l_Nat_reprFast(v___x_252_);
v___x_254_ = lean_string_append(v___x_250_, v___x_253_);
lean_dec_ref(v___x_253_);
v___x_255_ = lean_string_append(v___x_254_, v___x_249_);
v___x_256_ = l_Std_Http_Status_reasonPhrase(v_status_243_);
lean_dec(v_status_243_);
v___x_257_ = lean_string_append(v___x_255_, v___x_256_);
lean_dec_ref(v___x_256_);
v___x_258_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__1));
v___x_259_ = lean_string_append(v___x_257_, v___x_258_);
v___x_260_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__11));
v_sz_261_ = lean_array_size(v_entries_248_);
v___x_262_ = ((size_t)0ULL);
v_pairs_263_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_260_, v___f_241_, v_sz_261_, v___x_262_, v_entries_248_);
v___x_264_ = lean_array_to_list(v_pairs_263_);
v___x_265_ = l_String_intercalate(v___x_258_, v___x_264_);
v___x_266_ = lean_string_append(v___x_259_, v___x_265_);
lean_dec_ref(v___x_265_);
v___x_267_ = lean_string_append(v___x_266_, v___x_258_);
return v___x_267_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instEncodeV11Head___lam__0(lean_object* v___x_276_, lean_object* v___x_277_, lean_object* v___x_278_, lean_object* v_name_279_, lean_object* v___x_280_, uint32_t v___x_281_, lean_object* v___x_282_, lean_object* v_it_283_, lean_object* v_acc_284_, lean_object* v_hP_285_, lean_object* v_recur_286_){
_start:
{
lean_object* v_it_288_; lean_object* v_out_289_; lean_object* v___y_305_; lean_object* v___y_306_; uint32_t v___y_307_; uint8_t v___y_308_; lean_object* v_it_314_; lean_object* v_startInclusive_315_; lean_object* v_endExclusive_316_; 
if (lean_obj_tag(v_it_283_) == 0)
{
lean_object* v_currPos_323_; lean_object* v_searcher_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_346_; 
v_currPos_323_ = lean_ctor_get(v_it_283_, 0);
v_searcher_324_ = lean_ctor_get(v_it_283_, 1);
v_isSharedCheck_346_ = !lean_is_exclusive(v_it_283_);
if (v_isSharedCheck_346_ == 0)
{
v___x_326_ = v_it_283_;
v_isShared_327_ = v_isSharedCheck_346_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_searcher_324_);
lean_inc(v_currPos_323_);
lean_dec(v_it_283_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_346_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
uint8_t v_decide_328_; 
v_decide_328_ = lean_nat_dec_eq(v_searcher_324_, v___x_280_);
if (v_decide_328_ == 0)
{
uint32_t v___x_329_; uint8_t v___x_330_; 
lean_dec(v___x_280_);
v___x_329_ = lean_string_utf8_get_fast(v_name_279_, v_searcher_324_);
v___x_330_ = lean_uint32_dec_eq(v___x_329_, v___x_281_);
if (v___x_330_ == 0)
{
lean_object* v___x_331_; lean_object* v___x_333_; 
v___x_331_ = lean_string_utf8_next_fast(v_name_279_, v_searcher_324_);
lean_dec(v_searcher_324_);
if (v_isShared_327_ == 0)
{
lean_ctor_set(v___x_326_, 1, v___x_331_);
v___x_333_ = v___x_326_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v_currPos_323_);
lean_ctor_set(v_reuseFailAlloc_335_, 1, v___x_331_);
v___x_333_ = v_reuseFailAlloc_335_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
lean_object* v___x_334_; 
v___x_334_ = lean_apply_4(v_recur_286_, v___x_333_, v_acc_284_, lean_box(0), lean_box(0));
return v___x_334_;
}
}
else
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v_slice_339_; lean_object* v_nextIt_341_; 
v___x_336_ = lean_string_utf8_next_fast(v_name_279_, v_searcher_324_);
v___x_337_ = lean_nat_sub(v___x_336_, v_searcher_324_);
v___x_338_ = lean_nat_add(v_searcher_324_, v___x_337_);
lean_dec(v___x_337_);
v_slice_339_ = l_String_Slice_subslice_x21(v___x_282_, v_currPos_323_, v_searcher_324_);
lean_inc(v___x_338_);
if (v_isShared_327_ == 0)
{
lean_ctor_set(v___x_326_, 1, v___x_338_);
lean_ctor_set(v___x_326_, 0, v___x_338_);
v_nextIt_341_ = v___x_326_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v___x_338_);
lean_ctor_set(v_reuseFailAlloc_344_, 1, v___x_338_);
v_nextIt_341_ = v_reuseFailAlloc_344_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
lean_object* v_startInclusive_342_; lean_object* v_endExclusive_343_; 
v_startInclusive_342_ = lean_ctor_get(v_slice_339_, 0);
lean_inc(v_startInclusive_342_);
v_endExclusive_343_ = lean_ctor_get(v_slice_339_, 1);
lean_inc(v_endExclusive_343_);
lean_dec_ref(v_slice_339_);
v_it_314_ = v_nextIt_341_;
v_startInclusive_315_ = v_startInclusive_342_;
v_endExclusive_316_ = v_endExclusive_343_;
goto v___jp_313_;
}
}
}
else
{
lean_object* v___x_345_; 
lean_del_object(v___x_326_);
lean_dec(v_searcher_324_);
v___x_345_ = lean_box(1);
v_it_314_ = v___x_345_;
v_startInclusive_315_ = v_currPos_323_;
v_endExclusive_316_ = v___x_280_;
goto v___jp_313_;
}
}
}
else
{
lean_dec_ref(v_recur_286_);
lean_dec(v___x_280_);
return v_acc_284_;
}
v___jp_287_:
{
if (lean_obj_tag(v_acc_284_) == 0)
{
lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_290_, 0, v_out_289_);
v___x_291_ = lean_apply_4(v_recur_286_, v_it_288_, v___x_290_, lean_box(0), lean_box(0));
return v___x_291_;
}
else
{
lean_object* v_val_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_303_; 
v_val_292_ = lean_ctor_get(v_acc_284_, 0);
v_isSharedCheck_303_ = !lean_is_exclusive(v_acc_284_);
if (v_isSharedCheck_303_ == 0)
{
v___x_294_ = v_acc_284_;
v_isShared_295_ = v_isSharedCheck_303_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_val_292_);
lean_dec(v_acc_284_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_303_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_300_; 
v___x_296_ = lean_string_utf8_extract_fast(v___x_276_, v___x_277_, v___x_278_);
v___x_297_ = lean_string_append(v_val_292_, v___x_296_);
lean_dec_ref(v___x_296_);
v___x_298_ = lean_string_append(v___x_297_, v_out_289_);
lean_dec_ref(v_out_289_);
if (v_isShared_295_ == 0)
{
lean_ctor_set(v___x_294_, 0, v___x_298_);
v___x_300_ = v___x_294_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v___x_298_);
v___x_300_ = v_reuseFailAlloc_302_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
lean_object* v___x_301_; 
v___x_301_ = lean_apply_4(v_recur_286_, v_it_288_, v___x_300_, lean_box(0), lean_box(0));
return v___x_301_;
}
}
}
}
v___jp_304_:
{
if (v___y_308_ == 0)
{
lean_object* v___x_309_; 
v___x_309_ = lean_string_utf8_set(v___y_305_, v___x_277_, v___y_307_);
v_it_288_ = v___y_306_;
v_out_289_ = v___x_309_;
goto v___jp_287_;
}
else
{
uint32_t v___x_310_; uint32_t v___x_311_; lean_object* v___x_312_; 
v___x_310_ = 4294967264;
v___x_311_ = lean_uint32_add(v___y_307_, v___x_310_);
v___x_312_ = lean_string_utf8_set(v___y_305_, v___x_277_, v___x_311_);
v_it_288_ = v___y_306_;
v_out_289_ = v___x_312_;
goto v___jp_287_;
}
}
v___jp_313_:
{
lean_object* v___x_317_; uint32_t v___x_318_; uint32_t v___x_319_; uint8_t v___x_320_; 
v___x_317_ = lean_string_utf8_extract_fast(v_name_279_, v_startInclusive_315_, v_endExclusive_316_);
lean_dec(v_endExclusive_316_);
lean_dec(v_startInclusive_315_);
v___x_318_ = lean_string_utf8_get(v___x_317_, v___x_277_);
v___x_319_ = 97;
v___x_320_ = lean_uint32_dec_le(v___x_319_, v___x_318_);
if (v___x_320_ == 0)
{
v___y_305_ = v___x_317_;
v___y_306_ = v_it_314_;
v___y_307_ = v___x_318_;
v___y_308_ = v___x_320_;
goto v___jp_304_;
}
else
{
uint32_t v___x_321_; uint8_t v___x_322_; 
v___x_321_ = 122;
v___x_322_ = lean_uint32_dec_le(v___x_318_, v___x_321_);
v___y_305_ = v___x_317_;
v___y_306_ = v_it_314_;
v___y_307_ = v___x_318_;
v___y_308_ = v___x_322_;
goto v___jp_304_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instEncodeV11Head___lam__0___boxed(lean_object* v___x_347_, lean_object* v___x_348_, lean_object* v___x_349_, lean_object* v_name_350_, lean_object* v___x_351_, lean_object* v___x_352_, lean_object* v___x_353_, lean_object* v_it_354_, lean_object* v_acc_355_, lean_object* v_hP_356_, lean_object* v_recur_357_){
_start:
{
uint32_t v___x_1263__boxed_358_; lean_object* v_res_359_; 
v___x_1263__boxed_358_ = lean_unbox_uint32(v___x_352_);
lean_dec(v___x_352_);
v_res_359_ = l_Std_Http_Response_instEncodeV11Head___lam__0(v___x_347_, v___x_348_, v___x_349_, v_name_350_, v___x_351_, v___x_1263__boxed_358_, v___x_353_, v_it_354_, v_acc_355_, v_hP_356_, v_recur_357_);
lean_dec_ref(v___x_353_);
lean_dec_ref(v_name_350_);
lean_dec(v___x_349_);
lean_dec(v___x_348_);
lean_dec_ref(v___x_347_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instEncodeV11Head___lam__1(lean_object* v_buf_360_, lean_object* v_name_361_, lean_object* v_value_362_){
_start:
{
lean_object* v___y_364_; lean_object* v___f_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v_it_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___f_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v___f_383_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__1___closed__1));
v___x_384_ = lean_unsigned_to_nat(0u);
v___x_385_ = lean_string_utf8_byte_size(v_name_361_);
lean_inc_ref(v_name_361_);
v___x_386_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_386_, 0, v_name_361_);
lean_ctor_set(v___x_386_, 1, v___x_384_);
lean_ctor_set(v___x_386_, 2, v___x_385_);
lean_inc_ref(v___x_386_);
v_it_387_ = l_String_Slice_splitToSubslice___redArg(v___x_386_, v___f_383_);
v___x_388_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__1___closed__2));
v___x_389_ = lean_unsigned_to_nat(1u);
v___x_390_ = l_Std_Http_Response_instToStringHead___lam__1___boxed__const__1;
v___f_391_ = lean_alloc_closure((void*)(l_Std_Http_Response_instEncodeV11Head___lam__0___boxed), 11, 7);
lean_closure_set(v___f_391_, 0, v___x_388_);
lean_closure_set(v___f_391_, 1, v___x_384_);
lean_closure_set(v___f_391_, 2, v___x_389_);
lean_closure_set(v___f_391_, 3, v_name_361_);
lean_closure_set(v___f_391_, 4, v___x_385_);
lean_closure_set(v___f_391_, 5, v___x_390_);
lean_closure_set(v___f_391_, 6, v___x_386_);
v___x_392_ = lean_box(0);
v___x_393_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_391_, v_it_387_, v___x_392_, lean_box(0));
if (lean_obj_tag(v___x_393_) == 0)
{
lean_object* v___x_394_; 
v___x_394_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__1___closed__3));
v___y_364_ = v___x_394_;
goto v___jp_363_;
}
else
{
lean_object* v_val_395_; 
v_val_395_ = lean_ctor_get(v___x_393_, 0);
lean_inc(v_val_395_);
lean_dec_ref_known(v___x_393_, 1);
v___y_364_ = v_val_395_;
goto v___jp_363_;
}
v___jp_363_:
{
lean_object* v_data_365_; lean_object* v_size_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_382_; 
v_data_365_ = lean_ctor_get(v_buf_360_, 0);
v_size_366_ = lean_ctor_get(v_buf_360_, 1);
v_isSharedCheck_382_ = !lean_is_exclusive(v_buf_360_);
if (v_isSharedCheck_382_ == 0)
{
v___x_368_ = v_buf_360_;
v_isShared_369_ = v_isSharedCheck_382_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_size_366_);
lean_inc(v_data_365_);
lean_dec(v_buf_360_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_382_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_380_; 
v___x_370_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__1___closed__0));
v___x_371_ = lean_string_append(v___y_364_, v___x_370_);
v___x_372_ = lean_string_append(v___x_371_, v_value_362_);
v___x_373_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__1));
v___x_374_ = lean_string_append(v___x_372_, v___x_373_);
v___x_375_ = lean_string_to_utf8(v___x_374_);
lean_dec_ref(v___x_374_);
lean_inc_ref(v___x_375_);
v___x_376_ = lean_array_push(v_data_365_, v___x_375_);
v___x_377_ = lean_byte_array_size(v___x_375_);
lean_dec_ref(v___x_375_);
v___x_378_ = lean_nat_add(v_size_366_, v___x_377_);
lean_dec(v_size_366_);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 1, v___x_378_);
lean_ctor_set(v___x_368_, 0, v___x_376_);
v___x_380_ = v___x_368_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v___x_376_);
lean_ctor_set(v_reuseFailAlloc_381_, 1, v___x_378_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instEncodeV11Head___lam__1___boxed(lean_object* v_buf_396_, lean_object* v_name_397_, lean_object* v_value_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_Std_Http_Response_instEncodeV11Head___lam__1(v_buf_396_, v_name_397_, v_value_398_);
lean_dec_ref(v_value_398_);
return v_res_399_;
}
}
static lean_object* _init_l_Std_Http_Response_instEncodeV11Head___lam__2___closed__1(void){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_406_ = ((lean_object*)(l_Std_Http_Response_instEncodeV11Head___lam__2___closed__0));
v___x_407_ = lean_byte_array_size(v___x_406_);
return v___x_407_;
}
}
static lean_object* _init_l_Std_Http_Response_instEncodeV11Head___lam__2___closed__2(void){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_408_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__1));
v___x_409_ = lean_string_to_utf8(v___x_408_);
return v___x_409_;
}
}
static lean_object* _init_l_Std_Http_Response_instEncodeV11Head___lam__2___closed__3(void){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_410_ = lean_obj_once(&l_Std_Http_Response_instEncodeV11Head___lam__2___closed__2, &l_Std_Http_Response_instEncodeV11Head___lam__2___closed__2_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__2___closed__2);
v___x_411_ = lean_byte_array_size(v___x_410_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instEncodeV11Head___lam__2(lean_object* v___f_412_, lean_object* v_buffer_413_, lean_object* v_r_414_){
_start:
{
lean_object* v_status_415_; uint8_t v_version_416_; lean_object* v_headers_417_; lean_object* v___y_419_; 
v_status_415_ = lean_ctor_get(v_r_414_, 0);
v_version_416_ = lean_ctor_get_uint8(v_r_414_, sizeof(void*)*2);
v_headers_417_ = lean_ctor_get(v_r_414_, 1);
switch(v_version_416_)
{
case 0:
{
lean_object* v___x_467_; 
v___x_467_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__12));
v___y_419_ = v___x_467_;
goto v___jp_418_;
}
case 1:
{
lean_object* v___x_468_; 
v___x_468_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__13));
v___y_419_ = v___x_468_;
goto v___jp_418_;
}
case 2:
{
lean_object* v___x_469_; 
v___x_469_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__14));
v___y_419_ = v___x_469_;
goto v___jp_418_;
}
default: 
{
lean_object* v___x_470_; 
v___x_470_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__15));
v___y_419_ = v___x_470_;
goto v___jp_418_;
}
}
v___jp_418_:
{
lean_object* v_data_420_; lean_object* v_size_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_466_; 
v_data_420_ = lean_ctor_get(v_buffer_413_, 0);
v_size_421_ = lean_ctor_get(v_buffer_413_, 1);
v_isSharedCheck_466_ = !lean_is_exclusive(v_buffer_413_);
if (v_isSharedCheck_466_ == 0)
{
v___x_423_ = v_buffer_413_;
v_isShared_424_ = v_isSharedCheck_466_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_size_421_);
lean_inc(v_data_420_);
lean_dec(v_buffer_413_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_466_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; uint16_t v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v_buffer_452_; 
v___x_425_ = lean_string_to_utf8(v___y_419_);
lean_inc_ref(v___x_425_);
v___x_426_ = lean_array_push(v_data_420_, v___x_425_);
v___x_427_ = lean_byte_array_size(v___x_425_);
lean_dec_ref(v___x_425_);
v___x_428_ = lean_nat_add(v_size_421_, v___x_427_);
lean_dec(v_size_421_);
v___x_429_ = ((lean_object*)(l_Std_Http_Response_instEncodeV11Head___lam__2___closed__0));
v___x_430_ = lean_array_push(v___x_426_, v___x_429_);
v___x_431_ = lean_obj_once(&l_Std_Http_Response_instEncodeV11Head___lam__2___closed__1, &l_Std_Http_Response_instEncodeV11Head___lam__2___closed__1_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__2___closed__1);
v___x_432_ = lean_nat_add(v___x_428_, v___x_431_);
lean_dec(v___x_428_);
v___x_433_ = l_Std_Http_Status_toCode(v_status_415_);
v___x_434_ = lean_uint16_to_nat(v___x_433_);
v___x_435_ = l_Nat_reprFast(v___x_434_);
v___x_436_ = lean_string_to_utf8(v___x_435_);
lean_dec_ref(v___x_435_);
lean_inc_ref(v___x_436_);
v___x_437_ = lean_array_push(v___x_430_, v___x_436_);
v___x_438_ = lean_byte_array_size(v___x_436_);
lean_dec_ref(v___x_436_);
v___x_439_ = lean_nat_add(v___x_432_, v___x_438_);
lean_dec(v___x_432_);
v___x_440_ = lean_array_push(v___x_437_, v___x_429_);
v___x_441_ = lean_nat_add(v___x_439_, v___x_431_);
lean_dec(v___x_439_);
v___x_442_ = l_Std_Http_Status_reasonPhrase(v_status_415_);
v___x_443_ = lean_string_to_utf8(v___x_442_);
lean_dec_ref(v___x_442_);
lean_inc_ref(v___x_443_);
v___x_444_ = lean_array_push(v___x_440_, v___x_443_);
v___x_445_ = lean_byte_array_size(v___x_443_);
lean_dec_ref(v___x_443_);
v___x_446_ = lean_nat_add(v___x_441_, v___x_445_);
lean_dec(v___x_441_);
v___x_447_ = lean_obj_once(&l_Std_Http_Response_instEncodeV11Head___lam__2___closed__2, &l_Std_Http_Response_instEncodeV11Head___lam__2___closed__2_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__2___closed__2);
v___x_448_ = lean_array_push(v___x_444_, v___x_447_);
v___x_449_ = lean_obj_once(&l_Std_Http_Response_instEncodeV11Head___lam__2___closed__3, &l_Std_Http_Response_instEncodeV11Head___lam__2___closed__3_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__2___closed__3);
v___x_450_ = lean_nat_add(v___x_446_, v___x_449_);
lean_dec(v___x_446_);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 1, v___x_450_);
lean_ctor_set(v___x_423_, 0, v___x_448_);
v_buffer_452_ = v___x_423_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v___x_448_);
lean_ctor_set(v_reuseFailAlloc_465_, 1, v___x_450_);
v_buffer_452_ = v_reuseFailAlloc_465_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
lean_object* v_buffer_453_; lean_object* v_data_454_; lean_object* v_size_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_464_; 
v_buffer_453_ = l_Std_Http_Headers_fold___redArg(v_headers_417_, v_buffer_452_, v___f_412_);
v_data_454_ = lean_ctor_get(v_buffer_453_, 0);
v_size_455_ = lean_ctor_get(v_buffer_453_, 1);
v_isSharedCheck_464_ = !lean_is_exclusive(v_buffer_453_);
if (v_isSharedCheck_464_ == 0)
{
v___x_457_ = v_buffer_453_;
v_isShared_458_ = v_isSharedCheck_464_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_size_455_);
lean_inc(v_data_454_);
lean_dec(v_buffer_453_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_464_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_462_; 
v___x_459_ = lean_array_push(v_data_454_, v___x_447_);
v___x_460_ = lean_nat_add(v_size_455_, v___x_449_);
lean_dec(v_size_455_);
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 1, v___x_460_);
lean_ctor_set(v___x_457_, 0, v___x_459_);
v___x_462_ = v___x_457_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v___x_459_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v___x_460_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instEncodeV11Head___lam__2___boxed(lean_object* v___f_471_, lean_object* v_buffer_472_, lean_object* v_r_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Std_Http_Response_instEncodeV11Head___lam__2(v___f_471_, v_buffer_472_, v_r_473_);
lean_dec_ref(v_r_473_);
return v_res_474_;
}
}
static lean_object* _init_l_Std_Http_Response_new___closed__0(void){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_479_ = l_Std_Http_Extensions_empty;
v___x_480_ = lean_obj_once(&l_Std_Http_Response_instInhabitedHead_default___closed__0, &l_Std_Http_Response_instInhabitedHead_default___closed__0_once, _init_l_Std_Http_Response_instInhabitedHead_default___closed__0);
v___x_481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_481_, 0, v___x_480_);
lean_ctor_set(v___x_481_, 1, v___x_479_);
return v___x_481_;
}
}
static lean_object* _init_l_Std_Http_Response_new(void){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = lean_obj_once(&l_Std_Http_Response_new___closed__0, &l_Std_Http_Response_new___closed__0_once, _init_l_Std_Http_Response_new___closed__0);
return v___x_482_;
}
}
static lean_object* _init_l_Std_Http_Response_Builder_new(void){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = lean_obj_once(&l_Std_Http_Response_new___closed__0, &l_Std_Http_Response_new___closed__0_once, _init_l_Std_Http_Response_new___closed__0);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_status(lean_object* v_builder_484_, lean_object* v_status_485_){
_start:
{
lean_object* v_line_486_; lean_object* v_extensions_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_504_; 
v_line_486_ = lean_ctor_get(v_builder_484_, 0);
v_extensions_487_ = lean_ctor_get(v_builder_484_, 1);
v_isSharedCheck_504_ = !lean_is_exclusive(v_builder_484_);
if (v_isSharedCheck_504_ == 0)
{
v___x_489_ = v_builder_484_;
v_isShared_490_ = v_isSharedCheck_504_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_extensions_487_);
lean_inc(v_line_486_);
lean_dec(v_builder_484_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_504_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
uint8_t v_version_491_; lean_object* v_headers_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_502_; 
v_version_491_ = lean_ctor_get_uint8(v_line_486_, sizeof(void*)*2);
v_headers_492_ = lean_ctor_get(v_line_486_, 1);
v_isSharedCheck_502_ = !lean_is_exclusive(v_line_486_);
if (v_isSharedCheck_502_ == 0)
{
lean_object* v_unused_503_; 
v_unused_503_ = lean_ctor_get(v_line_486_, 0);
lean_dec(v_unused_503_);
v___x_494_ = v_line_486_;
v_isShared_495_ = v_isSharedCheck_502_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_headers_492_);
lean_dec(v_line_486_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_502_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_497_; 
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 0, v_status_485_);
v___x_497_ = v___x_494_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v_status_485_);
lean_ctor_set(v_reuseFailAlloc_501_, 1, v_headers_492_);
lean_ctor_set_uint8(v_reuseFailAlloc_501_, sizeof(void*)*2, v_version_491_);
v___x_497_ = v_reuseFailAlloc_501_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
lean_object* v___x_499_; 
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 0, v___x_497_);
v___x_499_ = v___x_489_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v___x_497_);
lean_ctor_set(v_reuseFailAlloc_500_, 1, v_extensions_487_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_headers(lean_object* v_builder_505_, lean_object* v_headers_506_){
_start:
{
lean_object* v_line_507_; lean_object* v_extensions_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_525_; 
v_line_507_ = lean_ctor_get(v_builder_505_, 0);
v_extensions_508_ = lean_ctor_get(v_builder_505_, 1);
v_isSharedCheck_525_ = !lean_is_exclusive(v_builder_505_);
if (v_isSharedCheck_525_ == 0)
{
v___x_510_ = v_builder_505_;
v_isShared_511_ = v_isSharedCheck_525_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_extensions_508_);
lean_inc(v_line_507_);
lean_dec(v_builder_505_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_525_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v_status_512_; uint8_t v_version_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_523_; 
v_status_512_ = lean_ctor_get(v_line_507_, 0);
v_version_513_ = lean_ctor_get_uint8(v_line_507_, sizeof(void*)*2);
v_isSharedCheck_523_ = !lean_is_exclusive(v_line_507_);
if (v_isSharedCheck_523_ == 0)
{
lean_object* v_unused_524_; 
v_unused_524_ = lean_ctor_get(v_line_507_, 1);
lean_dec(v_unused_524_);
v___x_515_ = v_line_507_;
v_isShared_516_ = v_isSharedCheck_523_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_status_512_);
lean_dec(v_line_507_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_523_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_518_; 
if (v_isShared_516_ == 0)
{
lean_ctor_set(v___x_515_, 1, v_headers_506_);
v___x_518_ = v___x_515_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_status_512_);
lean_ctor_set(v_reuseFailAlloc_522_, 1, v_headers_506_);
lean_ctor_set_uint8(v_reuseFailAlloc_522_, sizeof(void*)*2, v_version_513_);
v___x_518_ = v_reuseFailAlloc_522_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
lean_object* v___x_520_; 
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 0, v___x_518_);
v___x_520_ = v___x_510_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v___x_518_);
lean_ctor_set(v_reuseFailAlloc_521_, 1, v_extensions_508_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0___redArg(lean_object* v_a_526_, lean_object* v_x_527_){
_start:
{
if (lean_obj_tag(v_x_527_) == 0)
{
uint8_t v___x_528_; 
v___x_528_ = 0;
return v___x_528_;
}
else
{
lean_object* v_key_529_; lean_object* v_tail_530_; uint8_t v___x_531_; 
v_key_529_ = lean_ctor_get(v_x_527_, 0);
v_tail_530_ = lean_ctor_get(v_x_527_, 2);
v___x_531_ = lean_string_dec_eq(v_key_529_, v_a_526_);
if (v___x_531_ == 0)
{
v_x_527_ = v_tail_530_;
goto _start;
}
else
{
return v___x_531_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0___redArg___boxed(lean_object* v_a_533_, lean_object* v_x_534_){
_start:
{
uint8_t v_res_535_; lean_object* v_r_536_; 
v_res_535_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0___redArg(v_a_533_, v_x_534_);
lean_dec(v_x_534_);
lean_dec_ref(v_a_533_);
v_r_536_ = lean_box(v_res_535_);
return v_r_536_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_537_, lean_object* v_x_538_){
_start:
{
if (lean_obj_tag(v_x_538_) == 0)
{
return v_x_537_;
}
else
{
lean_object* v_key_539_; lean_object* v_value_540_; lean_object* v_tail_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_564_; 
v_key_539_ = lean_ctor_get(v_x_538_, 0);
v_value_540_ = lean_ctor_get(v_x_538_, 1);
v_tail_541_ = lean_ctor_get(v_x_538_, 2);
v_isSharedCheck_564_ = !lean_is_exclusive(v_x_538_);
if (v_isSharedCheck_564_ == 0)
{
v___x_543_ = v_x_538_;
v_isShared_544_ = v_isSharedCheck_564_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_tail_541_);
lean_inc(v_value_540_);
lean_inc(v_key_539_);
lean_dec(v_x_538_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_564_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_545_; uint64_t v___x_546_; uint64_t v___x_547_; uint64_t v___x_548_; uint64_t v_fold_549_; uint64_t v___x_550_; uint64_t v___x_551_; uint64_t v___x_552_; size_t v___x_553_; size_t v___x_554_; size_t v___x_555_; size_t v___x_556_; size_t v___x_557_; lean_object* v___x_558_; lean_object* v___x_560_; 
v___x_545_ = lean_array_get_size(v_x_537_);
v___x_546_ = lean_string_hash(v_key_539_);
v___x_547_ = 32ULL;
v___x_548_ = lean_uint64_shift_right(v___x_546_, v___x_547_);
v_fold_549_ = lean_uint64_xor(v___x_546_, v___x_548_);
v___x_550_ = 16ULL;
v___x_551_ = lean_uint64_shift_right(v_fold_549_, v___x_550_);
v___x_552_ = lean_uint64_xor(v_fold_549_, v___x_551_);
v___x_553_ = lean_uint64_to_usize(v___x_552_);
v___x_554_ = lean_usize_of_nat(v___x_545_);
v___x_555_ = ((size_t)1ULL);
v___x_556_ = lean_usize_sub(v___x_554_, v___x_555_);
v___x_557_ = lean_usize_land(v___x_553_, v___x_556_);
v___x_558_ = lean_array_uget_borrowed(v_x_537_, v___x_557_);
lean_inc(v___x_558_);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 2, v___x_558_);
v___x_560_ = v___x_543_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_key_539_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v_value_540_);
lean_ctor_set(v_reuseFailAlloc_563_, 2, v___x_558_);
v___x_560_ = v_reuseFailAlloc_563_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
lean_object* v___x_561_; 
v___x_561_ = lean_array_uset(v_x_537_, v___x_557_, v___x_560_);
v_x_537_ = v___x_561_;
v_x_538_ = v_tail_541_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2___redArg(lean_object* v_i_565_, lean_object* v_source_566_, lean_object* v_target_567_){
_start:
{
lean_object* v___x_568_; uint8_t v___x_569_; 
v___x_568_ = lean_array_get_size(v_source_566_);
v___x_569_ = lean_nat_dec_lt(v_i_565_, v___x_568_);
if (v___x_569_ == 0)
{
lean_dec_ref(v_source_566_);
lean_dec(v_i_565_);
return v_target_567_;
}
else
{
lean_object* v_es_570_; lean_object* v___x_571_; lean_object* v_source_572_; lean_object* v_target_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v_es_570_ = lean_array_fget(v_source_566_, v_i_565_);
v___x_571_ = lean_box(0);
v_source_572_ = lean_array_fset(v_source_566_, v_i_565_, v___x_571_);
v_target_573_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2_spec__3___redArg(v_target_567_, v_es_570_);
v___x_574_ = lean_unsigned_to_nat(1u);
v___x_575_ = lean_nat_add(v_i_565_, v___x_574_);
lean_dec(v_i_565_);
v_i_565_ = v___x_575_;
v_source_566_ = v_source_572_;
v_target_567_ = v_target_573_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1___redArg(lean_object* v_data_577_){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v_nbuckets_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_578_ = lean_array_get_size(v_data_577_);
v___x_579_ = lean_unsigned_to_nat(2u);
v_nbuckets_580_ = lean_nat_mul(v___x_578_, v___x_579_);
v___x_581_ = lean_unsigned_to_nat(0u);
v___x_582_ = lean_box(0);
v___x_583_ = lean_mk_array(v_nbuckets_580_, v___x_582_);
v___x_584_ = lean_array_propagate_mark(v_data_577_, v___x_583_);
v___x_585_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2___redArg(v___x_581_, v_data_577_, v___x_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__2___lam__0(lean_object* v_i_586_, lean_object* v_x_587_){
_start:
{
if (lean_obj_tag(v_x_587_) == 0)
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_588_ = lean_unsigned_to_nat(1u);
v___x_589_ = lean_mk_empty_array_with_capacity(v___x_588_);
v___x_590_ = lean_array_push(v___x_589_, v_i_586_);
v___x_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_591_, 0, v___x_590_);
return v___x_591_;
}
else
{
lean_object* v_val_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_600_; 
v_val_592_ = lean_ctor_get(v_x_587_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v_x_587_);
if (v_isSharedCheck_600_ == 0)
{
v___x_594_ = v_x_587_;
v_isShared_595_ = v_isSharedCheck_600_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_val_592_);
lean_dec(v_x_587_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_600_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_596_; lean_object* v___x_598_; 
v___x_596_ = lean_array_push(v_val_592_, v_i_586_);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 0, v___x_596_);
v___x_598_ = v___x_594_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v___x_596_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__2(lean_object* v_i_601_, lean_object* v_a_602_, lean_object* v_x_603_){
_start:
{
if (lean_obj_tag(v_x_603_) == 0)
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v_val_606_; lean_object* v___x_607_; 
v___x_604_ = lean_box(0);
v___x_605_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__2___lam__0(v_i_601_, v___x_604_);
v_val_606_ = lean_ctor_get(v___x_605_, 0);
lean_inc(v_val_606_);
lean_dec(v___x_605_);
v___x_607_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_607_, 0, v_a_602_);
lean_ctor_set(v___x_607_, 1, v_val_606_);
lean_ctor_set(v___x_607_, 2, v_x_603_);
return v___x_607_;
}
else
{
lean_object* v_key_608_; lean_object* v_value_609_; lean_object* v_tail_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_625_; 
v_key_608_ = lean_ctor_get(v_x_603_, 0);
v_value_609_ = lean_ctor_get(v_x_603_, 1);
v_tail_610_ = lean_ctor_get(v_x_603_, 2);
v_isSharedCheck_625_ = !lean_is_exclusive(v_x_603_);
if (v_isSharedCheck_625_ == 0)
{
v___x_612_ = v_x_603_;
v_isShared_613_ = v_isSharedCheck_625_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_tail_610_);
lean_inc(v_value_609_);
lean_inc(v_key_608_);
lean_dec(v_x_603_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_625_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
uint8_t v___x_614_; 
v___x_614_ = lean_string_dec_eq(v_key_608_, v_a_602_);
if (v___x_614_ == 0)
{
lean_object* v_tail_615_; lean_object* v___x_617_; 
v_tail_615_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__2(v_i_601_, v_a_602_, v_tail_610_);
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 2, v_tail_615_);
v___x_617_ = v___x_612_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_key_608_);
lean_ctor_set(v_reuseFailAlloc_618_, 1, v_value_609_);
lean_ctor_set(v_reuseFailAlloc_618_, 2, v_tail_615_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
else
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v_val_621_; lean_object* v___x_623_; 
lean_dec(v_key_608_);
v___x_619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_619_, 0, v_value_609_);
v___x_620_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__2___lam__0(v_i_601_, v___x_619_);
v_val_621_ = lean_ctor_get(v___x_620_, 0);
lean_inc(v_val_621_);
lean_dec(v___x_620_);
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 1, v_val_621_);
lean_ctor_set(v___x_612_, 0, v_a_602_);
v___x_623_ = v___x_612_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_a_602_);
lean_ctor_set(v_reuseFailAlloc_624_, 1, v_val_621_);
lean_ctor_set(v_reuseFailAlloc_624_, 2, v_tail_610_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0(lean_object* v_i_626_, lean_object* v_m_627_, lean_object* v_a_628_){
_start:
{
lean_object* v_size_629_; lean_object* v_buckets_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_680_; 
v_size_629_ = lean_ctor_get(v_m_627_, 0);
v_buckets_630_ = lean_ctor_get(v_m_627_, 1);
v_isSharedCheck_680_ = !lean_is_exclusive(v_m_627_);
if (v_isSharedCheck_680_ == 0)
{
v___x_632_ = v_m_627_;
v_isShared_633_ = v_isSharedCheck_680_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_buckets_630_);
lean_inc(v_size_629_);
lean_dec(v_m_627_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_680_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_634_; uint64_t v___x_635_; uint64_t v___x_636_; uint64_t v___x_637_; uint64_t v_fold_638_; uint64_t v___x_639_; uint64_t v___x_640_; uint64_t v___x_641_; size_t v___x_642_; size_t v___x_643_; size_t v___x_644_; size_t v___x_645_; size_t v___x_646_; lean_object* v_bkt_647_; uint8_t v___x_648_; 
v___x_634_ = lean_array_get_size(v_buckets_630_);
v___x_635_ = lean_string_hash(v_a_628_);
v___x_636_ = 32ULL;
v___x_637_ = lean_uint64_shift_right(v___x_635_, v___x_636_);
v_fold_638_ = lean_uint64_xor(v___x_635_, v___x_637_);
v___x_639_ = 16ULL;
v___x_640_ = lean_uint64_shift_right(v_fold_638_, v___x_639_);
v___x_641_ = lean_uint64_xor(v_fold_638_, v___x_640_);
v___x_642_ = lean_uint64_to_usize(v___x_641_);
v___x_643_ = lean_usize_of_nat(v___x_634_);
v___x_644_ = ((size_t)1ULL);
v___x_645_ = lean_usize_sub(v___x_643_, v___x_644_);
v___x_646_ = lean_usize_land(v___x_642_, v___x_645_);
v_bkt_647_ = lean_array_uget_borrowed(v_buckets_630_, v___x_646_);
v___x_648_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0___redArg(v_a_628_, v_bkt_647_);
if (v___x_648_ == 0)
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v_size_x27_652_; lean_object* v___x_653_; lean_object* v_buckets_x27_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; uint8_t v___x_660_; 
v___x_649_ = lean_unsigned_to_nat(1u);
v___x_650_ = lean_mk_empty_array_with_capacity(v___x_649_);
v___x_651_ = lean_array_push(v___x_650_, v_i_626_);
v_size_x27_652_ = lean_nat_add(v_size_629_, v___x_649_);
lean_dec(v_size_629_);
lean_inc(v_bkt_647_);
v___x_653_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_653_, 0, v_a_628_);
lean_ctor_set(v___x_653_, 1, v___x_651_);
lean_ctor_set(v___x_653_, 2, v_bkt_647_);
v_buckets_x27_654_ = lean_array_uset(v_buckets_630_, v___x_646_, v___x_653_);
v___x_655_ = lean_unsigned_to_nat(4u);
v___x_656_ = lean_nat_mul(v_size_x27_652_, v___x_655_);
v___x_657_ = lean_unsigned_to_nat(3u);
v___x_658_ = lean_nat_div(v___x_656_, v___x_657_);
lean_dec(v___x_656_);
v___x_659_ = lean_array_get_size(v_buckets_x27_654_);
v___x_660_ = lean_nat_dec_le(v___x_658_, v___x_659_);
lean_dec(v___x_658_);
if (v___x_660_ == 0)
{
lean_object* v_val_661_; lean_object* v___x_663_; 
v_val_661_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1___redArg(v_buckets_x27_654_);
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 1, v_val_661_);
lean_ctor_set(v___x_632_, 0, v_size_x27_652_);
v___x_663_ = v___x_632_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_size_x27_652_);
lean_ctor_set(v_reuseFailAlloc_664_, 1, v_val_661_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
else
{
lean_object* v___x_666_; 
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 1, v_buckets_x27_654_);
lean_ctor_set(v___x_632_, 0, v_size_x27_652_);
v___x_666_ = v___x_632_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_size_x27_652_);
lean_ctor_set(v_reuseFailAlloc_667_, 1, v_buckets_x27_654_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
else
{
lean_object* v___x_668_; lean_object* v_buckets_x27_669_; lean_object* v_bkt_x27_670_; lean_object* v___y_672_; uint8_t v___x_677_; 
lean_inc(v_bkt_647_);
v___x_668_ = lean_box(0);
v_buckets_x27_669_ = lean_array_uset(v_buckets_630_, v___x_646_, v___x_668_);
lean_inc_ref(v_a_628_);
v_bkt_x27_670_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__2(v_i_626_, v_a_628_, v_bkt_647_);
v___x_677_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0___redArg(v_a_628_, v_bkt_x27_670_);
lean_dec_ref(v_a_628_);
if (v___x_677_ == 0)
{
lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_678_ = lean_unsigned_to_nat(1u);
v___x_679_ = lean_nat_sub(v_size_629_, v___x_678_);
lean_dec(v_size_629_);
v___y_672_ = v___x_679_;
goto v___jp_671_;
}
else
{
v___y_672_ = v_size_629_;
goto v___jp_671_;
}
v___jp_671_:
{
lean_object* v___x_673_; lean_object* v___x_675_; 
v___x_673_ = lean_array_uset(v_buckets_x27_669_, v___x_646_, v_bkt_x27_670_);
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 1, v___x_673_);
lean_ctor_set(v___x_632_, 0, v___y_672_);
v___x_675_ = v___x_632_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v___y_672_);
lean_ctor_set(v_reuseFailAlloc_676_, 1, v___x_673_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_header(lean_object* v_builder_681_, lean_object* v_key_682_, lean_object* v_value_683_){
_start:
{
lean_object* v_line_684_; lean_object* v_headers_685_; lean_object* v_extensions_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_716_; 
v_line_684_ = lean_ctor_get(v_builder_681_, 0);
lean_inc_ref(v_line_684_);
v_headers_685_ = lean_ctor_get(v_line_684_, 1);
lean_inc_ref(v_headers_685_);
v_extensions_686_ = lean_ctor_get(v_builder_681_, 1);
v_isSharedCheck_716_ = !lean_is_exclusive(v_builder_681_);
if (v_isSharedCheck_716_ == 0)
{
lean_object* v_unused_717_; 
v_unused_717_ = lean_ctor_get(v_builder_681_, 0);
lean_dec(v_unused_717_);
v___x_688_ = v_builder_681_;
v_isShared_689_ = v_isSharedCheck_716_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_extensions_686_);
lean_dec(v_builder_681_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_716_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v_status_690_; uint8_t v_version_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_714_; 
v_status_690_ = lean_ctor_get(v_line_684_, 0);
v_version_691_ = lean_ctor_get_uint8(v_line_684_, sizeof(void*)*2);
v_isSharedCheck_714_ = !lean_is_exclusive(v_line_684_);
if (v_isSharedCheck_714_ == 0)
{
lean_object* v_unused_715_; 
v_unused_715_ = lean_ctor_get(v_line_684_, 1);
lean_dec(v_unused_715_);
v___x_693_ = v_line_684_;
v_isShared_694_ = v_isSharedCheck_714_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_status_690_);
lean_dec(v_line_684_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_714_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v_entries_695_; lean_object* v_indexes_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_713_; 
v_entries_695_ = lean_ctor_get(v_headers_685_, 0);
v_indexes_696_ = lean_ctor_get(v_headers_685_, 1);
v_isSharedCheck_713_ = !lean_is_exclusive(v_headers_685_);
if (v_isSharedCheck_713_ == 0)
{
v___x_698_ = v_headers_685_;
v_isShared_699_ = v_isSharedCheck_713_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_indexes_696_);
lean_inc(v_entries_695_);
lean_dec(v_headers_685_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_713_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v_i_700_; lean_object* v___x_701_; lean_object* v_entries_702_; lean_object* v_indexes_703_; lean_object* v___x_705_; 
v_i_700_ = lean_array_get_size(v_entries_695_);
lean_inc_ref(v_key_682_);
v___x_701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_701_, 0, v_key_682_);
lean_ctor_set(v___x_701_, 1, v_value_683_);
v_entries_702_ = lean_array_push(v_entries_695_, v___x_701_);
v_indexes_703_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0(v_i_700_, v_indexes_696_, v_key_682_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 1, v_indexes_703_);
lean_ctor_set(v___x_698_, 0, v_entries_702_);
v___x_705_ = v___x_698_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_entries_702_);
lean_ctor_set(v_reuseFailAlloc_712_, 1, v_indexes_703_);
v___x_705_ = v_reuseFailAlloc_712_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
lean_object* v___x_707_; 
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 1, v___x_705_);
v___x_707_ = v___x_693_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_status_690_);
lean_ctor_set(v_reuseFailAlloc_711_, 1, v___x_705_);
lean_ctor_set_uint8(v_reuseFailAlloc_711_, sizeof(void*)*2, v_version_691_);
v___x_707_ = v_reuseFailAlloc_711_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
lean_object* v___x_709_; 
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 0, v___x_707_);
v___x_709_ = v___x_688_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v___x_707_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v_extensions_686_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0(lean_object* v_00_u03b2_718_, lean_object* v_a_719_, lean_object* v_x_720_){
_start:
{
uint8_t v___x_721_; 
v___x_721_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0___redArg(v_a_719_, v_x_720_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0___boxed(lean_object* v_00_u03b2_722_, lean_object* v_a_723_, lean_object* v_x_724_){
_start:
{
uint8_t v_res_725_; lean_object* v_r_726_; 
v_res_725_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0(v_00_u03b2_722_, v_a_723_, v_x_724_);
lean_dec(v_x_724_);
lean_dec_ref(v_a_723_);
v_r_726_ = lean_box(v_res_725_);
return v_r_726_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1(lean_object* v_00_u03b2_727_, lean_object* v_data_728_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1___redArg(v_data_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_730_, lean_object* v_i_731_, lean_object* v_source_732_, lean_object* v_target_733_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2___redArg(v_i_731_, v_source_732_, v_target_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_735_, lean_object* v_x_736_, lean_object* v_x_737_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2_spec__3___redArg(v_x_736_, v_x_737_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_header_x21(lean_object* v_builder_739_, lean_object* v_key_740_, lean_object* v_value_741_){
_start:
{
lean_object* v_line_742_; lean_object* v_headers_743_; lean_object* v_extensions_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_776_; 
v_line_742_ = lean_ctor_get(v_builder_739_, 0);
lean_inc_ref(v_line_742_);
v_headers_743_ = lean_ctor_get(v_line_742_, 1);
lean_inc_ref(v_headers_743_);
v_extensions_744_ = lean_ctor_get(v_builder_739_, 1);
v_isSharedCheck_776_ = !lean_is_exclusive(v_builder_739_);
if (v_isSharedCheck_776_ == 0)
{
lean_object* v_unused_777_; 
v_unused_777_ = lean_ctor_get(v_builder_739_, 0);
lean_dec(v_unused_777_);
v___x_746_ = v_builder_739_;
v_isShared_747_ = v_isSharedCheck_776_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_extensions_744_);
lean_dec(v_builder_739_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_776_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v_status_748_; uint8_t v_version_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_774_; 
v_status_748_ = lean_ctor_get(v_line_742_, 0);
v_version_749_ = lean_ctor_get_uint8(v_line_742_, sizeof(void*)*2);
v_isSharedCheck_774_ = !lean_is_exclusive(v_line_742_);
if (v_isSharedCheck_774_ == 0)
{
lean_object* v_unused_775_; 
v_unused_775_ = lean_ctor_get(v_line_742_, 1);
lean_dec(v_unused_775_);
v___x_751_ = v_line_742_;
v_isShared_752_ = v_isSharedCheck_774_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_status_748_);
lean_dec(v_line_742_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_774_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v_entries_753_; lean_object* v_indexes_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_773_; 
v_entries_753_ = lean_ctor_get(v_headers_743_, 0);
v_indexes_754_ = lean_ctor_get(v_headers_743_, 1);
v_isSharedCheck_773_ = !lean_is_exclusive(v_headers_743_);
if (v_isSharedCheck_773_ == 0)
{
v___x_756_ = v_headers_743_;
v_isShared_757_ = v_isSharedCheck_773_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_indexes_754_);
lean_inc(v_entries_753_);
lean_dec(v_headers_743_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_773_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v_key_758_; lean_object* v_value_759_; lean_object* v_i_760_; lean_object* v___x_761_; lean_object* v_entries_762_; lean_object* v_indexes_763_; lean_object* v___x_765_; 
v_key_758_ = l_Std_Http_Header_Name_ofString_x21(v_key_740_);
v_value_759_ = l_Std_Http_Header_Value_ofString_x21(v_value_741_);
v_i_760_ = lean_array_get_size(v_entries_753_);
lean_inc_ref(v_key_758_);
v___x_761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_761_, 0, v_key_758_);
lean_ctor_set(v___x_761_, 1, v_value_759_);
v_entries_762_ = lean_array_push(v_entries_753_, v___x_761_);
v_indexes_763_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0(v_i_760_, v_indexes_754_, v_key_758_);
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 1, v_indexes_763_);
lean_ctor_set(v___x_756_, 0, v_entries_762_);
v___x_765_ = v___x_756_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_entries_762_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v_indexes_763_);
v___x_765_ = v_reuseFailAlloc_772_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
lean_object* v___x_767_; 
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 1, v___x_765_);
v___x_767_ = v___x_751_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_status_748_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v___x_765_);
lean_ctor_set_uint8(v_reuseFailAlloc_771_, sizeof(void*)*2, v_version_749_);
v___x_767_ = v_reuseFailAlloc_771_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
lean_object* v___x_769_; 
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 0, v___x_767_);
v___x_769_ = v___x_746_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_767_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v_extensions_744_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_header_x3f(lean_object* v_builder_778_, lean_object* v_key_779_, lean_object* v_value_780_){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = l_Std_Http_Header_Name_ofString_x3f(v_key_779_);
if (lean_obj_tag(v___x_781_) == 0)
{
lean_object* v___x_782_; 
lean_dec_ref(v_value_780_);
lean_dec_ref(v_builder_778_);
v___x_782_ = lean_box(0);
return v___x_782_;
}
else
{
lean_object* v_val_783_; lean_object* v___x_784_; 
v_val_783_ = lean_ctor_get(v___x_781_, 0);
lean_inc(v_val_783_);
lean_dec_ref_known(v___x_781_, 1);
v___x_784_ = l_Std_Http_Header_Value_ofString_x3f(v_value_780_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v___x_785_; 
lean_dec(v_val_783_);
lean_dec_ref(v_builder_778_);
v___x_785_ = lean_box(0);
return v___x_785_;
}
else
{
lean_object* v_line_786_; lean_object* v_headers_787_; lean_object* v_val_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_827_; 
v_line_786_ = lean_ctor_get(v_builder_778_, 0);
lean_inc_ref(v_line_786_);
v_headers_787_ = lean_ctor_get(v_line_786_, 1);
lean_inc_ref(v_headers_787_);
v_val_788_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_827_ == 0)
{
v___x_790_ = v___x_784_;
v_isShared_791_ = v_isSharedCheck_827_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_val_788_);
lean_dec(v___x_784_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_827_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v_extensions_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_825_; 
v_extensions_792_ = lean_ctor_get(v_builder_778_, 1);
v_isSharedCheck_825_ = !lean_is_exclusive(v_builder_778_);
if (v_isSharedCheck_825_ == 0)
{
lean_object* v_unused_826_; 
v_unused_826_ = lean_ctor_get(v_builder_778_, 0);
lean_dec(v_unused_826_);
v___x_794_ = v_builder_778_;
v_isShared_795_ = v_isSharedCheck_825_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_extensions_792_);
lean_dec(v_builder_778_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_825_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v_status_796_; uint8_t v_version_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_823_; 
v_status_796_ = lean_ctor_get(v_line_786_, 0);
v_version_797_ = lean_ctor_get_uint8(v_line_786_, sizeof(void*)*2);
v_isSharedCheck_823_ = !lean_is_exclusive(v_line_786_);
if (v_isSharedCheck_823_ == 0)
{
lean_object* v_unused_824_; 
v_unused_824_ = lean_ctor_get(v_line_786_, 1);
lean_dec(v_unused_824_);
v___x_799_ = v_line_786_;
v_isShared_800_ = v_isSharedCheck_823_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_status_796_);
lean_dec(v_line_786_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_823_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v_entries_801_; lean_object* v_indexes_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_822_; 
v_entries_801_ = lean_ctor_get(v_headers_787_, 0);
v_indexes_802_ = lean_ctor_get(v_headers_787_, 1);
v_isSharedCheck_822_ = !lean_is_exclusive(v_headers_787_);
if (v_isSharedCheck_822_ == 0)
{
v___x_804_ = v_headers_787_;
v_isShared_805_ = v_isSharedCheck_822_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_indexes_802_);
lean_inc(v_entries_801_);
lean_dec(v_headers_787_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_822_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v_i_806_; lean_object* v___x_807_; lean_object* v_entries_808_; lean_object* v_indexes_809_; lean_object* v___x_811_; 
v_i_806_ = lean_array_get_size(v_entries_801_);
lean_inc(v_val_783_);
v___x_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_807_, 0, v_val_783_);
lean_ctor_set(v___x_807_, 1, v_val_788_);
v_entries_808_ = lean_array_push(v_entries_801_, v___x_807_);
v_indexes_809_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0(v_i_806_, v_indexes_802_, v_val_783_);
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 1, v_indexes_809_);
lean_ctor_set(v___x_804_, 0, v_entries_808_);
v___x_811_ = v___x_804_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_entries_808_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v_indexes_809_);
v___x_811_ = v_reuseFailAlloc_821_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
lean_object* v___x_813_; 
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 1, v___x_811_);
v___x_813_ = v___x_799_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_status_796_);
lean_ctor_set(v_reuseFailAlloc_820_, 1, v___x_811_);
lean_ctor_set_uint8(v_reuseFailAlloc_820_, sizeof(void*)*2, v_version_797_);
v___x_813_ = v_reuseFailAlloc_820_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
lean_object* v___x_815_; 
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 0, v___x_813_);
v___x_815_ = v___x_794_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_813_);
lean_ctor_set(v_reuseFailAlloc_819_, 1, v_extensions_792_);
v___x_815_ = v_reuseFailAlloc_819_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
lean_object* v___x_817_; 
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 0, v___x_815_);
v___x_817_ = v___x_790_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_815_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
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
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_extension___redArg(lean_object* v_builder_829_, lean_object* v_inst_830_, lean_object* v_data_831_){
_start:
{
lean_object* v_line_832_; lean_object* v_extensions_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_844_; 
v_line_832_ = lean_ctor_get(v_builder_829_, 0);
v_extensions_833_ = lean_ctor_get(v_builder_829_, 1);
v_isSharedCheck_844_ = !lean_is_exclusive(v_builder_829_);
if (v_isSharedCheck_844_ == 0)
{
v___x_835_ = v_builder_829_;
v_isShared_836_ = v_isSharedCheck_844_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_extensions_833_);
lean_inc(v_line_832_);
lean_dec(v_builder_829_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_844_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v_dyn_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_842_; 
v_dyn_837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_dyn_837_, 0, v_inst_830_);
lean_ctor_set(v_dyn_837_, 1, v_data_831_);
v___x_838_ = ((lean_object*)(l_Std_Http_Response_Builder_extension___redArg___closed__0));
v___x_839_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_dyn_837_);
v___x_840_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_838_, v___x_839_, v_dyn_837_, v_extensions_833_);
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 1, v___x_840_);
v___x_842_ = v___x_835_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_line_832_);
lean_ctor_set(v_reuseFailAlloc_843_, 1, v___x_840_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_extension(lean_object* v_00_u03b1_845_, lean_object* v_builder_846_, lean_object* v_inst_847_, lean_object* v_data_848_){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = l_Std_Http_Response_Builder_extension___redArg(v_builder_846_, v_inst_847_, v_data_848_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_body___redArg(lean_object* v_builder_850_, lean_object* v_body_851_){
_start:
{
lean_object* v_line_852_; lean_object* v_extensions_853_; lean_object* v___x_854_; 
v_line_852_ = lean_ctor_get(v_builder_850_, 0);
v_extensions_853_ = lean_ctor_get(v_builder_850_, 1);
lean_inc(v_extensions_853_);
lean_inc_ref(v_line_852_);
v___x_854_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_854_, 0, v_line_852_);
lean_ctor_set(v___x_854_, 1, v_body_851_);
lean_ctor_set(v___x_854_, 2, v_extensions_853_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_body___redArg___boxed(lean_object* v_builder_855_, lean_object* v_body_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_Std_Http_Response_Builder_body___redArg(v_builder_855_, v_body_856_);
lean_dec_ref(v_builder_855_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_body(lean_object* v_t_858_, lean_object* v_builder_859_, lean_object* v_body_860_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = l_Std_Http_Response_Builder_body___redArg(v_builder_859_, v_body_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_body___boxed(lean_object* v_t_862_, lean_object* v_builder_863_, lean_object* v_body_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l_Std_Http_Response_Builder_body(v_t_862_, v_builder_863_, v_body_864_);
lean_dec_ref(v_builder_863_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_build___redArg(lean_object* v_inst_866_, lean_object* v_builder_867_){
_start:
{
lean_object* v_line_868_; lean_object* v_extensions_869_; lean_object* v___x_870_; 
v_line_868_ = lean_ctor_get(v_builder_867_, 0);
v_extensions_869_ = lean_ctor_get(v_builder_867_, 1);
lean_inc(v_extensions_869_);
lean_inc_ref(v_line_868_);
v___x_870_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_870_, 0, v_line_868_);
lean_ctor_set(v___x_870_, 1, v_inst_866_);
lean_ctor_set(v___x_870_, 2, v_extensions_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_build___redArg___boxed(lean_object* v_inst_871_, lean_object* v_builder_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l_Std_Http_Response_Builder_build___redArg(v_inst_871_, v_builder_872_);
lean_dec_ref(v_builder_872_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_build(lean_object* v_t_874_, lean_object* v_inst_875_, lean_object* v_builder_876_){
_start:
{
lean_object* v___x_877_; 
v___x_877_ = l_Std_Http_Response_Builder_build___redArg(v_inst_875_, v_builder_876_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_build___boxed(lean_object* v_t_878_, lean_object* v_inst_879_, lean_object* v_builder_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_Std_Http_Response_Builder_build(v_t_878_, v_inst_879_, v_builder_880_);
lean_dec_ref(v_builder_880_);
return v_res_881_;
}
}
static lean_object* _init_l_Std_Http_Response_ok___closed__0(void){
_start:
{
lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_882_ = lean_box(4);
v___x_883_ = l_Std_Http_Response_Builder_new;
v___x_884_ = l_Std_Http_Response_Builder_status(v___x_883_, v___x_882_);
return v___x_884_;
}
}
static lean_object* _init_l_Std_Http_Response_ok(void){
_start:
{
lean_object* v___x_885_; 
v___x_885_ = lean_obj_once(&l_Std_Http_Response_ok___closed__0, &l_Std_Http_Response_ok___closed__0_once, _init_l_Std_Http_Response_ok___closed__0);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_withStatus(lean_object* v_status_886_){
_start:
{
lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_887_ = l_Std_Http_Response_Builder_new;
v___x_888_ = l_Std_Http_Response_Builder_status(v___x_887_, v_status_886_);
return v___x_888_;
}
}
static lean_object* _init_l_Std_Http_Response_notFound___closed__0(void){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_889_ = lean_box(27);
v___x_890_ = l_Std_Http_Response_Builder_new;
v___x_891_ = l_Std_Http_Response_Builder_status(v___x_890_, v___x_889_);
return v___x_891_;
}
}
static lean_object* _init_l_Std_Http_Response_notFound(void){
_start:
{
lean_object* v___x_892_; 
v___x_892_ = lean_obj_once(&l_Std_Http_Response_notFound___closed__0, &l_Std_Http_Response_notFound___closed__0_once, _init_l_Std_Http_Response_notFound___closed__0);
return v___x_892_;
}
}
static lean_object* _init_l_Std_Http_Response_internalServerError___closed__0(void){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_893_ = lean_box(52);
v___x_894_ = l_Std_Http_Response_Builder_new;
v___x_895_ = l_Std_Http_Response_Builder_status(v___x_894_, v___x_893_);
return v___x_895_;
}
}
static lean_object* _init_l_Std_Http_Response_internalServerError(void){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = lean_obj_once(&l_Std_Http_Response_internalServerError___closed__0, &l_Std_Http_Response_internalServerError___closed__0_once, _init_l_Std_Http_Response_internalServerError___closed__0);
return v___x_896_;
}
}
static lean_object* _init_l_Std_Http_Response_badRequest___closed__0(void){
_start:
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_897_ = lean_box(23);
v___x_898_ = l_Std_Http_Response_Builder_new;
v___x_899_ = l_Std_Http_Response_Builder_status(v___x_898_, v___x_897_);
return v___x_899_;
}
}
static lean_object* _init_l_Std_Http_Response_badRequest(void){
_start:
{
lean_object* v___x_900_; 
v___x_900_ = lean_obj_once(&l_Std_Http_Response_badRequest___closed__0, &l_Std_Http_Response_badRequest___closed__0_once, _init_l_Std_Http_Response_badRequest___closed__0);
return v___x_900_;
}
}
static lean_object* _init_l_Std_Http_Response_created___closed__0(void){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_901_ = lean_box(5);
v___x_902_ = l_Std_Http_Response_Builder_new;
v___x_903_ = l_Std_Http_Response_Builder_status(v___x_902_, v___x_901_);
return v___x_903_;
}
}
static lean_object* _init_l_Std_Http_Response_created(void){
_start:
{
lean_object* v___x_904_; 
v___x_904_ = lean_obj_once(&l_Std_Http_Response_created___closed__0, &l_Std_Http_Response_created___closed__0_once, _init_l_Std_Http_Response_created___closed__0);
return v___x_904_;
}
}
static lean_object* _init_l_Std_Http_Response_accepted___closed__0(void){
_start:
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_905_ = lean_box(6);
v___x_906_ = l_Std_Http_Response_Builder_new;
v___x_907_ = l_Std_Http_Response_Builder_status(v___x_906_, v___x_905_);
return v___x_907_;
}
}
static lean_object* _init_l_Std_Http_Response_accepted(void){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = lean_obj_once(&l_Std_Http_Response_accepted___closed__0, &l_Std_Http_Response_accepted___closed__0_once, _init_l_Std_Http_Response_accepted___closed__0);
return v___x_908_;
}
}
static lean_object* _init_l_Std_Http_Response_unauthorized___closed__0(void){
_start:
{
lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_909_ = lean_box(24);
v___x_910_ = l_Std_Http_Response_Builder_new;
v___x_911_ = l_Std_Http_Response_Builder_status(v___x_910_, v___x_909_);
return v___x_911_;
}
}
static lean_object* _init_l_Std_Http_Response_unauthorized(void){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = lean_obj_once(&l_Std_Http_Response_unauthorized___closed__0, &l_Std_Http_Response_unauthorized___closed__0_once, _init_l_Std_Http_Response_unauthorized___closed__0);
return v___x_912_;
}
}
static lean_object* _init_l_Std_Http_Response_forbidden___closed__0(void){
_start:
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_913_ = lean_box(26);
v___x_914_ = l_Std_Http_Response_Builder_new;
v___x_915_ = l_Std_Http_Response_Builder_status(v___x_914_, v___x_913_);
return v___x_915_;
}
}
static lean_object* _init_l_Std_Http_Response_forbidden(void){
_start:
{
lean_object* v___x_916_; 
v___x_916_ = lean_obj_once(&l_Std_Http_Response_forbidden___closed__0, &l_Std_Http_Response_forbidden___closed__0_once, _init_l_Std_Http_Response_forbidden___closed__0);
return v___x_916_;
}
}
static lean_object* _init_l_Std_Http_Response_conflict___closed__0(void){
_start:
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_917_ = lean_box(32);
v___x_918_ = l_Std_Http_Response_Builder_new;
v___x_919_ = l_Std_Http_Response_Builder_status(v___x_918_, v___x_917_);
return v___x_919_;
}
}
static lean_object* _init_l_Std_Http_Response_conflict(void){
_start:
{
lean_object* v___x_920_; 
v___x_920_ = lean_obj_once(&l_Std_Http_Response_conflict___closed__0, &l_Std_Http_Response_conflict___closed__0_once, _init_l_Std_Http_Response_conflict___closed__0);
return v___x_920_;
}
}
static lean_object* _init_l_Std_Http_Response_serviceUnavailable___closed__0(void){
_start:
{
lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_921_ = lean_box(55);
v___x_922_ = l_Std_Http_Response_Builder_new;
v___x_923_ = l_Std_Http_Response_Builder_status(v___x_922_, v___x_921_);
return v___x_923_;
}
}
static lean_object* _init_l_Std_Http_Response_serviceUnavailable(void){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = lean_obj_once(&l_Std_Http_Response_serviceUnavailable___closed__0, &l_Std_Http_Response_serviceUnavailable___closed__0_once, _init_l_Std_Http_Response_serviceUnavailable___closed__0);
return v___x_924_;
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
