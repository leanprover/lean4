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
lean_object* lean_nat_add(lean_object*, lean_object*);
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
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_byte_array_size(lean_object*);
extern lean_object* l_Std_Http_Extensions_empty;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Std_Http_Extensions_compareName___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Dynamic_0__Dynamic_typeNameImpl(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_instReprStatus_repr(lean_object*, lean_object*);
lean_object* l_Std_Http_instReprVersion_repr(uint8_t, lean_object*);
lean_object* l_Std_Http_instReprHeaders_repr___redArg(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_byte_array_copy_slice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_Http_Internal_appendFieldLine___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_Headers_fold___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_byte_array_push(lean_object*, uint8_t);
lean_object* l_Std_Http_Internal_appendNat(lean_object*, lean_object*);
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
static lean_once_cell_t l_Std_Http_Response_instEncodeV11Head___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_instEncodeV11Head___lam__0___closed__0;
static lean_once_cell_t l_Std_Http_Response_instEncodeV11Head___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_instEncodeV11Head___lam__0___closed__1;
static const lean_closure_object l_Std_Http_Response_instEncodeV11Head___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Internal_appendFieldLine___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Response_instEncodeV11Head___lam__0___closed__2 = (const lean_object*)&l_Std_Http_Response_instEncodeV11Head___lam__0___closed__2_value;
static const lean_string_object l_Std_Http_Response_instEncodeV11Head___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "200 OK"};
static const lean_object* l_Std_Http_Response_instEncodeV11Head___lam__0___closed__3 = (const lean_object*)&l_Std_Http_Response_instEncodeV11Head___lam__0___closed__3_value;
static lean_once_cell_t l_Std_Http_Response_instEncodeV11Head___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_instEncodeV11Head___lam__0___closed__4;
static lean_once_cell_t l_Std_Http_Response_instEncodeV11Head___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_instEncodeV11Head___lam__0___closed__5;
static lean_once_cell_t l_Std_Http_Response_instEncodeV11Head___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_instEncodeV11Head___lam__0___closed__6;
static lean_once_cell_t l_Std_Http_Response_instEncodeV11Head___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_instEncodeV11Head___lam__0___closed__7;
static lean_once_cell_t l_Std_Http_Response_instEncodeV11Head___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_instEncodeV11Head___lam__0___closed__8;
static lean_once_cell_t l_Std_Http_Response_instEncodeV11Head___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_instEncodeV11Head___lam__0___closed__9;
static lean_once_cell_t l_Std_Http_Response_instEncodeV11Head___lam__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_instEncodeV11Head___lam__0___closed__10;
static lean_once_cell_t l_Std_Http_Response_instEncodeV11Head___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_instEncodeV11Head___lam__0___closed__11;
static lean_once_cell_t l_Std_Http_Response_instEncodeV11Head___lam__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_instEncodeV11Head___lam__0___closed__12;
static lean_once_cell_t l_Std_Http_Response_instEncodeV11Head___lam__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_instEncodeV11Head___lam__0___closed__13;
LEAN_EXPORT lean_object* l_Std_Http_Response_instEncodeV11Head___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_instEncodeV11Head___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Response_instEncodeV11Head___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Response_instEncodeV11Head___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Response_instEncodeV11Head___closed__0 = (const lean_object*)&l_Std_Http_Response_instEncodeV11Head___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Response_instEncodeV11Head = (const lean_object*)&l_Std_Http_Response_instEncodeV11Head___closed__0_value;
static lean_once_cell_t l_Std_Http_Response_new___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_new___closed__0;
LEAN_EXPORT lean_object* l_Std_Http_Response_new;
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_new;
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_status(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_headers(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_header(lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_263_; 
v___x_263_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__12));
v___y_243_ = v___x_263_;
goto v___jp_242_;
}
case 1:
{
lean_object* v___x_264_; 
v___x_264_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__13));
v___y_243_ = v___x_264_;
goto v___jp_242_;
}
case 2:
{
lean_object* v___x_265_; 
v___x_265_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__14));
v___y_243_ = v___x_265_;
goto v___jp_242_;
}
default: 
{
lean_object* v___x_266_; 
v___x_266_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__15));
v___y_243_ = v___x_266_;
goto v___jp_242_;
}
}
v___jp_242_:
{
lean_object* v___x_244_; lean_object* v___x_245_; uint16_t v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; size_t v_sz_256_; size_t v___x_257_; lean_object* v_pairs_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_244_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__0));
lean_inc_ref(v___y_243_);
v___x_245_ = lean_string_append(v___y_243_, v___x_244_);
v___x_246_ = l_Std_Http_Status_toCode(v_status_239_);
v___x_247_ = lean_uint16_to_nat(v___x_246_);
v___x_248_ = l_Nat_reprFast(v___x_247_);
v___x_249_ = lean_string_append(v___x_245_, v___x_248_);
lean_dec_ref(v___x_248_);
v___x_250_ = lean_string_append(v___x_249_, v___x_244_);
v___x_251_ = l_Std_Http_Status_reasonPhrase(v_status_239_);
lean_dec(v_status_239_);
v___x_252_ = lean_string_append(v___x_250_, v___x_251_);
lean_dec_ref(v___x_251_);
v___x_253_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__1));
v___x_254_ = lean_string_append(v___x_252_, v___x_253_);
v___x_255_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__11));
v_sz_256_ = lean_array_size(v_headers_241_);
v___x_257_ = ((size_t)0ULL);
v_pairs_258_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_255_, v___f_237_, v_sz_256_, v___x_257_, v_headers_241_);
v___x_259_ = lean_array_to_list(v_pairs_258_);
v___x_260_ = l_String_intercalate(v___x_253_, v___x_259_);
v___x_261_ = lean_string_append(v___x_254_, v___x_260_);
lean_dec_ref(v___x_260_);
v___x_262_ = lean_string_append(v___x_261_, v___x_253_);
return v___x_262_;
}
}
}
static lean_object* _init_l_Std_Http_Response_instEncodeV11Head___lam__0___closed__0(void){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_271_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__1));
v___x_272_ = lean_string_to_utf8(v___x_271_);
return v___x_272_;
}
}
static lean_object* _init_l_Std_Http_Response_instEncodeV11Head___lam__0___closed__1(void){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = lean_obj_once(&l_Std_Http_Response_instEncodeV11Head___lam__0___closed__0, &l_Std_Http_Response_instEncodeV11Head___lam__0___closed__0_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__0___closed__0);
v___x_274_ = lean_byte_array_size(v___x_273_);
return v___x_274_;
}
}
static lean_object* _init_l_Std_Http_Response_instEncodeV11Head___lam__0___closed__4(void){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = ((lean_object*)(l_Std_Http_Response_instEncodeV11Head___lam__0___closed__3));
v___x_278_ = lean_string_to_utf8(v___x_277_);
return v___x_278_;
}
}
static lean_object* _init_l_Std_Http_Response_instEncodeV11Head___lam__0___closed__5(void){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = lean_obj_once(&l_Std_Http_Response_instEncodeV11Head___lam__0___closed__4, &l_Std_Http_Response_instEncodeV11Head___lam__0___closed__4_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__0___closed__4);
v___x_280_ = lean_byte_array_size(v___x_279_);
return v___x_280_;
}
}
static lean_object* _init_l_Std_Http_Response_instEncodeV11Head___lam__0___closed__6(void){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__12));
v___x_282_ = lean_string_to_utf8(v___x_281_);
return v___x_282_;
}
}
static lean_object* _init_l_Std_Http_Response_instEncodeV11Head___lam__0___closed__7(void){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_283_ = lean_obj_once(&l_Std_Http_Response_instEncodeV11Head___lam__0___closed__6, &l_Std_Http_Response_instEncodeV11Head___lam__0___closed__6_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__0___closed__6);
v___x_284_ = lean_byte_array_size(v___x_283_);
return v___x_284_;
}
}
static lean_object* _init_l_Std_Http_Response_instEncodeV11Head___lam__0___closed__8(void){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_285_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__13));
v___x_286_ = lean_string_to_utf8(v___x_285_);
return v___x_286_;
}
}
static lean_object* _init_l_Std_Http_Response_instEncodeV11Head___lam__0___closed__9(void){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_287_ = lean_obj_once(&l_Std_Http_Response_instEncodeV11Head___lam__0___closed__8, &l_Std_Http_Response_instEncodeV11Head___lam__0___closed__8_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__0___closed__8);
v___x_288_ = lean_byte_array_size(v___x_287_);
return v___x_288_;
}
}
static lean_object* _init_l_Std_Http_Response_instEncodeV11Head___lam__0___closed__10(void){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_289_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__14));
v___x_290_ = lean_string_to_utf8(v___x_289_);
return v___x_290_;
}
}
static lean_object* _init_l_Std_Http_Response_instEncodeV11Head___lam__0___closed__11(void){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_291_ = lean_obj_once(&l_Std_Http_Response_instEncodeV11Head___lam__0___closed__10, &l_Std_Http_Response_instEncodeV11Head___lam__0___closed__10_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__0___closed__10);
v___x_292_ = lean_byte_array_size(v___x_291_);
return v___x_292_;
}
}
static lean_object* _init_l_Std_Http_Response_instEncodeV11Head___lam__0___closed__12(void){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_293_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__15));
v___x_294_ = lean_string_to_utf8(v___x_293_);
return v___x_294_;
}
}
static lean_object* _init_l_Std_Http_Response_instEncodeV11Head___lam__0___closed__13(void){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = lean_obj_once(&l_Std_Http_Response_instEncodeV11Head___lam__0___closed__12, &l_Std_Http_Response_instEncodeV11Head___lam__0___closed__12_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__0___closed__12);
v___x_296_ = lean_byte_array_size(v___x_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instEncodeV11Head___lam__0(lean_object* v_out_297_, lean_object* v_r_298_){
_start:
{
lean_object* v_status_299_; uint8_t v_version_300_; lean_object* v_headers_301_; lean_object* v___y_303_; lean_object* v___y_315_; 
v_status_299_ = lean_ctor_get(v_r_298_, 0);
v_version_300_ = lean_ctor_get_uint8(v_r_298_, sizeof(void*)*2);
v_headers_301_ = lean_ctor_get(v_r_298_, 1);
switch(v_version_300_)
{
case 0:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; lean_object* v___x_340_; 
v___x_335_ = lean_obj_once(&l_Std_Http_Response_instEncodeV11Head___lam__0___closed__6, &l_Std_Http_Response_instEncodeV11Head___lam__0___closed__6_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__0___closed__6);
v___x_336_ = lean_unsigned_to_nat(0u);
v___x_337_ = lean_byte_array_size(v_out_297_);
v___x_338_ = lean_obj_once(&l_Std_Http_Response_instEncodeV11Head___lam__0___closed__7, &l_Std_Http_Response_instEncodeV11Head___lam__0___closed__7_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__0___closed__7);
v___x_339_ = 0;
v___x_340_ = lean_byte_array_copy_slice(v___x_335_, v___x_336_, v_out_297_, v___x_337_, v___x_338_, v___x_339_);
v___y_315_ = v___x_340_;
goto v___jp_314_;
}
case 1:
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; uint8_t v___x_345_; lean_object* v___x_346_; 
v___x_341_ = lean_obj_once(&l_Std_Http_Response_instEncodeV11Head___lam__0___closed__8, &l_Std_Http_Response_instEncodeV11Head___lam__0___closed__8_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__0___closed__8);
v___x_342_ = lean_unsigned_to_nat(0u);
v___x_343_ = lean_byte_array_size(v_out_297_);
v___x_344_ = lean_obj_once(&l_Std_Http_Response_instEncodeV11Head___lam__0___closed__9, &l_Std_Http_Response_instEncodeV11Head___lam__0___closed__9_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__0___closed__9);
v___x_345_ = 0;
v___x_346_ = lean_byte_array_copy_slice(v___x_341_, v___x_342_, v_out_297_, v___x_343_, v___x_344_, v___x_345_);
v___y_315_ = v___x_346_;
goto v___jp_314_;
}
case 2:
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; uint8_t v___x_351_; lean_object* v___x_352_; 
v___x_347_ = lean_obj_once(&l_Std_Http_Response_instEncodeV11Head___lam__0___closed__10, &l_Std_Http_Response_instEncodeV11Head___lam__0___closed__10_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__0___closed__10);
v___x_348_ = lean_unsigned_to_nat(0u);
v___x_349_ = lean_byte_array_size(v_out_297_);
v___x_350_ = lean_obj_once(&l_Std_Http_Response_instEncodeV11Head___lam__0___closed__11, &l_Std_Http_Response_instEncodeV11Head___lam__0___closed__11_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__0___closed__11);
v___x_351_ = 0;
v___x_352_ = lean_byte_array_copy_slice(v___x_347_, v___x_348_, v_out_297_, v___x_349_, v___x_350_, v___x_351_);
v___y_315_ = v___x_352_;
goto v___jp_314_;
}
default: 
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; uint8_t v___x_357_; lean_object* v___x_358_; 
v___x_353_ = lean_obj_once(&l_Std_Http_Response_instEncodeV11Head___lam__0___closed__12, &l_Std_Http_Response_instEncodeV11Head___lam__0___closed__12_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__0___closed__12);
v___x_354_ = lean_unsigned_to_nat(0u);
v___x_355_ = lean_byte_array_size(v_out_297_);
v___x_356_ = lean_obj_once(&l_Std_Http_Response_instEncodeV11Head___lam__0___closed__13, &l_Std_Http_Response_instEncodeV11Head___lam__0___closed__13_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__0___closed__13);
v___x_357_ = 0;
v___x_358_ = lean_byte_array_copy_slice(v___x_353_, v___x_354_, v_out_297_, v___x_355_, v___x_356_, v___x_357_);
v___y_315_ = v___x_358_;
goto v___jp_314_;
}
}
v___jp_302_:
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; uint8_t v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_304_ = lean_byte_array_size(v___y_303_);
v___x_305_ = lean_obj_once(&l_Std_Http_Response_instEncodeV11Head___lam__0___closed__0, &l_Std_Http_Response_instEncodeV11Head___lam__0___closed__0_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__0___closed__0);
v___x_306_ = lean_unsigned_to_nat(0u);
v___x_307_ = lean_obj_once(&l_Std_Http_Response_instEncodeV11Head___lam__0___closed__1, &l_Std_Http_Response_instEncodeV11Head___lam__0___closed__1_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__0___closed__1);
v___x_308_ = 0;
v___x_309_ = lean_byte_array_copy_slice(v___x_305_, v___x_306_, v___y_303_, v___x_304_, v___x_307_, v___x_308_);
v___x_310_ = ((lean_object*)(l_Std_Http_Response_instEncodeV11Head___lam__0___closed__2));
v___x_311_ = l_Std_Http_Headers_fold___redArg(v_headers_301_, v___x_309_, v___x_310_);
v___x_312_ = lean_byte_array_size(v___x_311_);
v___x_313_ = lean_byte_array_copy_slice(v___x_305_, v___x_306_, v___x_311_, v___x_312_, v___x_307_, v___x_308_);
return v___x_313_;
}
v___jp_314_:
{
uint8_t v___x_316_; lean_object* v___x_317_; 
v___x_316_ = 32;
v___x_317_ = lean_byte_array_push(v___y_315_, v___x_316_);
if (lean_obj_tag(v_status_299_) == 4)
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; uint8_t v___x_322_; lean_object* v___x_323_; 
v___x_318_ = lean_obj_once(&l_Std_Http_Response_instEncodeV11Head___lam__0___closed__4, &l_Std_Http_Response_instEncodeV11Head___lam__0___closed__4_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__0___closed__4);
v___x_319_ = lean_unsigned_to_nat(0u);
v___x_320_ = lean_byte_array_size(v___x_317_);
v___x_321_ = lean_obj_once(&l_Std_Http_Response_instEncodeV11Head___lam__0___closed__5, &l_Std_Http_Response_instEncodeV11Head___lam__0___closed__5_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__0___closed__5);
v___x_322_ = 0;
v___x_323_ = lean_byte_array_copy_slice(v___x_318_, v___x_319_, v___x_317_, v___x_320_, v___x_321_, v___x_322_);
v___y_303_ = v___x_323_;
goto v___jp_302_;
}
else
{
uint16_t v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; uint8_t v___x_333_; lean_object* v___x_334_; 
v___x_324_ = l_Std_Http_Status_toCode(v_status_299_);
v___x_325_ = lean_uint16_to_nat(v___x_324_);
v___x_326_ = l_Std_Http_Internal_appendNat(v___x_317_, v___x_325_);
v___x_327_ = lean_byte_array_push(v___x_326_, v___x_316_);
v___x_328_ = l_Std_Http_Status_reasonPhrase(v_status_299_);
v___x_329_ = lean_string_to_utf8(v___x_328_);
v___x_330_ = lean_unsigned_to_nat(0u);
v___x_331_ = lean_byte_array_size(v___x_327_);
v___x_332_ = lean_byte_array_size(v___x_329_);
v___x_333_ = 0;
v___x_334_ = lean_byte_array_copy_slice(v___x_329_, v___x_330_, v___x_327_, v___x_331_, v___x_332_, v___x_333_);
lean_dec_ref(v___x_329_);
v___y_303_ = v___x_334_;
goto v___jp_302_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instEncodeV11Head___lam__0___boxed(lean_object* v_out_359_, lean_object* v_r_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Std_Http_Response_instEncodeV11Head___lam__0(v_out_359_, v_r_360_);
lean_dec_ref(v_r_360_);
return v_res_361_;
}
}
static lean_object* _init_l_Std_Http_Response_new___closed__0(void){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_364_ = l_Std_Http_Extensions_empty;
v___x_365_ = lean_obj_once(&l_Std_Http_Response_instInhabitedHead_default___closed__0, &l_Std_Http_Response_instInhabitedHead_default___closed__0_once, _init_l_Std_Http_Response_instInhabitedHead_default___closed__0);
v___x_366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_366_, 0, v___x_365_);
lean_ctor_set(v___x_366_, 1, v___x_364_);
return v___x_366_;
}
}
static lean_object* _init_l_Std_Http_Response_new(void){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = lean_obj_once(&l_Std_Http_Response_new___closed__0, &l_Std_Http_Response_new___closed__0_once, _init_l_Std_Http_Response_new___closed__0);
return v___x_367_;
}
}
static lean_object* _init_l_Std_Http_Response_Builder_new(void){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = lean_obj_once(&l_Std_Http_Response_new___closed__0, &l_Std_Http_Response_new___closed__0_once, _init_l_Std_Http_Response_new___closed__0);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_status(lean_object* v_builder_369_, lean_object* v_status_370_){
_start:
{
lean_object* v_line_371_; lean_object* v_extensions_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_389_; 
v_line_371_ = lean_ctor_get(v_builder_369_, 0);
v_extensions_372_ = lean_ctor_get(v_builder_369_, 1);
v_isSharedCheck_389_ = !lean_is_exclusive(v_builder_369_);
if (v_isSharedCheck_389_ == 0)
{
v___x_374_ = v_builder_369_;
v_isShared_375_ = v_isSharedCheck_389_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_extensions_372_);
lean_inc(v_line_371_);
lean_dec(v_builder_369_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_389_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
uint8_t v_version_376_; lean_object* v_headers_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_387_; 
v_version_376_ = lean_ctor_get_uint8(v_line_371_, sizeof(void*)*2);
v_headers_377_ = lean_ctor_get(v_line_371_, 1);
v_isSharedCheck_387_ = !lean_is_exclusive(v_line_371_);
if (v_isSharedCheck_387_ == 0)
{
lean_object* v_unused_388_; 
v_unused_388_ = lean_ctor_get(v_line_371_, 0);
lean_dec(v_unused_388_);
v___x_379_ = v_line_371_;
v_isShared_380_ = v_isSharedCheck_387_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_headers_377_);
lean_dec(v_line_371_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_387_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_382_; 
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 0, v_status_370_);
v___x_382_ = v___x_379_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v_status_370_);
lean_ctor_set(v_reuseFailAlloc_386_, 1, v_headers_377_);
lean_ctor_set_uint8(v_reuseFailAlloc_386_, sizeof(void*)*2, v_version_376_);
v___x_382_ = v_reuseFailAlloc_386_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
lean_object* v___x_384_; 
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 0, v___x_382_);
v___x_384_ = v___x_374_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v___x_382_);
lean_ctor_set(v_reuseFailAlloc_385_, 1, v_extensions_372_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
return v___x_384_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_headers(lean_object* v_builder_390_, lean_object* v_headers_391_){
_start:
{
lean_object* v_line_392_; lean_object* v_extensions_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_410_; 
v_line_392_ = lean_ctor_get(v_builder_390_, 0);
v_extensions_393_ = lean_ctor_get(v_builder_390_, 1);
v_isSharedCheck_410_ = !lean_is_exclusive(v_builder_390_);
if (v_isSharedCheck_410_ == 0)
{
v___x_395_ = v_builder_390_;
v_isShared_396_ = v_isSharedCheck_410_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_extensions_393_);
lean_inc(v_line_392_);
lean_dec(v_builder_390_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_410_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v_status_397_; uint8_t v_version_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_408_; 
v_status_397_ = lean_ctor_get(v_line_392_, 0);
v_version_398_ = lean_ctor_get_uint8(v_line_392_, sizeof(void*)*2);
v_isSharedCheck_408_ = !lean_is_exclusive(v_line_392_);
if (v_isSharedCheck_408_ == 0)
{
lean_object* v_unused_409_; 
v_unused_409_ = lean_ctor_get(v_line_392_, 1);
lean_dec(v_unused_409_);
v___x_400_ = v_line_392_;
v_isShared_401_ = v_isSharedCheck_408_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_status_397_);
lean_dec(v_line_392_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_408_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_403_; 
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 1, v_headers_391_);
v___x_403_ = v___x_400_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_status_397_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v_headers_391_);
lean_ctor_set_uint8(v_reuseFailAlloc_407_, sizeof(void*)*2, v_version_398_);
v___x_403_ = v_reuseFailAlloc_407_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
lean_object* v___x_405_; 
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 0, v___x_403_);
v___x_405_ = v___x_395_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v___x_403_);
lean_ctor_set(v_reuseFailAlloc_406_, 1, v_extensions_393_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_header(lean_object* v_builder_411_, lean_object* v_key_412_, lean_object* v_value_413_){
_start:
{
lean_object* v_line_414_; lean_object* v_extensions_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_434_; 
v_line_414_ = lean_ctor_get(v_builder_411_, 0);
v_extensions_415_ = lean_ctor_get(v_builder_411_, 1);
v_isSharedCheck_434_ = !lean_is_exclusive(v_builder_411_);
if (v_isSharedCheck_434_ == 0)
{
v___x_417_ = v_builder_411_;
v_isShared_418_ = v_isSharedCheck_434_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_extensions_415_);
lean_inc(v_line_414_);
lean_dec(v_builder_411_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_434_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v_status_419_; uint8_t v_version_420_; lean_object* v_headers_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_433_; 
v_status_419_ = lean_ctor_get(v_line_414_, 0);
v_version_420_ = lean_ctor_get_uint8(v_line_414_, sizeof(void*)*2);
v_headers_421_ = lean_ctor_get(v_line_414_, 1);
v_isSharedCheck_433_ = !lean_is_exclusive(v_line_414_);
if (v_isSharedCheck_433_ == 0)
{
v___x_423_ = v_line_414_;
v_isShared_424_ = v_isSharedCheck_433_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_headers_421_);
lean_inc(v_status_419_);
lean_dec(v_line_414_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_433_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_428_; 
v___x_425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_425_, 0, v_key_412_);
lean_ctor_set(v___x_425_, 1, v_value_413_);
v___x_426_ = lean_array_push(v_headers_421_, v___x_425_);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 1, v___x_426_);
v___x_428_ = v___x_423_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_status_419_);
lean_ctor_set(v_reuseFailAlloc_432_, 1, v___x_426_);
lean_ctor_set_uint8(v_reuseFailAlloc_432_, sizeof(void*)*2, v_version_420_);
v___x_428_ = v_reuseFailAlloc_432_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
lean_object* v___x_430_; 
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 0, v___x_428_);
v___x_430_ = v___x_417_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v___x_428_);
lean_ctor_set(v_reuseFailAlloc_431_, 1, v_extensions_415_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_header_x21(lean_object* v_builder_435_, lean_object* v_key_436_, lean_object* v_value_437_){
_start:
{
lean_object* v_line_438_; lean_object* v_extensions_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_460_; 
v_line_438_ = lean_ctor_get(v_builder_435_, 0);
v_extensions_439_ = lean_ctor_get(v_builder_435_, 1);
v_isSharedCheck_460_ = !lean_is_exclusive(v_builder_435_);
if (v_isSharedCheck_460_ == 0)
{
v___x_441_ = v_builder_435_;
v_isShared_442_ = v_isSharedCheck_460_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_extensions_439_);
lean_inc(v_line_438_);
lean_dec(v_builder_435_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_460_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v_status_443_; uint8_t v_version_444_; lean_object* v_headers_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_459_; 
v_status_443_ = lean_ctor_get(v_line_438_, 0);
v_version_444_ = lean_ctor_get_uint8(v_line_438_, sizeof(void*)*2);
v_headers_445_ = lean_ctor_get(v_line_438_, 1);
v_isSharedCheck_459_ = !lean_is_exclusive(v_line_438_);
if (v_isSharedCheck_459_ == 0)
{
v___x_447_ = v_line_438_;
v_isShared_448_ = v_isSharedCheck_459_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_headers_445_);
lean_inc(v_status_443_);
lean_dec(v_line_438_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_459_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v_key_449_; lean_object* v_value_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_454_; 
v_key_449_ = l_Std_Http_Header_Name_ofString_x21(v_key_436_);
v_value_450_ = l_Std_Http_Header_Value_ofString_x21(v_value_437_);
v___x_451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_451_, 0, v_key_449_);
lean_ctor_set(v___x_451_, 1, v_value_450_);
v___x_452_ = lean_array_push(v_headers_445_, v___x_451_);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 1, v___x_452_);
v___x_454_ = v___x_447_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_status_443_);
lean_ctor_set(v_reuseFailAlloc_458_, 1, v___x_452_);
lean_ctor_set_uint8(v_reuseFailAlloc_458_, sizeof(void*)*2, v_version_444_);
v___x_454_ = v_reuseFailAlloc_458_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
lean_object* v___x_456_; 
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 0, v___x_454_);
v___x_456_ = v___x_441_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v___x_454_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v_extensions_439_);
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
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_header_x3f(lean_object* v_builder_461_, lean_object* v_key_462_, lean_object* v_value_463_){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = l_Std_Http_Header_Name_ofString_x3f(v_key_462_);
if (lean_obj_tag(v___x_464_) == 0)
{
lean_object* v___x_465_; 
lean_dec_ref(v_value_463_);
lean_dec_ref(v_builder_461_);
v___x_465_ = lean_box(0);
return v___x_465_;
}
else
{
lean_object* v_val_466_; lean_object* v___x_467_; 
v_val_466_ = lean_ctor_get(v___x_464_, 0);
lean_inc(v_val_466_);
lean_dec_ref_known(v___x_464_, 1);
v___x_467_ = l_Std_Http_Header_Value_ofString_x3f(v_value_463_);
if (lean_obj_tag(v___x_467_) == 0)
{
lean_object* v___x_468_; 
lean_dec(v_val_466_);
lean_dec_ref(v_builder_461_);
v___x_468_ = lean_box(0);
return v___x_468_;
}
else
{
lean_object* v_line_469_; lean_object* v_val_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_498_; 
v_line_469_ = lean_ctor_get(v_builder_461_, 0);
lean_inc_ref(v_line_469_);
v_val_470_ = lean_ctor_get(v___x_467_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_467_);
if (v_isSharedCheck_498_ == 0)
{
v___x_472_ = v___x_467_;
v_isShared_473_ = v_isSharedCheck_498_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_val_470_);
lean_dec(v___x_467_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_498_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v_extensions_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_496_; 
v_extensions_474_ = lean_ctor_get(v_builder_461_, 1);
v_isSharedCheck_496_ = !lean_is_exclusive(v_builder_461_);
if (v_isSharedCheck_496_ == 0)
{
lean_object* v_unused_497_; 
v_unused_497_ = lean_ctor_get(v_builder_461_, 0);
lean_dec(v_unused_497_);
v___x_476_ = v_builder_461_;
v_isShared_477_ = v_isSharedCheck_496_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_extensions_474_);
lean_dec(v_builder_461_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_496_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v_status_478_; uint8_t v_version_479_; lean_object* v_headers_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_495_; 
v_status_478_ = lean_ctor_get(v_line_469_, 0);
v_version_479_ = lean_ctor_get_uint8(v_line_469_, sizeof(void*)*2);
v_headers_480_ = lean_ctor_get(v_line_469_, 1);
v_isSharedCheck_495_ = !lean_is_exclusive(v_line_469_);
if (v_isSharedCheck_495_ == 0)
{
v___x_482_ = v_line_469_;
v_isShared_483_ = v_isSharedCheck_495_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_headers_480_);
lean_inc(v_status_478_);
lean_dec(v_line_469_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_495_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_487_; 
v___x_484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_484_, 0, v_val_466_);
lean_ctor_set(v___x_484_, 1, v_val_470_);
v___x_485_ = lean_array_push(v_headers_480_, v___x_484_);
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 1, v___x_485_);
v___x_487_ = v___x_482_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_status_478_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v___x_485_);
lean_ctor_set_uint8(v_reuseFailAlloc_494_, sizeof(void*)*2, v_version_479_);
v___x_487_ = v_reuseFailAlloc_494_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
lean_object* v___x_489_; 
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 0, v___x_487_);
v___x_489_ = v___x_476_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v___x_487_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v_extensions_474_);
v___x_489_ = v_reuseFailAlloc_493_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
lean_object* v___x_491_; 
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 0, v___x_489_);
v___x_491_ = v___x_472_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v___x_489_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_extension___redArg(lean_object* v_builder_500_, lean_object* v_inst_501_, lean_object* v_data_502_){
_start:
{
lean_object* v_line_503_; lean_object* v_extensions_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_515_; 
v_line_503_ = lean_ctor_get(v_builder_500_, 0);
v_extensions_504_ = lean_ctor_get(v_builder_500_, 1);
v_isSharedCheck_515_ = !lean_is_exclusive(v_builder_500_);
if (v_isSharedCheck_515_ == 0)
{
v___x_506_ = v_builder_500_;
v_isShared_507_ = v_isSharedCheck_515_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_extensions_504_);
lean_inc(v_line_503_);
lean_dec(v_builder_500_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_515_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v_dyn_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_513_; 
v_dyn_508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_dyn_508_, 0, v_inst_501_);
lean_ctor_set(v_dyn_508_, 1, v_data_502_);
v___x_509_ = ((lean_object*)(l_Std_Http_Response_Builder_extension___redArg___closed__0));
v___x_510_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_dyn_508_);
v___x_511_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_509_, v___x_510_, v_dyn_508_, v_extensions_504_);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 1, v___x_511_);
v___x_513_ = v___x_506_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_line_503_);
lean_ctor_set(v_reuseFailAlloc_514_, 1, v___x_511_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_extension(lean_object* v_00_u03b1_516_, lean_object* v_builder_517_, lean_object* v_inst_518_, lean_object* v_data_519_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = l_Std_Http_Response_Builder_extension___redArg(v_builder_517_, v_inst_518_, v_data_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_body___redArg(lean_object* v_builder_521_, lean_object* v_body_522_){
_start:
{
lean_object* v_line_523_; lean_object* v_extensions_524_; lean_object* v___x_525_; 
v_line_523_ = lean_ctor_get(v_builder_521_, 0);
v_extensions_524_ = lean_ctor_get(v_builder_521_, 1);
lean_inc(v_extensions_524_);
lean_inc_ref(v_line_523_);
v___x_525_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_525_, 0, v_line_523_);
lean_ctor_set(v___x_525_, 1, v_body_522_);
lean_ctor_set(v___x_525_, 2, v_extensions_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_body___redArg___boxed(lean_object* v_builder_526_, lean_object* v_body_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Std_Http_Response_Builder_body___redArg(v_builder_526_, v_body_527_);
lean_dec_ref(v_builder_526_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_body(lean_object* v_t_529_, lean_object* v_builder_530_, lean_object* v_body_531_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = l_Std_Http_Response_Builder_body___redArg(v_builder_530_, v_body_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_body___boxed(lean_object* v_t_533_, lean_object* v_builder_534_, lean_object* v_body_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Std_Http_Response_Builder_body(v_t_533_, v_builder_534_, v_body_535_);
lean_dec_ref(v_builder_534_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_build___redArg(lean_object* v_inst_537_, lean_object* v_builder_538_){
_start:
{
lean_object* v_line_539_; lean_object* v_extensions_540_; lean_object* v___x_541_; 
v_line_539_ = lean_ctor_get(v_builder_538_, 0);
v_extensions_540_ = lean_ctor_get(v_builder_538_, 1);
lean_inc(v_extensions_540_);
lean_inc_ref(v_line_539_);
v___x_541_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_541_, 0, v_line_539_);
lean_ctor_set(v___x_541_, 1, v_inst_537_);
lean_ctor_set(v___x_541_, 2, v_extensions_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_build___redArg___boxed(lean_object* v_inst_542_, lean_object* v_builder_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_Std_Http_Response_Builder_build___redArg(v_inst_542_, v_builder_543_);
lean_dec_ref(v_builder_543_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_build(lean_object* v_t_545_, lean_object* v_inst_546_, lean_object* v_builder_547_){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = l_Std_Http_Response_Builder_build___redArg(v_inst_546_, v_builder_547_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_build___boxed(lean_object* v_t_549_, lean_object* v_inst_550_, lean_object* v_builder_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Std_Http_Response_Builder_build(v_t_549_, v_inst_550_, v_builder_551_);
lean_dec_ref(v_builder_551_);
return v_res_552_;
}
}
static lean_object* _init_l_Std_Http_Response_ok___closed__0(void){
_start:
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_553_ = lean_box(4);
v___x_554_ = l_Std_Http_Response_Builder_new;
v___x_555_ = l_Std_Http_Response_Builder_status(v___x_554_, v___x_553_);
return v___x_555_;
}
}
static lean_object* _init_l_Std_Http_Response_ok(void){
_start:
{
lean_object* v___x_556_; 
v___x_556_ = lean_obj_once(&l_Std_Http_Response_ok___closed__0, &l_Std_Http_Response_ok___closed__0_once, _init_l_Std_Http_Response_ok___closed__0);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_withStatus(lean_object* v_status_557_){
_start:
{
lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_558_ = l_Std_Http_Response_Builder_new;
v___x_559_ = l_Std_Http_Response_Builder_status(v___x_558_, v_status_557_);
return v___x_559_;
}
}
static lean_object* _init_l_Std_Http_Response_notFound___closed__0(void){
_start:
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_560_ = lean_box(27);
v___x_561_ = l_Std_Http_Response_Builder_new;
v___x_562_ = l_Std_Http_Response_Builder_status(v___x_561_, v___x_560_);
return v___x_562_;
}
}
static lean_object* _init_l_Std_Http_Response_notFound(void){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = lean_obj_once(&l_Std_Http_Response_notFound___closed__0, &l_Std_Http_Response_notFound___closed__0_once, _init_l_Std_Http_Response_notFound___closed__0);
return v___x_563_;
}
}
static lean_object* _init_l_Std_Http_Response_internalServerError___closed__0(void){
_start:
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_564_ = lean_box(52);
v___x_565_ = l_Std_Http_Response_Builder_new;
v___x_566_ = l_Std_Http_Response_Builder_status(v___x_565_, v___x_564_);
return v___x_566_;
}
}
static lean_object* _init_l_Std_Http_Response_internalServerError(void){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = lean_obj_once(&l_Std_Http_Response_internalServerError___closed__0, &l_Std_Http_Response_internalServerError___closed__0_once, _init_l_Std_Http_Response_internalServerError___closed__0);
return v___x_567_;
}
}
static lean_object* _init_l_Std_Http_Response_badRequest___closed__0(void){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_568_ = lean_box(23);
v___x_569_ = l_Std_Http_Response_Builder_new;
v___x_570_ = l_Std_Http_Response_Builder_status(v___x_569_, v___x_568_);
return v___x_570_;
}
}
static lean_object* _init_l_Std_Http_Response_badRequest(void){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = lean_obj_once(&l_Std_Http_Response_badRequest___closed__0, &l_Std_Http_Response_badRequest___closed__0_once, _init_l_Std_Http_Response_badRequest___closed__0);
return v___x_571_;
}
}
static lean_object* _init_l_Std_Http_Response_created___closed__0(void){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_572_ = lean_box(5);
v___x_573_ = l_Std_Http_Response_Builder_new;
v___x_574_ = l_Std_Http_Response_Builder_status(v___x_573_, v___x_572_);
return v___x_574_;
}
}
static lean_object* _init_l_Std_Http_Response_created(void){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = lean_obj_once(&l_Std_Http_Response_created___closed__0, &l_Std_Http_Response_created___closed__0_once, _init_l_Std_Http_Response_created___closed__0);
return v___x_575_;
}
}
static lean_object* _init_l_Std_Http_Response_accepted___closed__0(void){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_576_ = lean_box(6);
v___x_577_ = l_Std_Http_Response_Builder_new;
v___x_578_ = l_Std_Http_Response_Builder_status(v___x_577_, v___x_576_);
return v___x_578_;
}
}
static lean_object* _init_l_Std_Http_Response_accepted(void){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = lean_obj_once(&l_Std_Http_Response_accepted___closed__0, &l_Std_Http_Response_accepted___closed__0_once, _init_l_Std_Http_Response_accepted___closed__0);
return v___x_579_;
}
}
static lean_object* _init_l_Std_Http_Response_unauthorized___closed__0(void){
_start:
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_580_ = lean_box(24);
v___x_581_ = l_Std_Http_Response_Builder_new;
v___x_582_ = l_Std_Http_Response_Builder_status(v___x_581_, v___x_580_);
return v___x_582_;
}
}
static lean_object* _init_l_Std_Http_Response_unauthorized(void){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = lean_obj_once(&l_Std_Http_Response_unauthorized___closed__0, &l_Std_Http_Response_unauthorized___closed__0_once, _init_l_Std_Http_Response_unauthorized___closed__0);
return v___x_583_;
}
}
static lean_object* _init_l_Std_Http_Response_forbidden___closed__0(void){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_584_ = lean_box(26);
v___x_585_ = l_Std_Http_Response_Builder_new;
v___x_586_ = l_Std_Http_Response_Builder_status(v___x_585_, v___x_584_);
return v___x_586_;
}
}
static lean_object* _init_l_Std_Http_Response_forbidden(void){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = lean_obj_once(&l_Std_Http_Response_forbidden___closed__0, &l_Std_Http_Response_forbidden___closed__0_once, _init_l_Std_Http_Response_forbidden___closed__0);
return v___x_587_;
}
}
static lean_object* _init_l_Std_Http_Response_conflict___closed__0(void){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_588_ = lean_box(32);
v___x_589_ = l_Std_Http_Response_Builder_new;
v___x_590_ = l_Std_Http_Response_Builder_status(v___x_589_, v___x_588_);
return v___x_590_;
}
}
static lean_object* _init_l_Std_Http_Response_conflict(void){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = lean_obj_once(&l_Std_Http_Response_conflict___closed__0, &l_Std_Http_Response_conflict___closed__0_once, _init_l_Std_Http_Response_conflict___closed__0);
return v___x_591_;
}
}
static lean_object* _init_l_Std_Http_Response_serviceUnavailable___closed__0(void){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_592_ = lean_box(55);
v___x_593_ = l_Std_Http_Response_Builder_new;
v___x_594_ = l_Std_Http_Response_Builder_status(v___x_593_, v___x_592_);
return v___x_594_;
}
}
static lean_object* _init_l_Std_Http_Response_serviceUnavailable(void){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = lean_obj_once(&l_Std_Http_Response_serviceUnavailable___closed__0, &l_Std_Http_Response_serviceUnavailable___closed__0_once, _init_l_Std_Http_Response_serviceUnavailable___closed__0);
return v___x_595_;
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
