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
extern lean_object* l_Std_Http_instInhabitedHeaders_default;
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
lean_object* l_String_splitOnAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Http_instInhabitedExtensions_default;
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint16_t l_Std_Http_Status_toCode(lean_object*);
lean_object* lean_uint16_to_nat(uint16_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Std_Http_Status_reasonPhrase(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Std_Http_Extensions_compareName___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Dynamic_0__Dynamic_typeNameImpl(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
extern lean_object* l_Std_Http_Extensions_empty;
extern lean_object* l_Std_Http_Headers_empty;
lean_object* l_Std_Http_instReprStatus_repr(lean_object*, lean_object*);
lean_object* l_Std_Http_instReprVersion_repr(uint8_t, lean_object*);
lean_object* l_Std_Http_instReprHeaders_repr___redArg(lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_uint32_to_uint8(uint32_t);
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
LEAN_EXPORT lean_object* l_Std_Http_Response_instToStringHead___lam__0(lean_object*);
static const lean_string_object l_Std_Http_Response_instToStringHead___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Std_Http_Response_instToStringHead___lam__1___closed__0 = (const lean_object*)&l_Std_Http_Response_instToStringHead___lam__1___closed__0_value;
static const lean_string_object l_Std_Http_Response_instToStringHead___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Std_Http_Response_instToStringHead___lam__1___closed__1 = (const lean_object*)&l_Std_Http_Response_instToStringHead___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Response_instToStringHead___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_instToStringHead___lam__1___boxed(lean_object*, lean_object*);
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
static const lean_closure_object l_Std_Http_Response_instToStringHead___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Response_instToStringHead___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Response_instToStringHead___closed__0 = (const lean_object*)&l_Std_Http_Response_instToStringHead___closed__0_value;
static const lean_closure_object l_Std_Http_Response_instToStringHead___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Response_instToStringHead___lam__1___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Response_instToStringHead___closed__0_value)} };
static const lean_object* l_Std_Http_Response_instToStringHead___closed__1 = (const lean_object*)&l_Std_Http_Response_instToStringHead___closed__1_value;
static const lean_closure_object l_Std_Http_Response_instToStringHead___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Response_instToStringHead___lam__2, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Response_instToStringHead___closed__1_value)} };
static const lean_object* l_Std_Http_Response_instToStringHead___closed__2 = (const lean_object*)&l_Std_Http_Response_instToStringHead___closed__2_value;
LEAN_EXPORT const lean_object* l_Std_Http_Response_instToStringHead = (const lean_object*)&l_Std_Http_Response_instToStringHead___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Http_Response_instEncodeV11Head___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_instEncodeV11Head___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Http_Response_instEncodeV11Head___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_Response_instEncodeV11Head___lam__0___closed__0;
static lean_once_cell_t l_Std_Http_Response_instEncodeV11Head___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_instEncodeV11Head___lam__0___closed__1;
static lean_once_cell_t l_Std_Http_Response_instEncodeV11Head___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_instEncodeV11Head___lam__0___closed__2;
static lean_once_cell_t l_Std_Http_Response_instEncodeV11Head___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_instEncodeV11Head___lam__0___closed__3;
static lean_once_cell_t l_Std_Http_Response_instEncodeV11Head___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_instEncodeV11Head___lam__0___closed__4;
LEAN_EXPORT lean_object* l_Std_Http_Response_instEncodeV11Head___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_instEncodeV11Head___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Response_instEncodeV11Head___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Response_instEncodeV11Head___lam__1___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Response_instToStringHead___closed__0_value)} };
static const lean_object* l_Std_Http_Response_instEncodeV11Head___closed__0 = (const lean_object*)&l_Std_Http_Response_instEncodeV11Head___closed__0_value;
static const lean_closure_object l_Std_Http_Response_instEncodeV11Head___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Response_instEncodeV11Head___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Response_instEncodeV11Head___closed__0_value)} };
static const lean_object* l_Std_Http_Response_instEncodeV11Head___closed__1 = (const lean_object*)&l_Std_Http_Response_instEncodeV11Head___closed__1_value;
LEAN_EXPORT const lean_object* l_Std_Http_Response_instEncodeV11Head = (const lean_object*)&l_Std_Http_Response_instEncodeV11Head___closed__1_value;
static lean_once_cell_t l_Std_Http_Response_new___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_new___closed__0;
static lean_once_cell_t l_Std_Http_Response_new___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_new___closed__1;
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
v___x_1_ = l_Std_Http_instInhabitedHeaders_default;
v___x_2_ = 0;
v___x_3_ = lean_box(0);
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
v___x_94_ = l_Std_Http_Response_instInhabitedHead_default;
v___x_95_ = l_Std_Http_instInhabitedExtensions_default;
v___x_96_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_96_, 0, v___x_94_);
lean_ctor_set(v___x_96_, 1, v_inst_93_);
lean_ctor_set(v___x_96_, 2, v___x_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instInhabitedResponse_default(lean_object* v_a_97_, lean_object* v_inst_98_){
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
LEAN_EXPORT lean_object* l_Std_Http_Response_instToStringHead___lam__0(lean_object* v_x_105_){
_start:
{
lean_object* v___x_106_; uint32_t v___x_107_; uint32_t v___x_108_; uint8_t v___x_109_; 
v___x_106_ = lean_unsigned_to_nat(0u);
v___x_107_ = lean_string_utf8_get(v_x_105_, v___x_106_);
v___x_108_ = 97;
v___x_109_ = lean_uint32_dec_le(v___x_108_, v___x_107_);
if (v___x_109_ == 0)
{
lean_object* v___x_110_; 
v___x_110_ = lean_string_utf8_set(v_x_105_, v___x_106_, v___x_107_);
return v___x_110_;
}
else
{
uint32_t v___x_111_; uint8_t v___x_112_; 
v___x_111_ = 122;
v___x_112_ = lean_uint32_dec_le(v___x_107_, v___x_111_);
if (v___x_112_ == 0)
{
lean_object* v___x_113_; 
v___x_113_ = lean_string_utf8_set(v_x_105_, v___x_106_, v___x_107_);
return v___x_113_;
}
else
{
uint32_t v___x_114_; uint32_t v___x_115_; lean_object* v___x_116_; 
v___x_114_ = 4294967264;
v___x_115_ = lean_uint32_add(v___x_107_, v___x_114_);
v___x_116_ = lean_string_utf8_set(v_x_105_, v___x_106_, v___x_115_);
return v___x_116_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instToStringHead___lam__1(lean_object* v___f_119_, lean_object* v_x_120_){
_start:
{
lean_object* v_fst_121_; lean_object* v_snd_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v_it_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v_fst_121_ = lean_ctor_get(v_x_120_, 0);
v_snd_122_ = lean_ctor_get(v_x_120_, 1);
v___x_123_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__1___closed__0));
v___x_124_ = lean_unsigned_to_nat(0u);
v___x_125_ = lean_box(0);
v___x_126_ = l_String_splitOnAux(v_fst_121_, v___x_123_, v___x_124_, v___x_124_, v___x_124_, v___x_125_);
v_it_127_ = l_List_mapTR_loop___redArg(v___f_119_, v___x_126_, v___x_125_);
v___x_128_ = l_String_intercalate(v___x_123_, v_it_127_);
v___x_129_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__1___closed__1));
v___x_130_ = lean_string_append(v___x_128_, v___x_129_);
v___x_131_ = lean_string_append(v___x_130_, v_snd_122_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instToStringHead___lam__1___boxed(lean_object* v___f_132_, lean_object* v_x_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l_Std_Http_Response_instToStringHead___lam__1(v___f_132_, v_x_133_);
lean_dec_ref(v_x_133_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instToStringHead___lam__2(lean_object* v___f_160_, lean_object* v_r_161_){
_start:
{
lean_object* v_status_162_; uint8_t v_version_163_; lean_object* v_headers_164_; lean_object* v___y_166_; 
v_status_162_ = lean_ctor_get(v_r_161_, 0);
lean_inc(v_status_162_);
v_version_163_ = lean_ctor_get_uint8(v_r_161_, sizeof(void*)*2);
v_headers_164_ = lean_ctor_get(v_r_161_, 1);
lean_inc_ref(v_headers_164_);
lean_dec_ref(v_r_161_);
switch(v_version_163_)
{
case 0:
{
lean_object* v___x_187_; 
v___x_187_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__12));
v___y_166_ = v___x_187_;
goto v___jp_165_;
}
case 1:
{
lean_object* v___x_188_; 
v___x_188_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__13));
v___y_166_ = v___x_188_;
goto v___jp_165_;
}
case 2:
{
lean_object* v___x_189_; 
v___x_189_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__14));
v___y_166_ = v___x_189_;
goto v___jp_165_;
}
default: 
{
lean_object* v___x_190_; 
v___x_190_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__15));
v___y_166_ = v___x_190_;
goto v___jp_165_;
}
}
v___jp_165_:
{
lean_object* v_entries_167_; lean_object* v___x_168_; lean_object* v___x_169_; uint16_t v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; size_t v_sz_180_; size_t v___x_181_; lean_object* v_pairs_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v_entries_167_ = lean_ctor_get(v_headers_164_, 0);
lean_inc_ref(v_entries_167_);
lean_dec_ref(v_headers_164_);
v___x_168_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__0));
lean_inc_ref(v___y_166_);
v___x_169_ = lean_string_append(v___y_166_, v___x_168_);
v___x_170_ = l_Std_Http_Status_toCode(v_status_162_);
v___x_171_ = lean_uint16_to_nat(v___x_170_);
v___x_172_ = l_Nat_reprFast(v___x_171_);
v___x_173_ = lean_string_append(v___x_169_, v___x_172_);
lean_dec_ref(v___x_172_);
v___x_174_ = lean_string_append(v___x_173_, v___x_168_);
v___x_175_ = l_Std_Http_Status_reasonPhrase(v_status_162_);
lean_dec(v_status_162_);
v___x_176_ = lean_string_append(v___x_174_, v___x_175_);
lean_dec_ref(v___x_175_);
v___x_177_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__1));
v___x_178_ = lean_string_append(v___x_176_, v___x_177_);
v___x_179_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__11));
v_sz_180_ = lean_array_size(v_entries_167_);
v___x_181_ = ((size_t)0ULL);
v_pairs_182_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_179_, v___f_160_, v_sz_180_, v___x_181_, v_entries_167_);
v___x_183_ = lean_array_to_list(v_pairs_182_);
v___x_184_ = l_String_intercalate(v___x_177_, v___x_183_);
v___x_185_ = lean_string_append(v___x_178_, v___x_184_);
lean_dec_ref(v___x_184_);
v___x_186_ = lean_string_append(v___x_185_, v___x_177_);
return v___x_186_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instEncodeV11Head___lam__1(lean_object* v___f_197_, lean_object* v_buf_198_, lean_object* v_name_199_, lean_object* v_value_200_){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v_data_205_; lean_object* v_size_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_224_; 
v___x_201_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__1___closed__0));
v___x_202_ = lean_unsigned_to_nat(0u);
v___x_203_ = lean_box(0);
v___x_204_ = l_String_splitOnAux(v_name_199_, v___x_201_, v___x_202_, v___x_202_, v___x_202_, v___x_203_);
v_data_205_ = lean_ctor_get(v_buf_198_, 0);
v_size_206_ = lean_ctor_get(v_buf_198_, 1);
v_isSharedCheck_224_ = !lean_is_exclusive(v_buf_198_);
if (v_isSharedCheck_224_ == 0)
{
v___x_208_ = v_buf_198_;
v_isShared_209_ = v_isSharedCheck_224_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_size_206_);
lean_inc(v_data_205_);
lean_dec(v_buf_198_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_224_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v_it_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_222_; 
v_it_210_ = l_List_mapTR_loop___redArg(v___f_197_, v___x_204_, v___x_203_);
v___x_211_ = l_String_intercalate(v___x_201_, v_it_210_);
v___x_212_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__1___closed__1));
v___x_213_ = lean_string_append(v___x_211_, v___x_212_);
v___x_214_ = lean_string_append(v___x_213_, v_value_200_);
v___x_215_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__1));
v___x_216_ = lean_string_append(v___x_214_, v___x_215_);
v___x_217_ = lean_string_to_utf8(v___x_216_);
lean_dec_ref(v___x_216_);
lean_inc_ref(v___x_217_);
v___x_218_ = lean_array_push(v_data_205_, v___x_217_);
v___x_219_ = lean_byte_array_size(v___x_217_);
lean_dec_ref(v___x_217_);
v___x_220_ = lean_nat_add(v_size_206_, v___x_219_);
lean_dec(v_size_206_);
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 1, v___x_220_);
lean_ctor_set(v___x_208_, 0, v___x_218_);
v___x_222_ = v___x_208_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v___x_218_);
lean_ctor_set(v_reuseFailAlloc_223_, 1, v___x_220_);
v___x_222_ = v_reuseFailAlloc_223_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
return v___x_222_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instEncodeV11Head___lam__1___boxed(lean_object* v___f_225_, lean_object* v_buf_226_, lean_object* v_name_227_, lean_object* v_value_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Std_Http_Response_instEncodeV11Head___lam__1(v___f_225_, v_buf_226_, v_name_227_, v_value_228_);
lean_dec_ref(v_value_228_);
lean_dec_ref(v_name_227_);
return v_res_229_;
}
}
static uint8_t _init_l_Std_Http_Response_instEncodeV11Head___lam__0___closed__0(void){
_start:
{
uint32_t v___x_230_; uint8_t v___x_231_; 
v___x_230_ = 32;
v___x_231_ = lean_uint32_to_uint8(v___x_230_);
return v___x_231_;
}
}
static lean_object* _init_l_Std_Http_Response_instEncodeV11Head___lam__0___closed__1(void){
_start:
{
uint8_t v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_232_ = lean_uint8_once(&l_Std_Http_Response_instEncodeV11Head___lam__0___closed__0, &l_Std_Http_Response_instEncodeV11Head___lam__0___closed__0_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__0___closed__0);
v___x_233_ = lean_unsigned_to_nat(1u);
v___x_234_ = lean_mk_empty_array_with_capacity(v___x_233_);
v___x_235_ = lean_box(v___x_232_);
v___x_236_ = lean_array_push(v___x_234_, v___x_235_);
v___x_237_ = lean_byte_array_mk(v___x_236_);
return v___x_237_;
}
}
static lean_object* _init_l_Std_Http_Response_instEncodeV11Head___lam__0___closed__2(void){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = lean_obj_once(&l_Std_Http_Response_instEncodeV11Head___lam__0___closed__1, &l_Std_Http_Response_instEncodeV11Head___lam__0___closed__1_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__0___closed__1);
v___x_239_ = lean_byte_array_size(v___x_238_);
return v___x_239_;
}
}
static lean_object* _init_l_Std_Http_Response_instEncodeV11Head___lam__0___closed__3(void){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_240_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__1));
v___x_241_ = lean_string_to_utf8(v___x_240_);
return v___x_241_;
}
}
static lean_object* _init_l_Std_Http_Response_instEncodeV11Head___lam__0___closed__4(void){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_242_ = lean_obj_once(&l_Std_Http_Response_instEncodeV11Head___lam__0___closed__3, &l_Std_Http_Response_instEncodeV11Head___lam__0___closed__3_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__0___closed__3);
v___x_243_ = lean_byte_array_size(v___x_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instEncodeV11Head___lam__0(lean_object* v___f_244_, lean_object* v_buffer_245_, lean_object* v_r_246_){
_start:
{
lean_object* v_status_247_; uint8_t v_version_248_; lean_object* v_headers_249_; lean_object* v___y_251_; 
v_status_247_ = lean_ctor_get(v_r_246_, 0);
v_version_248_ = lean_ctor_get_uint8(v_r_246_, sizeof(void*)*2);
v_headers_249_ = lean_ctor_get(v_r_246_, 1);
switch(v_version_248_)
{
case 0:
{
lean_object* v___x_299_; 
v___x_299_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__12));
v___y_251_ = v___x_299_;
goto v___jp_250_;
}
case 1:
{
lean_object* v___x_300_; 
v___x_300_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__13));
v___y_251_ = v___x_300_;
goto v___jp_250_;
}
case 2:
{
lean_object* v___x_301_; 
v___x_301_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__14));
v___y_251_ = v___x_301_;
goto v___jp_250_;
}
default: 
{
lean_object* v___x_302_; 
v___x_302_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__2___closed__15));
v___y_251_ = v___x_302_;
goto v___jp_250_;
}
}
v___jp_250_:
{
lean_object* v_data_252_; lean_object* v_size_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_298_; 
v_data_252_ = lean_ctor_get(v_buffer_245_, 0);
v_size_253_ = lean_ctor_get(v_buffer_245_, 1);
v_isSharedCheck_298_ = !lean_is_exclusive(v_buffer_245_);
if (v_isSharedCheck_298_ == 0)
{
v___x_255_ = v_buffer_245_;
v_isShared_256_ = v_isSharedCheck_298_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_size_253_);
lean_inc(v_data_252_);
lean_dec(v_buffer_245_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_298_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; uint16_t v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v_buffer_284_; 
v___x_257_ = lean_string_to_utf8(v___y_251_);
lean_inc_ref(v___x_257_);
v___x_258_ = lean_array_push(v_data_252_, v___x_257_);
v___x_259_ = lean_byte_array_size(v___x_257_);
lean_dec_ref(v___x_257_);
v___x_260_ = lean_nat_add(v_size_253_, v___x_259_);
lean_dec(v_size_253_);
v___x_261_ = lean_obj_once(&l_Std_Http_Response_instEncodeV11Head___lam__0___closed__1, &l_Std_Http_Response_instEncodeV11Head___lam__0___closed__1_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__0___closed__1);
v___x_262_ = lean_array_push(v___x_258_, v___x_261_);
v___x_263_ = lean_obj_once(&l_Std_Http_Response_instEncodeV11Head___lam__0___closed__2, &l_Std_Http_Response_instEncodeV11Head___lam__0___closed__2_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__0___closed__2);
v___x_264_ = lean_nat_add(v___x_260_, v___x_263_);
lean_dec(v___x_260_);
v___x_265_ = l_Std_Http_Status_toCode(v_status_247_);
v___x_266_ = lean_uint16_to_nat(v___x_265_);
v___x_267_ = l_Nat_reprFast(v___x_266_);
v___x_268_ = lean_string_to_utf8(v___x_267_);
lean_dec_ref(v___x_267_);
lean_inc_ref(v___x_268_);
v___x_269_ = lean_array_push(v___x_262_, v___x_268_);
v___x_270_ = lean_byte_array_size(v___x_268_);
lean_dec_ref(v___x_268_);
v___x_271_ = lean_nat_add(v___x_264_, v___x_270_);
lean_dec(v___x_264_);
v___x_272_ = lean_array_push(v___x_269_, v___x_261_);
v___x_273_ = lean_nat_add(v___x_271_, v___x_263_);
lean_dec(v___x_271_);
v___x_274_ = l_Std_Http_Status_reasonPhrase(v_status_247_);
v___x_275_ = lean_string_to_utf8(v___x_274_);
lean_dec_ref(v___x_274_);
lean_inc_ref(v___x_275_);
v___x_276_ = lean_array_push(v___x_272_, v___x_275_);
v___x_277_ = lean_byte_array_size(v___x_275_);
lean_dec_ref(v___x_275_);
v___x_278_ = lean_nat_add(v___x_273_, v___x_277_);
lean_dec(v___x_273_);
v___x_279_ = lean_obj_once(&l_Std_Http_Response_instEncodeV11Head___lam__0___closed__3, &l_Std_Http_Response_instEncodeV11Head___lam__0___closed__3_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__0___closed__3);
v___x_280_ = lean_array_push(v___x_276_, v___x_279_);
v___x_281_ = lean_obj_once(&l_Std_Http_Response_instEncodeV11Head___lam__0___closed__4, &l_Std_Http_Response_instEncodeV11Head___lam__0___closed__4_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__0___closed__4);
v___x_282_ = lean_nat_add(v___x_278_, v___x_281_);
lean_dec(v___x_278_);
if (v_isShared_256_ == 0)
{
lean_ctor_set(v___x_255_, 1, v___x_282_);
lean_ctor_set(v___x_255_, 0, v___x_280_);
v_buffer_284_ = v___x_255_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v___x_280_);
lean_ctor_set(v_reuseFailAlloc_297_, 1, v___x_282_);
v_buffer_284_ = v_reuseFailAlloc_297_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
lean_object* v_buffer_285_; lean_object* v_data_286_; lean_object* v_size_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_296_; 
v_buffer_285_ = l_Std_Http_Headers_fold___redArg(v_headers_249_, v_buffer_284_, v___f_244_);
v_data_286_ = lean_ctor_get(v_buffer_285_, 0);
v_size_287_ = lean_ctor_get(v_buffer_285_, 1);
v_isSharedCheck_296_ = !lean_is_exclusive(v_buffer_285_);
if (v_isSharedCheck_296_ == 0)
{
v___x_289_ = v_buffer_285_;
v_isShared_290_ = v_isSharedCheck_296_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_size_287_);
lean_inc(v_data_286_);
lean_dec(v_buffer_285_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_296_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_294_; 
v___x_291_ = lean_array_push(v_data_286_, v___x_279_);
v___x_292_ = lean_nat_add(v_size_287_, v___x_281_);
lean_dec(v_size_287_);
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 1, v___x_292_);
lean_ctor_set(v___x_289_, 0, v___x_291_);
v___x_294_ = v___x_289_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v___x_291_);
lean_ctor_set(v_reuseFailAlloc_295_, 1, v___x_292_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instEncodeV11Head___lam__0___boxed(lean_object* v___f_303_, lean_object* v_buffer_304_, lean_object* v_r_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Std_Http_Response_instEncodeV11Head___lam__0(v___f_303_, v_buffer_304_, v_r_305_);
lean_dec_ref(v_r_305_);
return v_res_306_;
}
}
static lean_object* _init_l_Std_Http_Response_new___closed__0(void){
_start:
{
lean_object* v___x_312_; uint8_t v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_312_ = l_Std_Http_Headers_empty;
v___x_313_ = 1;
v___x_314_ = lean_box(4);
v___x_315_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_315_, 0, v___x_314_);
lean_ctor_set(v___x_315_, 1, v___x_312_);
lean_ctor_set_uint8(v___x_315_, sizeof(void*)*2, v___x_313_);
return v___x_315_;
}
}
static lean_object* _init_l_Std_Http_Response_new___closed__1(void){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_316_ = l_Std_Http_Extensions_empty;
v___x_317_ = lean_obj_once(&l_Std_Http_Response_new___closed__0, &l_Std_Http_Response_new___closed__0_once, _init_l_Std_Http_Response_new___closed__0);
v___x_318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
lean_ctor_set(v___x_318_, 1, v___x_316_);
return v___x_318_;
}
}
static lean_object* _init_l_Std_Http_Response_new(void){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = lean_obj_once(&l_Std_Http_Response_new___closed__1, &l_Std_Http_Response_new___closed__1_once, _init_l_Std_Http_Response_new___closed__1);
return v___x_319_;
}
}
static lean_object* _init_l_Std_Http_Response_Builder_new(void){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = lean_obj_once(&l_Std_Http_Response_new___closed__1, &l_Std_Http_Response_new___closed__1_once, _init_l_Std_Http_Response_new___closed__1);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_status(lean_object* v_builder_321_, lean_object* v_status_322_){
_start:
{
lean_object* v_line_323_; lean_object* v_extensions_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_341_; 
v_line_323_ = lean_ctor_get(v_builder_321_, 0);
v_extensions_324_ = lean_ctor_get(v_builder_321_, 1);
v_isSharedCheck_341_ = !lean_is_exclusive(v_builder_321_);
if (v_isSharedCheck_341_ == 0)
{
v___x_326_ = v_builder_321_;
v_isShared_327_ = v_isSharedCheck_341_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_extensions_324_);
lean_inc(v_line_323_);
lean_dec(v_builder_321_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_341_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
uint8_t v_version_328_; lean_object* v_headers_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_339_; 
v_version_328_ = lean_ctor_get_uint8(v_line_323_, sizeof(void*)*2);
v_headers_329_ = lean_ctor_get(v_line_323_, 1);
v_isSharedCheck_339_ = !lean_is_exclusive(v_line_323_);
if (v_isSharedCheck_339_ == 0)
{
lean_object* v_unused_340_; 
v_unused_340_ = lean_ctor_get(v_line_323_, 0);
lean_dec(v_unused_340_);
v___x_331_ = v_line_323_;
v_isShared_332_ = v_isSharedCheck_339_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_headers_329_);
lean_dec(v_line_323_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_339_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_334_; 
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 0, v_status_322_);
v___x_334_ = v___x_331_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_status_322_);
lean_ctor_set(v_reuseFailAlloc_338_, 1, v_headers_329_);
lean_ctor_set_uint8(v_reuseFailAlloc_338_, sizeof(void*)*2, v_version_328_);
v___x_334_ = v_reuseFailAlloc_338_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
lean_object* v___x_336_; 
if (v_isShared_327_ == 0)
{
lean_ctor_set(v___x_326_, 0, v___x_334_);
v___x_336_ = v___x_326_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v___x_334_);
lean_ctor_set(v_reuseFailAlloc_337_, 1, v_extensions_324_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_headers(lean_object* v_builder_342_, lean_object* v_headers_343_){
_start:
{
lean_object* v_line_344_; lean_object* v_extensions_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_362_; 
v_line_344_ = lean_ctor_get(v_builder_342_, 0);
v_extensions_345_ = lean_ctor_get(v_builder_342_, 1);
v_isSharedCheck_362_ = !lean_is_exclusive(v_builder_342_);
if (v_isSharedCheck_362_ == 0)
{
v___x_347_ = v_builder_342_;
v_isShared_348_ = v_isSharedCheck_362_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_extensions_345_);
lean_inc(v_line_344_);
lean_dec(v_builder_342_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_362_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v_status_349_; uint8_t v_version_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_360_; 
v_status_349_ = lean_ctor_get(v_line_344_, 0);
v_version_350_ = lean_ctor_get_uint8(v_line_344_, sizeof(void*)*2);
v_isSharedCheck_360_ = !lean_is_exclusive(v_line_344_);
if (v_isSharedCheck_360_ == 0)
{
lean_object* v_unused_361_; 
v_unused_361_ = lean_ctor_get(v_line_344_, 1);
lean_dec(v_unused_361_);
v___x_352_ = v_line_344_;
v_isShared_353_ = v_isSharedCheck_360_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_status_349_);
lean_dec(v_line_344_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_360_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_355_; 
if (v_isShared_353_ == 0)
{
lean_ctor_set(v___x_352_, 1, v_headers_343_);
v___x_355_ = v___x_352_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_status_349_);
lean_ctor_set(v_reuseFailAlloc_359_, 1, v_headers_343_);
lean_ctor_set_uint8(v_reuseFailAlloc_359_, sizeof(void*)*2, v_version_350_);
v___x_355_ = v_reuseFailAlloc_359_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
lean_object* v___x_357_; 
if (v_isShared_348_ == 0)
{
lean_ctor_set(v___x_347_, 0, v___x_355_);
v___x_357_ = v___x_347_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v___x_355_);
lean_ctor_set(v_reuseFailAlloc_358_, 1, v_extensions_345_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0___redArg(lean_object* v_a_363_, lean_object* v_x_364_){
_start:
{
if (lean_obj_tag(v_x_364_) == 0)
{
uint8_t v___x_365_; 
v___x_365_ = 0;
return v___x_365_;
}
else
{
lean_object* v_key_366_; lean_object* v_tail_367_; uint8_t v___x_368_; 
v_key_366_ = lean_ctor_get(v_x_364_, 0);
v_tail_367_ = lean_ctor_get(v_x_364_, 2);
v___x_368_ = lean_string_dec_eq(v_key_366_, v_a_363_);
if (v___x_368_ == 0)
{
v_x_364_ = v_tail_367_;
goto _start;
}
else
{
return v___x_368_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0___redArg___boxed(lean_object* v_a_370_, lean_object* v_x_371_){
_start:
{
uint8_t v_res_372_; lean_object* v_r_373_; 
v_res_372_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0___redArg(v_a_370_, v_x_371_);
lean_dec(v_x_371_);
lean_dec_ref(v_a_370_);
v_r_373_ = lean_box(v_res_372_);
return v_r_373_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_374_, lean_object* v_x_375_){
_start:
{
if (lean_obj_tag(v_x_375_) == 0)
{
return v_x_374_;
}
else
{
lean_object* v_key_376_; lean_object* v_value_377_; lean_object* v_tail_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_401_; 
v_key_376_ = lean_ctor_get(v_x_375_, 0);
v_value_377_ = lean_ctor_get(v_x_375_, 1);
v_tail_378_ = lean_ctor_get(v_x_375_, 2);
v_isSharedCheck_401_ = !lean_is_exclusive(v_x_375_);
if (v_isSharedCheck_401_ == 0)
{
v___x_380_ = v_x_375_;
v_isShared_381_ = v_isSharedCheck_401_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_tail_378_);
lean_inc(v_value_377_);
lean_inc(v_key_376_);
lean_dec(v_x_375_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_401_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v___x_382_; uint64_t v___x_383_; uint64_t v___x_384_; uint64_t v___x_385_; uint64_t v_fold_386_; uint64_t v___x_387_; uint64_t v___x_388_; uint64_t v___x_389_; size_t v___x_390_; size_t v___x_391_; size_t v___x_392_; size_t v___x_393_; size_t v___x_394_; lean_object* v___x_395_; lean_object* v___x_397_; 
v___x_382_ = lean_array_get_size(v_x_374_);
v___x_383_ = lean_string_hash(v_key_376_);
v___x_384_ = 32ULL;
v___x_385_ = lean_uint64_shift_right(v___x_383_, v___x_384_);
v_fold_386_ = lean_uint64_xor(v___x_383_, v___x_385_);
v___x_387_ = 16ULL;
v___x_388_ = lean_uint64_shift_right(v_fold_386_, v___x_387_);
v___x_389_ = lean_uint64_xor(v_fold_386_, v___x_388_);
v___x_390_ = lean_uint64_to_usize(v___x_389_);
v___x_391_ = lean_usize_of_nat(v___x_382_);
v___x_392_ = ((size_t)1ULL);
v___x_393_ = lean_usize_sub(v___x_391_, v___x_392_);
v___x_394_ = lean_usize_land(v___x_390_, v___x_393_);
v___x_395_ = lean_array_uget_borrowed(v_x_374_, v___x_394_);
lean_inc(v___x_395_);
if (v_isShared_381_ == 0)
{
lean_ctor_set(v___x_380_, 2, v___x_395_);
v___x_397_ = v___x_380_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v_key_376_);
lean_ctor_set(v_reuseFailAlloc_400_, 1, v_value_377_);
lean_ctor_set(v_reuseFailAlloc_400_, 2, v___x_395_);
v___x_397_ = v_reuseFailAlloc_400_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
lean_object* v___x_398_; 
v___x_398_ = lean_array_uset(v_x_374_, v___x_394_, v___x_397_);
v_x_374_ = v___x_398_;
v_x_375_ = v_tail_378_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2___redArg(lean_object* v_i_402_, lean_object* v_source_403_, lean_object* v_target_404_){
_start:
{
lean_object* v___x_405_; uint8_t v___x_406_; 
v___x_405_ = lean_array_get_size(v_source_403_);
v___x_406_ = lean_nat_dec_lt(v_i_402_, v___x_405_);
if (v___x_406_ == 0)
{
lean_dec_ref(v_source_403_);
lean_dec(v_i_402_);
return v_target_404_;
}
else
{
lean_object* v_es_407_; lean_object* v___x_408_; lean_object* v_source_409_; lean_object* v_target_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v_es_407_ = lean_array_fget(v_source_403_, v_i_402_);
v___x_408_ = lean_box(0);
v_source_409_ = lean_array_fset(v_source_403_, v_i_402_, v___x_408_);
v_target_410_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2_spec__3___redArg(v_target_404_, v_es_407_);
v___x_411_ = lean_unsigned_to_nat(1u);
v___x_412_ = lean_nat_add(v_i_402_, v___x_411_);
lean_dec(v_i_402_);
v_i_402_ = v___x_412_;
v_source_403_ = v_source_409_;
v_target_404_ = v_target_410_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1___redArg(lean_object* v_data_414_){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v_nbuckets_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_415_ = lean_array_get_size(v_data_414_);
v___x_416_ = lean_unsigned_to_nat(2u);
v_nbuckets_417_ = lean_nat_mul(v___x_415_, v___x_416_);
v___x_418_ = lean_unsigned_to_nat(0u);
v___x_419_ = lean_box(0);
v___x_420_ = lean_mk_array(v_nbuckets_417_, v___x_419_);
v___x_421_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2___redArg(v___x_418_, v_data_414_, v___x_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__2___lam__0(lean_object* v_i_422_, lean_object* v_x_423_){
_start:
{
if (lean_obj_tag(v_x_423_) == 0)
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_424_ = lean_unsigned_to_nat(1u);
v___x_425_ = lean_mk_empty_array_with_capacity(v___x_424_);
v___x_426_ = lean_array_push(v___x_425_, v_i_422_);
v___x_427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_427_, 0, v___x_426_);
return v___x_427_;
}
else
{
lean_object* v_val_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_436_; 
v_val_428_ = lean_ctor_get(v_x_423_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v_x_423_);
if (v_isSharedCheck_436_ == 0)
{
v___x_430_ = v_x_423_;
v_isShared_431_ = v_isSharedCheck_436_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_val_428_);
lean_dec(v_x_423_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_436_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_432_; lean_object* v___x_434_; 
v___x_432_ = lean_array_push(v_val_428_, v_i_422_);
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 0, v___x_432_);
v___x_434_ = v___x_430_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v___x_432_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__2(lean_object* v_i_437_, lean_object* v_a_438_, lean_object* v_x_439_){
_start:
{
if (lean_obj_tag(v_x_439_) == 0)
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v_val_442_; lean_object* v___x_443_; 
v___x_440_ = lean_box(0);
v___x_441_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__2___lam__0(v_i_437_, v___x_440_);
v_val_442_ = lean_ctor_get(v___x_441_, 0);
lean_inc(v_val_442_);
lean_dec(v___x_441_);
v___x_443_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_443_, 0, v_a_438_);
lean_ctor_set(v___x_443_, 1, v_val_442_);
lean_ctor_set(v___x_443_, 2, v_x_439_);
return v___x_443_;
}
else
{
lean_object* v_key_444_; lean_object* v_value_445_; lean_object* v_tail_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_461_; 
v_key_444_ = lean_ctor_get(v_x_439_, 0);
v_value_445_ = lean_ctor_get(v_x_439_, 1);
v_tail_446_ = lean_ctor_get(v_x_439_, 2);
v_isSharedCheck_461_ = !lean_is_exclusive(v_x_439_);
if (v_isSharedCheck_461_ == 0)
{
v___x_448_ = v_x_439_;
v_isShared_449_ = v_isSharedCheck_461_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_tail_446_);
lean_inc(v_value_445_);
lean_inc(v_key_444_);
lean_dec(v_x_439_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_461_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
uint8_t v___x_450_; 
v___x_450_ = lean_string_dec_eq(v_key_444_, v_a_438_);
if (v___x_450_ == 0)
{
lean_object* v_tail_451_; lean_object* v___x_453_; 
v_tail_451_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__2(v_i_437_, v_a_438_, v_tail_446_);
if (v_isShared_449_ == 0)
{
lean_ctor_set(v___x_448_, 2, v_tail_451_);
v___x_453_ = v___x_448_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_key_444_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v_value_445_);
lean_ctor_set(v_reuseFailAlloc_454_, 2, v_tail_451_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
else
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v_val_457_; lean_object* v___x_459_; 
lean_dec(v_key_444_);
v___x_455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_455_, 0, v_value_445_);
v___x_456_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__2___lam__0(v_i_437_, v___x_455_);
v_val_457_ = lean_ctor_get(v___x_456_, 0);
lean_inc(v_val_457_);
lean_dec(v___x_456_);
if (v_isShared_449_ == 0)
{
lean_ctor_set(v___x_448_, 1, v_val_457_);
lean_ctor_set(v___x_448_, 0, v_a_438_);
v___x_459_ = v___x_448_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_a_438_);
lean_ctor_set(v_reuseFailAlloc_460_, 1, v_val_457_);
lean_ctor_set(v_reuseFailAlloc_460_, 2, v_tail_446_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0(lean_object* v_i_462_, lean_object* v_m_463_, lean_object* v_a_464_){
_start:
{
lean_object* v_size_465_; lean_object* v_buckets_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_516_; 
v_size_465_ = lean_ctor_get(v_m_463_, 0);
v_buckets_466_ = lean_ctor_get(v_m_463_, 1);
v_isSharedCheck_516_ = !lean_is_exclusive(v_m_463_);
if (v_isSharedCheck_516_ == 0)
{
v___x_468_ = v_m_463_;
v_isShared_469_ = v_isSharedCheck_516_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_buckets_466_);
lean_inc(v_size_465_);
lean_dec(v_m_463_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_516_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_470_; uint64_t v___x_471_; uint64_t v___x_472_; uint64_t v___x_473_; uint64_t v_fold_474_; uint64_t v___x_475_; uint64_t v___x_476_; uint64_t v___x_477_; size_t v___x_478_; size_t v___x_479_; size_t v___x_480_; size_t v___x_481_; size_t v___x_482_; lean_object* v_bkt_483_; uint8_t v___x_484_; 
v___x_470_ = lean_array_get_size(v_buckets_466_);
v___x_471_ = lean_string_hash(v_a_464_);
v___x_472_ = 32ULL;
v___x_473_ = lean_uint64_shift_right(v___x_471_, v___x_472_);
v_fold_474_ = lean_uint64_xor(v___x_471_, v___x_473_);
v___x_475_ = 16ULL;
v___x_476_ = lean_uint64_shift_right(v_fold_474_, v___x_475_);
v___x_477_ = lean_uint64_xor(v_fold_474_, v___x_476_);
v___x_478_ = lean_uint64_to_usize(v___x_477_);
v___x_479_ = lean_usize_of_nat(v___x_470_);
v___x_480_ = ((size_t)1ULL);
v___x_481_ = lean_usize_sub(v___x_479_, v___x_480_);
v___x_482_ = lean_usize_land(v___x_478_, v___x_481_);
v_bkt_483_ = lean_array_uget_borrowed(v_buckets_466_, v___x_482_);
v___x_484_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0___redArg(v_a_464_, v_bkt_483_);
if (v___x_484_ == 0)
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v_size_x27_488_; lean_object* v___x_489_; lean_object* v_buckets_x27_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; uint8_t v___x_496_; 
v___x_485_ = lean_unsigned_to_nat(1u);
v___x_486_ = lean_mk_empty_array_with_capacity(v___x_485_);
v___x_487_ = lean_array_push(v___x_486_, v_i_462_);
v_size_x27_488_ = lean_nat_add(v_size_465_, v___x_485_);
lean_dec(v_size_465_);
lean_inc(v_bkt_483_);
v___x_489_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_489_, 0, v_a_464_);
lean_ctor_set(v___x_489_, 1, v___x_487_);
lean_ctor_set(v___x_489_, 2, v_bkt_483_);
v_buckets_x27_490_ = lean_array_uset(v_buckets_466_, v___x_482_, v___x_489_);
v___x_491_ = lean_unsigned_to_nat(4u);
v___x_492_ = lean_nat_mul(v_size_x27_488_, v___x_491_);
v___x_493_ = lean_unsigned_to_nat(3u);
v___x_494_ = lean_nat_div(v___x_492_, v___x_493_);
lean_dec(v___x_492_);
v___x_495_ = lean_array_get_size(v_buckets_x27_490_);
v___x_496_ = lean_nat_dec_le(v___x_494_, v___x_495_);
lean_dec(v___x_494_);
if (v___x_496_ == 0)
{
lean_object* v_val_497_; lean_object* v___x_499_; 
v_val_497_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1___redArg(v_buckets_x27_490_);
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 1, v_val_497_);
lean_ctor_set(v___x_468_, 0, v_size_x27_488_);
v___x_499_ = v___x_468_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_size_x27_488_);
lean_ctor_set(v_reuseFailAlloc_500_, 1, v_val_497_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
else
{
lean_object* v___x_502_; 
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 1, v_buckets_x27_490_);
lean_ctor_set(v___x_468_, 0, v_size_x27_488_);
v___x_502_ = v___x_468_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_size_x27_488_);
lean_ctor_set(v_reuseFailAlloc_503_, 1, v_buckets_x27_490_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
else
{
lean_object* v___x_504_; lean_object* v_buckets_x27_505_; lean_object* v_bkt_x27_506_; lean_object* v___y_508_; uint8_t v___x_513_; 
lean_inc(v_bkt_483_);
v___x_504_ = lean_box(0);
v_buckets_x27_505_ = lean_array_uset(v_buckets_466_, v___x_482_, v___x_504_);
lean_inc_ref(v_a_464_);
v_bkt_x27_506_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__2(v_i_462_, v_a_464_, v_bkt_483_);
v___x_513_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0___redArg(v_a_464_, v_bkt_x27_506_);
lean_dec_ref(v_a_464_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_514_ = lean_unsigned_to_nat(1u);
v___x_515_ = lean_nat_sub(v_size_465_, v___x_514_);
lean_dec(v_size_465_);
v___y_508_ = v___x_515_;
goto v___jp_507_;
}
else
{
v___y_508_ = v_size_465_;
goto v___jp_507_;
}
v___jp_507_:
{
lean_object* v___x_509_; lean_object* v___x_511_; 
v___x_509_ = lean_array_uset(v_buckets_x27_505_, v___x_482_, v_bkt_x27_506_);
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 1, v___x_509_);
lean_ctor_set(v___x_468_, 0, v___y_508_);
v___x_511_ = v___x_468_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v___y_508_);
lean_ctor_set(v_reuseFailAlloc_512_, 1, v___x_509_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_header(lean_object* v_builder_517_, lean_object* v_key_518_, lean_object* v_value_519_){
_start:
{
lean_object* v_line_520_; lean_object* v_headers_521_; lean_object* v_extensions_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_552_; 
v_line_520_ = lean_ctor_get(v_builder_517_, 0);
lean_inc_ref(v_line_520_);
v_headers_521_ = lean_ctor_get(v_line_520_, 1);
lean_inc_ref(v_headers_521_);
v_extensions_522_ = lean_ctor_get(v_builder_517_, 1);
v_isSharedCheck_552_ = !lean_is_exclusive(v_builder_517_);
if (v_isSharedCheck_552_ == 0)
{
lean_object* v_unused_553_; 
v_unused_553_ = lean_ctor_get(v_builder_517_, 0);
lean_dec(v_unused_553_);
v___x_524_ = v_builder_517_;
v_isShared_525_ = v_isSharedCheck_552_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_extensions_522_);
lean_dec(v_builder_517_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_552_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v_status_526_; uint8_t v_version_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_550_; 
v_status_526_ = lean_ctor_get(v_line_520_, 0);
v_version_527_ = lean_ctor_get_uint8(v_line_520_, sizeof(void*)*2);
v_isSharedCheck_550_ = !lean_is_exclusive(v_line_520_);
if (v_isSharedCheck_550_ == 0)
{
lean_object* v_unused_551_; 
v_unused_551_ = lean_ctor_get(v_line_520_, 1);
lean_dec(v_unused_551_);
v___x_529_ = v_line_520_;
v_isShared_530_ = v_isSharedCheck_550_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_status_526_);
lean_dec(v_line_520_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_550_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v_entries_531_; lean_object* v_indexes_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_549_; 
v_entries_531_ = lean_ctor_get(v_headers_521_, 0);
v_indexes_532_ = lean_ctor_get(v_headers_521_, 1);
v_isSharedCheck_549_ = !lean_is_exclusive(v_headers_521_);
if (v_isSharedCheck_549_ == 0)
{
v___x_534_ = v_headers_521_;
v_isShared_535_ = v_isSharedCheck_549_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_indexes_532_);
lean_inc(v_entries_531_);
lean_dec(v_headers_521_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_549_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v_i_536_; lean_object* v___x_537_; lean_object* v_entries_538_; lean_object* v_indexes_539_; lean_object* v___x_541_; 
v_i_536_ = lean_array_get_size(v_entries_531_);
lean_inc_ref(v_key_518_);
v___x_537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_537_, 0, v_key_518_);
lean_ctor_set(v___x_537_, 1, v_value_519_);
v_entries_538_ = lean_array_push(v_entries_531_, v___x_537_);
v_indexes_539_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0(v_i_536_, v_indexes_532_, v_key_518_);
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 1, v_indexes_539_);
lean_ctor_set(v___x_534_, 0, v_entries_538_);
v___x_541_ = v___x_534_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_entries_538_);
lean_ctor_set(v_reuseFailAlloc_548_, 1, v_indexes_539_);
v___x_541_ = v_reuseFailAlloc_548_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
lean_object* v___x_543_; 
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 1, v___x_541_);
v___x_543_ = v___x_529_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_status_526_);
lean_ctor_set(v_reuseFailAlloc_547_, 1, v___x_541_);
lean_ctor_set_uint8(v_reuseFailAlloc_547_, sizeof(void*)*2, v_version_527_);
v___x_543_ = v_reuseFailAlloc_547_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
lean_object* v___x_545_; 
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 0, v___x_543_);
v___x_545_ = v___x_524_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v___x_543_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v_extensions_522_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0(lean_object* v_00_u03b2_554_, lean_object* v_a_555_, lean_object* v_x_556_){
_start:
{
uint8_t v___x_557_; 
v___x_557_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0___redArg(v_a_555_, v_x_556_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0___boxed(lean_object* v_00_u03b2_558_, lean_object* v_a_559_, lean_object* v_x_560_){
_start:
{
uint8_t v_res_561_; lean_object* v_r_562_; 
v_res_561_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__0(v_00_u03b2_558_, v_a_559_, v_x_560_);
lean_dec(v_x_560_);
lean_dec_ref(v_a_559_);
v_r_562_ = lean_box(v_res_561_);
return v_r_562_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1(lean_object* v_00_u03b2_563_, lean_object* v_data_564_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1___redArg(v_data_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_566_, lean_object* v_i_567_, lean_object* v_source_568_, lean_object* v_target_569_){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2___redArg(v_i_567_, v_source_568_, v_target_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_571_, lean_object* v_x_572_, lean_object* v_x_573_){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0_spec__1_spec__2_spec__3___redArg(v_x_572_, v_x_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_header_x21(lean_object* v_builder_575_, lean_object* v_key_576_, lean_object* v_value_577_){
_start:
{
lean_object* v_line_578_; lean_object* v_headers_579_; lean_object* v_extensions_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_612_; 
v_line_578_ = lean_ctor_get(v_builder_575_, 0);
lean_inc_ref(v_line_578_);
v_headers_579_ = lean_ctor_get(v_line_578_, 1);
lean_inc_ref(v_headers_579_);
v_extensions_580_ = lean_ctor_get(v_builder_575_, 1);
v_isSharedCheck_612_ = !lean_is_exclusive(v_builder_575_);
if (v_isSharedCheck_612_ == 0)
{
lean_object* v_unused_613_; 
v_unused_613_ = lean_ctor_get(v_builder_575_, 0);
lean_dec(v_unused_613_);
v___x_582_ = v_builder_575_;
v_isShared_583_ = v_isSharedCheck_612_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_extensions_580_);
lean_dec(v_builder_575_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_612_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v_status_584_; uint8_t v_version_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_610_; 
v_status_584_ = lean_ctor_get(v_line_578_, 0);
v_version_585_ = lean_ctor_get_uint8(v_line_578_, sizeof(void*)*2);
v_isSharedCheck_610_ = !lean_is_exclusive(v_line_578_);
if (v_isSharedCheck_610_ == 0)
{
lean_object* v_unused_611_; 
v_unused_611_ = lean_ctor_get(v_line_578_, 1);
lean_dec(v_unused_611_);
v___x_587_ = v_line_578_;
v_isShared_588_ = v_isSharedCheck_610_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_status_584_);
lean_dec(v_line_578_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_610_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v_entries_589_; lean_object* v_indexes_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_609_; 
v_entries_589_ = lean_ctor_get(v_headers_579_, 0);
v_indexes_590_ = lean_ctor_get(v_headers_579_, 1);
v_isSharedCheck_609_ = !lean_is_exclusive(v_headers_579_);
if (v_isSharedCheck_609_ == 0)
{
v___x_592_ = v_headers_579_;
v_isShared_593_ = v_isSharedCheck_609_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_indexes_590_);
lean_inc(v_entries_589_);
lean_dec(v_headers_579_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_609_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v_key_594_; lean_object* v_value_595_; lean_object* v_i_596_; lean_object* v___x_597_; lean_object* v_entries_598_; lean_object* v_indexes_599_; lean_object* v___x_601_; 
v_key_594_ = l_Std_Http_Header_Name_ofString_x21(v_key_576_);
v_value_595_ = l_Std_Http_Header_Value_ofString_x21(v_value_577_);
v_i_596_ = lean_array_get_size(v_entries_589_);
lean_inc_ref(v_key_594_);
v___x_597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_597_, 0, v_key_594_);
lean_ctor_set(v___x_597_, 1, v_value_595_);
v_entries_598_ = lean_array_push(v_entries_589_, v___x_597_);
v_indexes_599_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0(v_i_596_, v_indexes_590_, v_key_594_);
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 1, v_indexes_599_);
lean_ctor_set(v___x_592_, 0, v_entries_598_);
v___x_601_ = v___x_592_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_entries_598_);
lean_ctor_set(v_reuseFailAlloc_608_, 1, v_indexes_599_);
v___x_601_ = v_reuseFailAlloc_608_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
lean_object* v___x_603_; 
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 1, v___x_601_);
v___x_603_ = v___x_587_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_status_584_);
lean_ctor_set(v_reuseFailAlloc_607_, 1, v___x_601_);
lean_ctor_set_uint8(v_reuseFailAlloc_607_, sizeof(void*)*2, v_version_585_);
v___x_603_ = v_reuseFailAlloc_607_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
lean_object* v___x_605_; 
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 0, v___x_603_);
v___x_605_ = v___x_582_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v___x_603_);
lean_ctor_set(v_reuseFailAlloc_606_, 1, v_extensions_580_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_header_x3f(lean_object* v_builder_614_, lean_object* v_key_615_, lean_object* v_value_616_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = l_Std_Http_Header_Name_ofString_x3f(v_key_615_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v___x_618_; 
lean_dec_ref(v_value_616_);
lean_dec_ref(v_builder_614_);
v___x_618_ = lean_box(0);
return v___x_618_;
}
else
{
lean_object* v_val_619_; lean_object* v___x_620_; 
v_val_619_ = lean_ctor_get(v___x_617_, 0);
lean_inc(v_val_619_);
lean_dec_ref(v___x_617_);
v___x_620_ = l_Std_Http_Header_Value_ofString_x3f(v_value_616_);
if (lean_obj_tag(v___x_620_) == 0)
{
lean_object* v___x_621_; 
lean_dec(v_val_619_);
lean_dec_ref(v_builder_614_);
v___x_621_ = lean_box(0);
return v___x_621_;
}
else
{
lean_object* v_line_622_; lean_object* v_headers_623_; lean_object* v_val_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_663_; 
v_line_622_ = lean_ctor_get(v_builder_614_, 0);
lean_inc_ref(v_line_622_);
v_headers_623_ = lean_ctor_get(v_line_622_, 1);
lean_inc_ref(v_headers_623_);
v_val_624_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_663_ == 0)
{
v___x_626_ = v___x_620_;
v_isShared_627_ = v_isSharedCheck_663_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_val_624_);
lean_dec(v___x_620_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_663_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v_extensions_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_661_; 
v_extensions_628_ = lean_ctor_get(v_builder_614_, 1);
v_isSharedCheck_661_ = !lean_is_exclusive(v_builder_614_);
if (v_isSharedCheck_661_ == 0)
{
lean_object* v_unused_662_; 
v_unused_662_ = lean_ctor_get(v_builder_614_, 0);
lean_dec(v_unused_662_);
v___x_630_ = v_builder_614_;
v_isShared_631_ = v_isSharedCheck_661_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_extensions_628_);
lean_dec(v_builder_614_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_661_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v_status_632_; uint8_t v_version_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_659_; 
v_status_632_ = lean_ctor_get(v_line_622_, 0);
v_version_633_ = lean_ctor_get_uint8(v_line_622_, sizeof(void*)*2);
v_isSharedCheck_659_ = !lean_is_exclusive(v_line_622_);
if (v_isSharedCheck_659_ == 0)
{
lean_object* v_unused_660_; 
v_unused_660_ = lean_ctor_get(v_line_622_, 1);
lean_dec(v_unused_660_);
v___x_635_ = v_line_622_;
v_isShared_636_ = v_isSharedCheck_659_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_status_632_);
lean_dec(v_line_622_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_659_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v_entries_637_; lean_object* v_indexes_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_658_; 
v_entries_637_ = lean_ctor_get(v_headers_623_, 0);
v_indexes_638_ = lean_ctor_get(v_headers_623_, 1);
v_isSharedCheck_658_ = !lean_is_exclusive(v_headers_623_);
if (v_isSharedCheck_658_ == 0)
{
v___x_640_ = v_headers_623_;
v_isShared_641_ = v_isSharedCheck_658_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_indexes_638_);
lean_inc(v_entries_637_);
lean_dec(v_headers_623_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_658_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v_i_642_; lean_object* v___x_643_; lean_object* v_entries_644_; lean_object* v_indexes_645_; lean_object* v___x_647_; 
v_i_642_ = lean_array_get_size(v_entries_637_);
lean_inc(v_val_619_);
v___x_643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_643_, 0, v_val_619_);
lean_ctor_set(v___x_643_, 1, v_val_624_);
v_entries_644_ = lean_array_push(v_entries_637_, v___x_643_);
v_indexes_645_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Response_Builder_header_spec__0(v_i_642_, v_indexes_638_, v_val_619_);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 1, v_indexes_645_);
lean_ctor_set(v___x_640_, 0, v_entries_644_);
v___x_647_ = v___x_640_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_entries_644_);
lean_ctor_set(v_reuseFailAlloc_657_, 1, v_indexes_645_);
v___x_647_ = v_reuseFailAlloc_657_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
lean_object* v___x_649_; 
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 1, v___x_647_);
v___x_649_ = v___x_635_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_status_632_);
lean_ctor_set(v_reuseFailAlloc_656_, 1, v___x_647_);
lean_ctor_set_uint8(v_reuseFailAlloc_656_, sizeof(void*)*2, v_version_633_);
v___x_649_ = v_reuseFailAlloc_656_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
lean_object* v___x_651_; 
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 0, v___x_649_);
v___x_651_ = v___x_630_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v___x_649_);
lean_ctor_set(v_reuseFailAlloc_655_, 1, v_extensions_628_);
v___x_651_ = v_reuseFailAlloc_655_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
lean_object* v___x_653_; 
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 0, v___x_651_);
v___x_653_ = v___x_626_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v___x_651_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
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
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_extension___redArg(lean_object* v_builder_665_, lean_object* v_inst_666_, lean_object* v_data_667_){
_start:
{
lean_object* v_line_668_; lean_object* v_extensions_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_680_; 
v_line_668_ = lean_ctor_get(v_builder_665_, 0);
v_extensions_669_ = lean_ctor_get(v_builder_665_, 1);
v_isSharedCheck_680_ = !lean_is_exclusive(v_builder_665_);
if (v_isSharedCheck_680_ == 0)
{
v___x_671_ = v_builder_665_;
v_isShared_672_ = v_isSharedCheck_680_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_extensions_669_);
lean_inc(v_line_668_);
lean_dec(v_builder_665_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_680_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v_dyn_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_678_; 
v_dyn_673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_dyn_673_, 0, v_inst_666_);
lean_ctor_set(v_dyn_673_, 1, v_data_667_);
v___x_674_ = ((lean_object*)(l_Std_Http_Response_Builder_extension___redArg___closed__0));
v___x_675_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_dyn_673_);
v___x_676_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_674_, v___x_675_, v_dyn_673_, v_extensions_669_);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 1, v___x_676_);
v___x_678_ = v___x_671_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_line_668_);
lean_ctor_set(v_reuseFailAlloc_679_, 1, v___x_676_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_extension(lean_object* v_00_u03b1_681_, lean_object* v_builder_682_, lean_object* v_inst_683_, lean_object* v_data_684_){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = l_Std_Http_Response_Builder_extension___redArg(v_builder_682_, v_inst_683_, v_data_684_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_body___redArg(lean_object* v_builder_686_, lean_object* v_body_687_){
_start:
{
lean_object* v_line_688_; lean_object* v_extensions_689_; lean_object* v___x_690_; 
v_line_688_ = lean_ctor_get(v_builder_686_, 0);
v_extensions_689_ = lean_ctor_get(v_builder_686_, 1);
lean_inc(v_extensions_689_);
lean_inc_ref(v_line_688_);
v___x_690_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_690_, 0, v_line_688_);
lean_ctor_set(v___x_690_, 1, v_body_687_);
lean_ctor_set(v___x_690_, 2, v_extensions_689_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_body___redArg___boxed(lean_object* v_builder_691_, lean_object* v_body_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Std_Http_Response_Builder_body___redArg(v_builder_691_, v_body_692_);
lean_dec_ref(v_builder_691_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_body(lean_object* v_t_694_, lean_object* v_builder_695_, lean_object* v_body_696_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = l_Std_Http_Response_Builder_body___redArg(v_builder_695_, v_body_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_body___boxed(lean_object* v_t_698_, lean_object* v_builder_699_, lean_object* v_body_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_Std_Http_Response_Builder_body(v_t_698_, v_builder_699_, v_body_700_);
lean_dec_ref(v_builder_699_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_build___redArg(lean_object* v_inst_702_, lean_object* v_builder_703_){
_start:
{
lean_object* v_line_704_; lean_object* v_extensions_705_; lean_object* v___x_706_; 
v_line_704_ = lean_ctor_get(v_builder_703_, 0);
v_extensions_705_ = lean_ctor_get(v_builder_703_, 1);
lean_inc(v_extensions_705_);
lean_inc_ref(v_line_704_);
v___x_706_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_706_, 0, v_line_704_);
lean_ctor_set(v___x_706_, 1, v_inst_702_);
lean_ctor_set(v___x_706_, 2, v_extensions_705_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_build___redArg___boxed(lean_object* v_inst_707_, lean_object* v_builder_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_Std_Http_Response_Builder_build___redArg(v_inst_707_, v_builder_708_);
lean_dec_ref(v_builder_708_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_build(lean_object* v_t_710_, lean_object* v_inst_711_, lean_object* v_builder_712_){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = l_Std_Http_Response_Builder_build___redArg(v_inst_711_, v_builder_712_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_build___boxed(lean_object* v_t_714_, lean_object* v_inst_715_, lean_object* v_builder_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Std_Http_Response_Builder_build(v_t_714_, v_inst_715_, v_builder_716_);
lean_dec_ref(v_builder_716_);
return v_res_717_;
}
}
static lean_object* _init_l_Std_Http_Response_ok___closed__0(void){
_start:
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_718_ = lean_box(4);
v___x_719_ = l_Std_Http_Response_Builder_new;
v___x_720_ = l_Std_Http_Response_Builder_status(v___x_719_, v___x_718_);
return v___x_720_;
}
}
static lean_object* _init_l_Std_Http_Response_ok(void){
_start:
{
lean_object* v___x_721_; 
v___x_721_ = lean_obj_once(&l_Std_Http_Response_ok___closed__0, &l_Std_Http_Response_ok___closed__0_once, _init_l_Std_Http_Response_ok___closed__0);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_withStatus(lean_object* v_status_722_){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_723_ = l_Std_Http_Response_Builder_new;
v___x_724_ = l_Std_Http_Response_Builder_status(v___x_723_, v_status_722_);
return v___x_724_;
}
}
static lean_object* _init_l_Std_Http_Response_notFound___closed__0(void){
_start:
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_725_ = lean_box(27);
v___x_726_ = l_Std_Http_Response_Builder_new;
v___x_727_ = l_Std_Http_Response_Builder_status(v___x_726_, v___x_725_);
return v___x_727_;
}
}
static lean_object* _init_l_Std_Http_Response_notFound(void){
_start:
{
lean_object* v___x_728_; 
v___x_728_ = lean_obj_once(&l_Std_Http_Response_notFound___closed__0, &l_Std_Http_Response_notFound___closed__0_once, _init_l_Std_Http_Response_notFound___closed__0);
return v___x_728_;
}
}
static lean_object* _init_l_Std_Http_Response_internalServerError___closed__0(void){
_start:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_729_ = lean_box(52);
v___x_730_ = l_Std_Http_Response_Builder_new;
v___x_731_ = l_Std_Http_Response_Builder_status(v___x_730_, v___x_729_);
return v___x_731_;
}
}
static lean_object* _init_l_Std_Http_Response_internalServerError(void){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = lean_obj_once(&l_Std_Http_Response_internalServerError___closed__0, &l_Std_Http_Response_internalServerError___closed__0_once, _init_l_Std_Http_Response_internalServerError___closed__0);
return v___x_732_;
}
}
static lean_object* _init_l_Std_Http_Response_badRequest___closed__0(void){
_start:
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_733_ = lean_box(23);
v___x_734_ = l_Std_Http_Response_Builder_new;
v___x_735_ = l_Std_Http_Response_Builder_status(v___x_734_, v___x_733_);
return v___x_735_;
}
}
static lean_object* _init_l_Std_Http_Response_badRequest(void){
_start:
{
lean_object* v___x_736_; 
v___x_736_ = lean_obj_once(&l_Std_Http_Response_badRequest___closed__0, &l_Std_Http_Response_badRequest___closed__0_once, _init_l_Std_Http_Response_badRequest___closed__0);
return v___x_736_;
}
}
static lean_object* _init_l_Std_Http_Response_created___closed__0(void){
_start:
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_737_ = lean_box(5);
v___x_738_ = l_Std_Http_Response_Builder_new;
v___x_739_ = l_Std_Http_Response_Builder_status(v___x_738_, v___x_737_);
return v___x_739_;
}
}
static lean_object* _init_l_Std_Http_Response_created(void){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = lean_obj_once(&l_Std_Http_Response_created___closed__0, &l_Std_Http_Response_created___closed__0_once, _init_l_Std_Http_Response_created___closed__0);
return v___x_740_;
}
}
static lean_object* _init_l_Std_Http_Response_accepted___closed__0(void){
_start:
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_741_ = lean_box(6);
v___x_742_ = l_Std_Http_Response_Builder_new;
v___x_743_ = l_Std_Http_Response_Builder_status(v___x_742_, v___x_741_);
return v___x_743_;
}
}
static lean_object* _init_l_Std_Http_Response_accepted(void){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = lean_obj_once(&l_Std_Http_Response_accepted___closed__0, &l_Std_Http_Response_accepted___closed__0_once, _init_l_Std_Http_Response_accepted___closed__0);
return v___x_744_;
}
}
static lean_object* _init_l_Std_Http_Response_unauthorized___closed__0(void){
_start:
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_745_ = lean_box(24);
v___x_746_ = l_Std_Http_Response_Builder_new;
v___x_747_ = l_Std_Http_Response_Builder_status(v___x_746_, v___x_745_);
return v___x_747_;
}
}
static lean_object* _init_l_Std_Http_Response_unauthorized(void){
_start:
{
lean_object* v___x_748_; 
v___x_748_ = lean_obj_once(&l_Std_Http_Response_unauthorized___closed__0, &l_Std_Http_Response_unauthorized___closed__0_once, _init_l_Std_Http_Response_unauthorized___closed__0);
return v___x_748_;
}
}
static lean_object* _init_l_Std_Http_Response_forbidden___closed__0(void){
_start:
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_749_ = lean_box(26);
v___x_750_ = l_Std_Http_Response_Builder_new;
v___x_751_ = l_Std_Http_Response_Builder_status(v___x_750_, v___x_749_);
return v___x_751_;
}
}
static lean_object* _init_l_Std_Http_Response_forbidden(void){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = lean_obj_once(&l_Std_Http_Response_forbidden___closed__0, &l_Std_Http_Response_forbidden___closed__0_once, _init_l_Std_Http_Response_forbidden___closed__0);
return v___x_752_;
}
}
static lean_object* _init_l_Std_Http_Response_conflict___closed__0(void){
_start:
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_753_ = lean_box(32);
v___x_754_ = l_Std_Http_Response_Builder_new;
v___x_755_ = l_Std_Http_Response_Builder_status(v___x_754_, v___x_753_);
return v___x_755_;
}
}
static lean_object* _init_l_Std_Http_Response_conflict(void){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = lean_obj_once(&l_Std_Http_Response_conflict___closed__0, &l_Std_Http_Response_conflict___closed__0_once, _init_l_Std_Http_Response_conflict___closed__0);
return v___x_756_;
}
}
static lean_object* _init_l_Std_Http_Response_serviceUnavailable___closed__0(void){
_start:
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_757_ = lean_box(55);
v___x_758_ = l_Std_Http_Response_Builder_new;
v___x_759_ = l_Std_Http_Response_Builder_status(v___x_758_, v___x_757_);
return v___x_759_;
}
}
static lean_object* _init_l_Std_Http_Response_serviceUnavailable(void){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = lean_obj_once(&l_Std_Http_Response_serviceUnavailable___closed__0, &l_Std_Http_Response_serviceUnavailable___closed__0_once, _init_l_Std_Http_Response_serviceUnavailable___closed__0);
return v___x_760_;
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
