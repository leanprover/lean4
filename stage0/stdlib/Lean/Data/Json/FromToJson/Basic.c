// Lean compiler output
// Module: Lean.Data.Json.FromToJson.Basic
// Imports: public import Lean.Data.Json.Printer public import Init.Data.ToString.Macro import Init.Data.Array.GetLit
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
LEAN_EXPORT lean_object* l_Lean_instFromJsonJson___lam__0(lean_object*);
static const lean_closure_object l_Lean_instFromJsonJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instFromJsonJson___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonJson___closed__0 = (const lean_object*)&l_Lean_instFromJsonJson___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instFromJsonJson = (const lean_object*)&l_Lean_instFromJsonJson___closed__0_value;
lean_object* l_id___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instToJsonJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_instToJsonJson___closed__0 = (const lean_object*)&l_Lean_instToJsonJson___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonJson = (const lean_object*)&l_Lean_instToJsonJson___closed__0_value;
lean_object* l_Lean_Json_getNum_x3f(lean_object*);
static const lean_closure_object l_Lean_instFromJsonJsonNumber___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Json_getNum_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonJsonNumber___closed__0 = (const lean_object*)&l_Lean_instFromJsonJsonNumber___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instFromJsonJsonNumber = (const lean_object*)&l_Lean_instFromJsonJsonNumber___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instToJsonJsonNumber___lam__0(lean_object*);
static const lean_closure_object l_Lean_instToJsonJsonNumber___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonJsonNumber___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonJsonNumber___closed__0 = (const lean_object*)&l_Lean_instToJsonJsonNumber___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonJsonNumber = (const lean_object*)&l_Lean_instToJsonJsonNumber___closed__0_value;
static const lean_string_object l_Lean_instFromJsonEmpty___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "type Empty has no constructor to match JSON value '"};
static const lean_object* l_Lean_instFromJsonEmpty___lam__0___closed__0 = (const lean_object*)&l_Lean_instFromJsonEmpty___lam__0___closed__0_value;
static const lean_string_object l_Lean_instFromJsonEmpty___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 122, .m_capacity = 122, .m_length = 121, .m_data = "'. This occurs when deserializing a value for type Empty, e.g. at type Option Empty with code for the 'some' constructor."};
static const lean_object* l_Lean_instFromJsonEmpty___lam__0___closed__1 = (const lean_object*)&l_Lean_instFromJsonEmpty___lam__0___closed__1_value;
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonEmpty___lam__0(lean_object*);
static const lean_closure_object l_Lean_instFromJsonEmpty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instFromJsonEmpty___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonEmpty___closed__0 = (const lean_object*)&l_Lean_instFromJsonEmpty___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instFromJsonEmpty = (const lean_object*)&l_Lean_instFromJsonEmpty___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instToJsonEmpty___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_instToJsonEmpty___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_instToJsonEmpty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonEmpty___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonEmpty___closed__0 = (const lean_object*)&l_Lean_instToJsonEmpty___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonEmpty = (const lean_object*)&l_Lean_instToJsonEmpty___closed__0_value;
lean_object* l_Lean_Json_getBool_x3f___boxed(lean_object*);
static const lean_closure_object l_Lean_instFromJsonBool___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Json_getBool_x3f___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonBool___closed__0 = (const lean_object*)&l_Lean_instFromJsonBool___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instFromJsonBool = (const lean_object*)&l_Lean_instFromJsonBool___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instToJsonBool___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_instToJsonBool___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_instToJsonBool___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonBool___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonBool___closed__0 = (const lean_object*)&l_Lean_instToJsonBool___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonBool = (const lean_object*)&l_Lean_instToJsonBool___closed__0_value;
lean_object* l_Lean_Json_getNat_x3f(lean_object*);
static const lean_closure_object l_Lean_instFromJsonNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Json_getNat_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonNat___closed__0 = (const lean_object*)&l_Lean_instFromJsonNat___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instFromJsonNat = (const lean_object*)&l_Lean_instFromJsonNat___closed__0_value;
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToJsonNat___lam__0(lean_object*);
static const lean_closure_object l_Lean_instToJsonNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonNat___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonNat___closed__0 = (const lean_object*)&l_Lean_instToJsonNat___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonNat = (const lean_object*)&l_Lean_instToJsonNat___closed__0_value;
lean_object* l_Lean_Json_getInt_x3f(lean_object*);
static const lean_closure_object l_Lean_instFromJsonInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Json_getInt_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonInt___closed__0 = (const lean_object*)&l_Lean_instFromJsonInt___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instFromJsonInt = (const lean_object*)&l_Lean_instFromJsonInt___closed__0_value;
lean_object* l_Lean_JsonNumber_fromInt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToJsonInt___lam__0(lean_object*);
static const lean_closure_object l_Lean_instToJsonInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonInt___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonInt___closed__0 = (const lean_object*)&l_Lean_instToJsonInt___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonInt = (const lean_object*)&l_Lean_instToJsonInt___closed__0_value;
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
static const lean_closure_object l_Lean_instFromJsonString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Json_getStr_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonString___closed__0 = (const lean_object*)&l_Lean_instFromJsonString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instFromJsonString = (const lean_object*)&l_Lean_instFromJsonString___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instToJsonString___lam__0(lean_object*);
static const lean_closure_object l_Lean_instToJsonString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonString___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonString___closed__0 = (const lean_object*)&l_Lean_instToJsonString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonString = (const lean_object*)&l_Lean_instToJsonString___closed__0_value;
lean_object* l_String_toSlice(lean_object*);
static const lean_closure_object l_Lean_instFromJsonSlice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_toSlice, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonSlice___closed__0 = (const lean_object*)&l_Lean_instFromJsonSlice___closed__0_value;
lean_object* l_Except_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_instFromJsonSlice___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_map, .m_arity = 5, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instFromJsonSlice___closed__0_value)} };
static const lean_object* l_Lean_instFromJsonSlice___closed__1 = (const lean_object*)&l_Lean_instFromJsonSlice___closed__1_value;
lean_object* l_Function_comp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_instFromJsonSlice___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Function_comp, .m_arity = 6, .m_num_fixed = 5, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instFromJsonSlice___closed__1_value),((lean_object*)&l_Lean_instFromJsonString___closed__0_value)} };
static const lean_object* l_Lean_instFromJsonSlice___closed__2 = (const lean_object*)&l_Lean_instFromJsonSlice___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_instFromJsonSlice = (const lean_object*)&l_Lean_instFromJsonSlice___closed__2_value;
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToJsonSlice___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToJsonSlice___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_instToJsonSlice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonSlice___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonSlice___closed__0 = (const lean_object*)&l_Lean_instToJsonSlice___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonSlice = (const lean_object*)&l_Lean_instToJsonSlice___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instFromJsonFilePath___lam__0(lean_object*);
static const lean_closure_object l_Lean_instFromJsonFilePath___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instFromJsonFilePath___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonFilePath___closed__0 = (const lean_object*)&l_Lean_instFromJsonFilePath___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instFromJsonFilePath = (const lean_object*)&l_Lean_instFromJsonFilePath___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instToJsonFilePath___lam__0(lean_object*);
static const lean_closure_object l_Lean_instToJsonFilePath___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonFilePath___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonFilePath___closed__0 = (const lean_object*)&l_Lean_instToJsonFilePath___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonFilePath = (const lean_object*)&l_Lean_instToJsonFilePath___closed__0_value;
lean_object* l_Except_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Array_fromJson_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_fromJson_x3f___redArg___closed__0 = (const lean_object*)&l_Array_fromJson_x3f___redArg___closed__0_value;
lean_object* l_Except_instMonad___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Array_fromJson_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_instMonad___lam__1, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_fromJson_x3f___redArg___closed__1 = (const lean_object*)&l_Array_fromJson_x3f___redArg___closed__1_value;
lean_object* l_Except_instMonad___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Array_fromJson_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_instMonad___lam__2___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_fromJson_x3f___redArg___closed__2 = (const lean_object*)&l_Array_fromJson_x3f___redArg___closed__2_value;
lean_object* l_Except_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Array_fromJson_x3f___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_fromJson_x3f___redArg___closed__3 = (const lean_object*)&l_Array_fromJson_x3f___redArg___closed__3_value;
static const lean_closure_object l_Array_fromJson_x3f___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_map, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Array_fromJson_x3f___redArg___closed__4 = (const lean_object*)&l_Array_fromJson_x3f___redArg___closed__4_value;
static const lean_ctor_object l_Array_fromJson_x3f___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_fromJson_x3f___redArg___closed__4_value),((lean_object*)&l_Array_fromJson_x3f___redArg___closed__0_value)}};
static const lean_object* l_Array_fromJson_x3f___redArg___closed__5 = (const lean_object*)&l_Array_fromJson_x3f___redArg___closed__5_value;
lean_object* l_Except_pure(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Array_fromJson_x3f___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_pure, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Array_fromJson_x3f___redArg___closed__6 = (const lean_object*)&l_Array_fromJson_x3f___redArg___closed__6_value;
static const lean_ctor_object l_Array_fromJson_x3f___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_fromJson_x3f___redArg___closed__5_value),((lean_object*)&l_Array_fromJson_x3f___redArg___closed__6_value),((lean_object*)&l_Array_fromJson_x3f___redArg___closed__1_value),((lean_object*)&l_Array_fromJson_x3f___redArg___closed__2_value),((lean_object*)&l_Array_fromJson_x3f___redArg___closed__3_value)}};
static const lean_object* l_Array_fromJson_x3f___redArg___closed__7 = (const lean_object*)&l_Array_fromJson_x3f___redArg___closed__7_value;
lean_object* l_Except_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Array_fromJson_x3f___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_bind, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Array_fromJson_x3f___redArg___closed__8 = (const lean_object*)&l_Array_fromJson_x3f___redArg___closed__8_value;
static const lean_ctor_object l_Array_fromJson_x3f___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_fromJson_x3f___redArg___closed__7_value),((lean_object*)&l_Array_fromJson_x3f___redArg___closed__8_value)}};
static const lean_object* l_Array_fromJson_x3f___redArg___closed__9 = (const lean_object*)&l_Array_fromJson_x3f___redArg___closed__9_value;
static const lean_string_object l_Array_fromJson_x3f___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Array_fromJson_x3f___redArg___closed__10 = (const lean_object*)&l_Array_fromJson_x3f___redArg___closed__10_value;
static const lean_string_object l_Array_fromJson_x3f___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Array_fromJson_x3f___redArg___closed__11 = (const lean_object*)&l_Array_fromJson_x3f___redArg___closed__11_value;
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Array_toJson___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_toJson___redArg___closed__0 = (const lean_object*)&l_Array_toJson___redArg___closed__0_value;
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Array_toJson___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_toJson___redArg___closed__1 = (const lean_object*)&l_Array_toJson___redArg___closed__1_value;
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Array_toJson___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_toJson___redArg___closed__2 = (const lean_object*)&l_Array_toJson___redArg___closed__2_value;
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Array_toJson___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_toJson___redArg___closed__3 = (const lean_object*)&l_Array_toJson___redArg___closed__3_value;
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Array_toJson___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_toJson___redArg___closed__4 = (const lean_object*)&l_Array_toJson___redArg___closed__4_value;
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Array_toJson___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_toJson___redArg___closed__5 = (const lean_object*)&l_Array_toJson___redArg___closed__5_value;
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Array_toJson___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_toJson___redArg___closed__6 = (const lean_object*)&l_Array_toJson___redArg___closed__6_value;
static const lean_ctor_object l_Array_toJson___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_toJson___redArg___closed__0_value),((lean_object*)&l_Array_toJson___redArg___closed__1_value)}};
static const lean_object* l_Array_toJson___redArg___closed__7 = (const lean_object*)&l_Array_toJson___redArg___closed__7_value;
static const lean_ctor_object l_Array_toJson___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_toJson___redArg___closed__7_value),((lean_object*)&l_Array_toJson___redArg___closed__2_value),((lean_object*)&l_Array_toJson___redArg___closed__3_value),((lean_object*)&l_Array_toJson___redArg___closed__4_value),((lean_object*)&l_Array_toJson___redArg___closed__5_value)}};
static const lean_object* l_Array_toJson___redArg___closed__8 = (const lean_object*)&l_Array_toJson___redArg___closed__8_value;
static const lean_ctor_object l_Array_toJson___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_toJson___redArg___closed__8_value),((lean_object*)&l_Array_toJson___redArg___closed__6_value)}};
static const lean_object* l_Array_toJson___redArg___closed__9 = (const lean_object*)&l_Array_toJson___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Array_toJson___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToJsonArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToJsonArray(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_List_fromJson_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_fromJson_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonList(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_List_toJson___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_toJson(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToJsonList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToJsonList(lean_object*, lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___redArg___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_fromJson_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonOption___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonOption(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_toJson___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_toJson(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToJsonOption___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToJsonOption(lean_object*, lean_object*);
static const lean_string_object l_Prod_fromJson_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "expected pair, got '"};
static const lean_object* l_Prod_fromJson_x3f___redArg___closed__0 = (const lean_object*)&l_Prod_fromJson_x3f___redArg___closed__0_value;
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_fromJson_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_fromJson_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonProd___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonProd(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_toJson___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_toJson(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToJsonProd___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToJsonProd(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Name_fromJson_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "[anonymous]"};
static const lean_object* l_Lean_Name_fromJson_x3f___closed__0 = (const lean_object*)&l_Lean_Name_fromJson_x3f___closed__0_value;
static const lean_string_object l_Lean_Name_fromJson_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "expected a `Name`, got '"};
static const lean_object* l_Lean_Name_fromJson_x3f___closed__1 = (const lean_object*)&l_Lean_Name_fromJson_x3f___closed__1_value;
static const lean_ctor_object l_Lean_Name_fromJson_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Name_fromJson_x3f___closed__2 = (const lean_object*)&l_Lean_Name_fromJson_x3f___closed__2_value;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_String_toName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_fromJson_x3f(lean_object*);
static const lean_closure_object l_Lean_instFromJsonName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_fromJson_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonName___closed__0 = (const lean_object*)&l_Lean_instFromJsonName___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instFromJsonName = (const lean_object*)&l_Lean_instFromJsonName___closed__0_value;
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_instToJsonName___lam__0(lean_object*);
static const lean_closure_object l_Lean_instToJsonName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonName___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonName___closed__0 = (const lean_object*)&l_Lean_instToJsonName___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonName = (const lean_object*)&l_Lean_instToJsonName___closed__0_value;
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_NameMap_fromJson_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "expected a `NameMap`, got '"};
static const lean_object* l_Lean_NameMap_fromJson_x3f___redArg___closed__0 = (const lean_object*)&l_Lean_NameMap_fromJson_x3f___redArg___closed__0_value;
lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonNameMap___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonNameMap(lean_object*, lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_NameMap_toJson___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_NameMap_toJson___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_NameMap_toJson___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_NameMap_toJson___redArg___closed__0 = (const lean_object*)&l_Lean_NameMap_toJson___redArg___closed__0_value;
lean_object* l_Std_DTreeMap_Internal_Impl_foldl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToJsonNameMap___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToJsonNameMap(lean_object*, lean_object*);
static const lean_string_object l_Lean_bignumFromJson_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "expected a string-encoded number, got '"};
static const lean_object* l_Lean_bignumFromJson_x3f___closed__0 = (const lean_object*)&l_Lean_bignumFromJson_x3f___closed__0_value;
lean_object* l_Lean_Syntax_decodeNatLitVal_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_bignumFromJson_x3f(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lean_bignumToJson(lean_object*);
extern lean_object* l_System_Platform_numBits;
lean_object* lean_nat_pow(lean_object*, lean_object*);
static lean_once_cell_t l_USize_fromJson_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_USize_fromJson_x3f___closed__0;
static const lean_string_object l_USize_fromJson_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "value '"};
static const lean_object* l_USize_fromJson_x3f___closed__1 = (const lean_object*)&l_USize_fromJson_x3f___closed__1_value;
static const lean_string_object l_USize_fromJson_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "' is too large for `USize`"};
static const lean_object* l_USize_fromJson_x3f___closed__2 = (const lean_object*)&l_USize_fromJson_x3f___closed__2_value;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_USize_fromJson_x3f(lean_object*);
static const lean_closure_object l_Lean_instFromJsonUSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_USize_fromJson_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonUSize___closed__0 = (const lean_object*)&l_Lean_instFromJsonUSize___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instFromJsonUSize = (const lean_object*)&l_Lean_instFromJsonUSize___closed__0_value;
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Lean_instToJsonUSize___lam__0(size_t);
LEAN_EXPORT lean_object* l_Lean_instToJsonUSize___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_instToJsonUSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonUSize___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonUSize___closed__0 = (const lean_object*)&l_Lean_instToJsonUSize___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonUSize = (const lean_object*)&l_Lean_instToJsonUSize___closed__0_value;
static lean_once_cell_t l_UInt64_fromJson_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_UInt64_fromJson_x3f___closed__0;
static const lean_string_object l_UInt64_fromJson_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "' is too large for `UInt64`"};
static const lean_object* l_UInt64_fromJson_x3f___closed__1 = (const lean_object*)&l_UInt64_fromJson_x3f___closed__1_value;
uint64_t lean_uint64_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_UInt64_fromJson_x3f(lean_object*);
static const lean_closure_object l_Lean_instFromJsonUInt64___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_fromJson_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonUInt64___closed__0 = (const lean_object*)&l_Lean_instFromJsonUInt64___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instFromJsonUInt64 = (const lean_object*)&l_Lean_instFromJsonUInt64___closed__0_value;
lean_object* lean_uint64_to_nat(uint64_t);
LEAN_EXPORT lean_object* l_Lean_instToJsonUInt64___lam__0(uint64_t);
LEAN_EXPORT lean_object* l_Lean_instToJsonUInt64___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_instToJsonUInt64___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonUInt64___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonUInt64___closed__0 = (const lean_object*)&l_Lean_instToJsonUInt64___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonUInt64 = (const lean_object*)&l_Lean_instToJsonUInt64___closed__0_value;
lean_object* l_Lean_JsonNumber_fromFloat_x3f(double);
LEAN_EXPORT lean_object* l_Float_toJson(double);
LEAN_EXPORT lean_object* l_Float_toJson___boxed(lean_object*);
static const lean_closure_object l_Lean_instToJsonFloat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float_toJson___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonFloat___closed__0 = (const lean_object*)&l_Lean_instToJsonFloat___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonFloat = (const lean_object*)&l_Lean_instToJsonFloat___closed__0_value;
static const lean_string_object l_Float_fromJson_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "Expected a number or a string 'Infinity', '-Infinity', 'NaN'."};
static const lean_object* l_Float_fromJson_x3f___closed__0 = (const lean_object*)&l_Float_fromJson_x3f___closed__0_value;
static const lean_ctor_object l_Float_fromJson_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Float_fromJson_x3f___closed__0_value)}};
static const lean_object* l_Float_fromJson_x3f___closed__1 = (const lean_object*)&l_Float_fromJson_x3f___closed__1_value;
static const lean_string_object l_Float_fromJson_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Infinity"};
static const lean_object* l_Float_fromJson_x3f___closed__2 = (const lean_object*)&l_Float_fromJson_x3f___closed__2_value;
static const lean_string_object l_Float_fromJson_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "-Infinity"};
static const lean_object* l_Float_fromJson_x3f___closed__3 = (const lean_object*)&l_Float_fromJson_x3f___closed__3_value;
static const lean_string_object l_Float_fromJson_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "NaN"};
static const lean_object* l_Float_fromJson_x3f___closed__4 = (const lean_object*)&l_Float_fromJson_x3f___closed__4_value;
double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
double lean_float_div(double, double);
double lean_float_negate(double);
double l_Lean_JsonNumber_toFloat(lean_object*);
LEAN_EXPORT lean_object* l_Float_fromJson_x3f(lean_object*);
static const lean_closure_object l_Lean_instFromJsonFloat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float_fromJson_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonFloat___closed__0 = (const lean_object*)&l_Lean_instFromJsonFloat___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instFromJsonFloat = (const lean_object*)&l_Lean_instFromJsonFloat___closed__0_value;
static const lean_string_object l_Lean_Json_Structured_fromJson_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "expected structured object, got '"};
static const lean_object* l_Lean_Json_Structured_fromJson_x3f___closed__0 = (const lean_object*)&l_Lean_Json_Structured_fromJson_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_Structured_fromJson_x3f(lean_object*);
static const lean_closure_object l_Lean_Json_instFromJsonStructured___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Json_Structured_fromJson_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Json_instFromJsonStructured___closed__0 = (const lean_object*)&l_Lean_Json_instFromJsonStructured___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Json_instFromJsonStructured = (const lean_object*)&l_Lean_Json_instFromJsonStructured___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_Structured_toJson(lean_object*);
static const lean_closure_object l_Lean_Json_instToJsonStructured___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Json_Structured_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Json_instToJsonStructured___closed__0 = (const lean_object*)&l_Lean_Json_instToJsonStructured___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Json_instToJsonStructured = (const lean_object*)&l_Lean_Json_instToJsonStructured___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_setObjVal_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_setObjValAs_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_setObjValAs_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getTag_x3f(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Name_getString_x21(lean_object*);
lean_object* l_Lean_Json_getObjVal_x3f(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Json_parseTagged_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Json_parseTagged_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Json_parseTagged___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "incorrect number of fields: "};
static const lean_object* l_Lean_Json_parseTagged___closed__0 = (const lean_object*)&l_Lean_Json_parseTagged___closed__0_value;
static const lean_string_object l_Lean_Json_parseTagged___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = " ≟ "};
static const lean_object* l_Lean_Json_parseTagged___closed__1 = (const lean_object*)&l_Lean_Json_parseTagged___closed__1_value;
static const lean_array_object l_Lean_Json_parseTagged___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Json_parseTagged___closed__2 = (const lean_object*)&l_Lean_Json_parseTagged___closed__2_value;
static const lean_string_object l_Lean_Json_parseTagged___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "incorrect tag: "};
static const lean_object* l_Lean_Json_parseTagged___closed__3 = (const lean_object*)&l_Lean_Json_parseTagged___closed__3_value;
static const lean_ctor_object l_Lean_Json_parseTagged___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json_parseTagged___closed__2_value)}};
static const lean_object* l_Lean_Json_parseTagged___closed__4 = (const lean_object*)&l_Lean_Json_parseTagged___closed__4_value;
lean_object* l_Lean_Json_getArr_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_parseTagged(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_parseTagged___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_parseCtorFields_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_parseCtorFields_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_parseCtorFields(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_parseCtorFields___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonJson___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonJsonNumber___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonEmpty___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = ((lean_object*)(l_Lean_instFromJsonEmpty___lam__0___closed__0));
x_3 = lean_unsigned_to_nat(80u);
x_4 = l_Lean_Json_pretty(x_1, x_3);
x_5 = lean_string_append(x_2, x_4);
lean_dec_ref(x_4);
x_6 = ((lean_object*)(l_Lean_instFromJsonEmpty___lam__0___closed__1));
x_7 = lean_string_append(x_5, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonEmpty___lam__0(uint8_t x_1) {
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonEmpty___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_instToJsonEmpty___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBool___lam__0(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBool___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_instToJsonBool___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonNat___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_JsonNumber_fromNat(x_1);
x_3 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonInt___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_JsonNumber_fromInt(x_1);
x_3 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonString___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonSlice___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_string_utf8_extract(x_2, x_3, x_4);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonSlice___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_instToJsonSlice___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonFilePath___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Json_getStr_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_10; 
x_3 = lean_ctor_get(x_2, 0);
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
x_4 = x_2;
x_5 = x_10;
goto block_9;
}
else
{
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = x_10;
goto block_9;
}
block_9:
{
lean_object* x_6; 
if (x_5 == 0)
{
x_6 = x_4;
goto block_7;
}
else
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_3);
x_6 = x_8;
goto block_7;
}
block_7:
{
return x_6;
}
}
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_18; 
x_11 = lean_ctor_get(x_2, 0);
x_18 = !lean_is_exclusive(x_2);
if (x_18 == 0)
{
x_12 = x_2;
x_13 = x_18;
goto block_17;
}
else
{
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_14; 
if (x_13 == 0)
{
x_14 = x_12;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_11);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonFilePath___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = ((lean_object*)(l_Array_fromJson_x3f___redArg___closed__9));
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_2);
x_5 = lean_array_size(x_4);
x_6 = 0;
x_7 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_3, x_1, x_5, x_6, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec_ref(x_1);
x_8 = ((lean_object*)(l_Array_fromJson_x3f___redArg___closed__10));
x_9 = lean_unsigned_to_nat(80u);
x_10 = l_Lean_Json_pretty(x_2, x_9);
x_11 = lean_string_append(x_8, x_10);
lean_dec_ref(x_10);
x_12 = ((lean_object*)(l_Array_fromJson_x3f___redArg___closed__11));
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_fromJson_x3f___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonArray___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_fromJson_x3f), 3, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonArray(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_fromJson_x3f), 3, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_alloc_closure((void*)(l_Array_toJson___redArg___lam__0), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = ((lean_object*)(l_Array_toJson___redArg___closed__9));
x_5 = lean_array_size(x_2);
x_6 = 0;
x_7 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_4, x_3, x_5, x_6, x_2);
x_8 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_toJson(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_toJson___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonArray___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_toJson), 3, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonArray(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_toJson), 3, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_fromJson_x3f___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_fromJson_x3f___redArg(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_11; 
x_4 = lean_ctor_get(x_3, 0);
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
x_5 = x_3;
x_6 = x_11;
goto block_10;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_11;
goto block_10;
}
block_10:
{
lean_object* x_7; 
if (x_6 == 0)
{
x_7 = x_5;
goto block_8;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_4);
x_7 = x_9;
goto block_8;
}
block_8:
{
return x_7;
}
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_20; 
x_12 = lean_ctor_get(x_3, 0);
x_20 = !lean_is_exclusive(x_3);
if (x_20 == 0)
{
x_13 = x_3;
x_14 = x_20;
goto block_19;
}
else
{
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_to_list(x_12);
if (x_14 == 0)
{
lean_ctor_set(x_13, 0, x_15);
x_16 = x_13;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_15);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_fromJson_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_fromJson_x3f___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonList___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_fromJson_x3f), 3, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonList(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_fromJson_x3f), 3, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_toJson___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_array_mk(x_2);
x_4 = l_Array_toJson___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_toJson(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_toJson___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonList___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_toJson), 3, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonList(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_toJson), 3, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec_ref(x_1);
x_3 = ((lean_object*)(l_Option_fromJson_x3f___redArg___closed__0));
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_12; 
x_5 = lean_ctor_get(x_4, 0);
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
x_6 = x_4;
x_7 = x_12;
goto block_11;
}
else
{
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = x_12;
goto block_11;
}
block_11:
{
lean_object* x_8; 
if (x_7 == 0)
{
x_8 = x_6;
goto block_9;
}
else
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_5);
x_8 = x_10;
goto block_9;
}
block_9:
{
return x_8;
}
}
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_21; 
x_13 = lean_ctor_get(x_4, 0);
x_21 = !lean_is_exclusive(x_4);
if (x_21 == 0)
{
x_14 = x_4;
x_15 = x_21;
goto block_20;
}
else
{
lean_inc(x_13);
lean_dec(x_4);
x_14 = lean_box(0);
x_15 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_13);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_16);
x_17 = x_14;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_16);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Option_fromJson_x3f___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonOption___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Option_fromJson_x3f), 3, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonOption(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Option_fromJson_x3f), 3, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Option_toJson___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec_ref(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Option_toJson(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Option_toJson___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonOption___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Option_toJson), 3, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonOption(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Option_toJson), 3, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Prod_fromJson_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_array_get_size(x_13);
x_15 = lean_unsigned_to_nat(2u);
x_16 = lean_nat_dec_eq(x_14, x_15);
if (x_16 == 0)
{
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = x_3;
goto block_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_inc_ref(x_13);
lean_dec_ref(x_3);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_fget_borrowed(x_13, x_17);
lean_inc(x_18);
x_19 = lean_apply_1(x_1, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_27; 
lean_dec_ref(x_13);
lean_dec_ref(x_2);
x_20 = lean_ctor_get(x_19, 0);
x_27 = !lean_is_exclusive(x_19);
if (x_27 == 0)
{
x_21 = x_19;
x_22 = x_27;
goto block_26;
}
else
{
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_23; 
if (x_22 == 0)
{
x_23 = x_21;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_20);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_19, 0);
lean_inc(x_28);
lean_dec_ref(x_19);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_array_fget(x_13, x_29);
lean_dec_ref(x_13);
x_31 = lean_apply_1(x_2, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_39; 
lean_dec(x_28);
x_32 = lean_ctor_get(x_31, 0);
x_39 = !lean_is_exclusive(x_31);
if (x_39 == 0)
{
x_33 = x_31;
x_34 = x_39;
goto block_38;
}
else
{
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_box(0);
x_34 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_35; 
if (x_34 == 0)
{
x_35 = x_33;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_32);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_48; 
x_40 = lean_ctor_get(x_31, 0);
x_48 = !lean_is_exclusive(x_31);
if (x_48 == 0)
{
x_41 = x_31;
x_42 = x_48;
goto block_47;
}
else
{
lean_inc(x_40);
lean_dec(x_31);
x_41 = lean_box(0);
x_42 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_28);
lean_ctor_set(x_43, 1, x_40);
if (x_42 == 0)
{
lean_ctor_set(x_41, 0, x_43);
x_44 = x_41;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_43);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
}
}
else
{
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = x_3;
goto block_12;
}
block_12:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = ((lean_object*)(l_Prod_fromJson_x3f___redArg___closed__0));
x_6 = lean_unsigned_to_nat(80u);
x_7 = l_Lean_Json_pretty(x_4, x_6);
x_8 = lean_string_append(x_5, x_7);
lean_dec_ref(x_7);
x_9 = ((lean_object*)(l_Array_fromJson_x3f___redArg___closed__11));
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Prod_fromJson_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Prod_fromJson_x3f___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonProd___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Prod_fromJson_x3f), 5, 4);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, lean_box(0));
lean_closure_set(x_3, 2, x_1);
lean_closure_set(x_3, 3, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonProd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Prod_fromJson_x3f), 5, 4);
lean_closure_set(x_5, 0, lean_box(0));
lean_closure_set(x_5, 1, lean_box(0));
lean_closure_set(x_5, 2, x_3);
lean_closure_set(x_5, 3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Prod_toJson___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = lean_apply_1(x_1, x_4);
x_7 = lean_apply_1(x_2, x_5);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_mk_empty_array_with_capacity(x_8);
x_10 = lean_array_push(x_9, x_6);
x_11 = lean_array_push(x_10, x_7);
x_12 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Prod_toJson(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Prod_toJson___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonProd___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Prod_toJson), 5, 4);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, lean_box(0));
lean_closure_set(x_3, 2, x_1);
lean_closure_set(x_3, 3, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonProd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Prod_toJson), 5, 4);
lean_closure_set(x_5, 0, lean_box(0));
lean_closure_set(x_5, 1, lean_box(0));
lean_closure_set(x_5, 2, x_3);
lean_closure_set(x_5, 3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_fromJson_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
lean_inc(x_1);
x_2 = l_Lean_Json_getStr_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_10; 
lean_dec(x_1);
x_3 = lean_ctor_get(x_2, 0);
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
x_4 = x_2;
x_5 = x_10;
goto block_9;
}
else
{
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = x_10;
goto block_9;
}
block_9:
{
lean_object* x_6; 
if (x_5 == 0)
{
x_6 = x_4;
goto block_7;
}
else
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_3);
x_6 = x_8;
goto block_7;
}
block_7:
{
return x_6;
}
}
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_32; 
x_11 = lean_ctor_get(x_2, 0);
x_32 = !lean_is_exclusive(x_2);
if (x_32 == 0)
{
x_12 = x_2;
x_13 = x_32;
goto block_31;
}
else
{
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_14; uint8_t x_15; 
x_14 = ((lean_object*)(l_Lean_Name_fromJson_x3f___closed__0));
x_15 = lean_string_dec_eq(x_11, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_String_toName(x_11);
x_17 = l_Lean_Name_isAnonymous(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_1);
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_16);
x_18 = x_12;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_16);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_16);
x_21 = ((lean_object*)(l_Lean_Name_fromJson_x3f___closed__1));
x_22 = lean_unsigned_to_nat(80u);
x_23 = l_Lean_Json_pretty(x_1, x_22);
x_24 = lean_string_append(x_21, x_23);
lean_dec_ref(x_23);
x_25 = ((lean_object*)(l_Array_fromJson_x3f___redArg___closed__11));
x_26 = lean_string_append(x_24, x_25);
if (x_13 == 0)
{
lean_ctor_set_tag(x_12, 0);
lean_ctor_set(x_12, 0, x_26);
x_27 = x_12;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_26);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
else
{
lean_object* x_30; 
lean_del_object(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_30 = ((lean_object*)(l_Lean_Name_fromJson_x3f___closed__2));
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonName___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_2 = 1;
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_1, x_2);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = ((lean_object*)(l_Lean_Name_fromJson_x3f___closed__0));
x_6 = lean_string_dec_eq(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
lean_inc_ref(x_3);
x_7 = l_String_toName(x_3);
x_8 = l_Lean_Name_isAnonymous(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec_ref(x_3);
x_9 = lean_apply_1(x_1, x_4);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_17; 
lean_dec(x_7);
lean_dec(x_2);
x_10 = lean_ctor_get(x_9, 0);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
x_11 = x_9;
x_12 = x_17;
goto block_16;
}
else
{
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_13; 
if (x_12 == 0)
{
x_13 = x_11;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_10);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_26; 
x_18 = lean_ctor_get(x_9, 0);
x_26 = !lean_is_exclusive(x_9);
if (x_26 == 0)
{
x_19 = x_9;
x_20 = x_26;
goto block_25;
}
else
{
lean_inc(x_18);
lean_dec(x_9);
x_19 = lean_box(0);
x_20 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(x_7, x_18, x_2);
if (x_20 == 0)
{
lean_ctor_set(x_19, 0, x_21);
x_22 = x_19;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_21);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_27 = ((lean_object*)(l_Lean_Name_fromJson_x3f___closed__1));
x_28 = lean_string_append(x_27, x_3);
lean_dec_ref(x_3);
x_29 = ((lean_object*)(l_Array_fromJson_x3f___redArg___closed__11));
x_30 = lean_string_append(x_28, x_29);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
else
{
lean_object* x_32; 
lean_dec_ref(x_3);
x_32 = lean_apply_1(x_1, x_4);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_40; 
lean_dec(x_2);
x_33 = lean_ctor_get(x_32, 0);
x_40 = !lean_is_exclusive(x_32);
if (x_40 == 0)
{
x_34 = x_32;
x_35 = x_40;
goto block_39;
}
else
{
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_box(0);
x_35 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_36; 
if (x_35 == 0)
{
x_36 = x_34;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_33);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_50; 
x_41 = lean_ctor_get(x_32, 0);
x_50 = !lean_is_exclusive(x_32);
if (x_50 == 0)
{
x_42 = x_32;
x_43 = x_50;
goto block_49;
}
else
{
lean_inc(x_41);
lean_dec(x_32);
x_42 = lean_box(0);
x_43 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_box(0);
x_45 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(x_44, x_41, x_2);
if (x_43 == 0)
{
lean_ctor_set(x_42, 0, x_45);
x_46 = x_42;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_45);
x_46 = x_48;
goto block_47;
}
block_47:
{
return x_46;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = ((lean_object*)(l_Array_fromJson_x3f___redArg___closed__9));
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lean_alloc_closure((void*)(l_Lean_NameMap_fromJson_x3f___redArg___lam__0), 4, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_box(1);
x_7 = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(x_3, x_5, x_6, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec_ref(x_1);
x_8 = ((lean_object*)(l_Lean_NameMap_fromJson_x3f___redArg___closed__0));
x_9 = lean_unsigned_to_nat(80u);
x_10 = l_Lean_Json_pretty(x_2, x_9);
x_11 = lean_string_append(x_8, x_10);
lean_dec_ref(x_10);
x_12 = ((lean_object*)(l_Array_fromJson_x3f___redArg___closed__11));
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_NameMap_fromJson_x3f___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonNameMap___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_NameMap_fromJson_x3f), 3, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonNameMap(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_NameMap_fromJson_x3f), 3, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_NameMap_toJson___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_string_dec_lt(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = lean_string_dec_eq(x_1, x_2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 2;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_NameMap_toJson___redArg___lam__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = 1;
x_7 = l_Lean_Name_toString(x_4, x_6);
x_8 = lean_apply_1(x_1, x_5);
x_9 = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(x_2, x_7, x_8, x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = ((lean_object*)(l_Lean_NameMap_toJson___redArg___closed__0));
x_4 = lean_alloc_closure((void*)(l_Lean_NameMap_toJson___redArg___lam__1), 5, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
x_5 = lean_box(1);
x_6 = l_Std_DTreeMap_Internal_Impl_foldl___redArg(x_4, x_5, x_2);
x_7 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_NameMap_toJson___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonNameMap___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_NameMap_toJson), 3, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonNameMap(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_NameMap_toJson), 3, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_bignumFromJson_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
lean_inc(x_1);
x_2 = l_Lean_Json_getStr_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_10; 
lean_dec(x_1);
x_3 = lean_ctor_get(x_2, 0);
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
x_4 = x_2;
x_5 = x_10;
goto block_9;
}
else
{
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = x_10;
goto block_9;
}
block_9:
{
lean_object* x_6; 
if (x_5 == 0)
{
x_6 = x_4;
goto block_7;
}
else
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_3);
x_6 = x_8;
goto block_7;
}
block_7:
{
return x_6;
}
}
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_29; 
x_11 = lean_ctor_get(x_2, 0);
x_29 = !lean_is_exclusive(x_2);
if (x_29 == 0)
{
x_12 = x_2;
x_13 = x_29;
goto block_28;
}
else
{
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_14; 
x_14 = l_Lean_Syntax_decodeNatLitVal_x3f(x_11);
lean_dec(x_11);
if (lean_obj_tag(x_14) == 1)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_15);
x_16 = x_12;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_15);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_14);
x_19 = ((lean_object*)(l_Lean_bignumFromJson_x3f___closed__0));
x_20 = lean_unsigned_to_nat(80u);
x_21 = l_Lean_Json_pretty(x_1, x_20);
x_22 = lean_string_append(x_19, x_21);
lean_dec_ref(x_21);
x_23 = ((lean_object*)(l_Array_fromJson_x3f___redArg___closed__11));
x_24 = lean_string_append(x_22, x_23);
if (x_13 == 0)
{
lean_ctor_set_tag(x_12, 0);
lean_ctor_set(x_12, 0, x_24);
x_25 = x_12;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_24);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_bignumToJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Nat_reprFast(x_1);
x_3 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_USize_fromJson_x3f___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_System_Platform_numBits;
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_nat_pow(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_USize_fromJson_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
lean_inc(x_1);
x_2 = l_Lean_bignumFromJson_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_10; 
lean_dec(x_1);
x_3 = lean_ctor_get(x_2, 0);
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
x_4 = x_2;
x_5 = x_10;
goto block_9;
}
else
{
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = x_10;
goto block_9;
}
block_9:
{
lean_object* x_6; 
if (x_5 == 0)
{
x_6 = x_4;
goto block_7;
}
else
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_3);
x_6 = x_8;
goto block_7;
}
block_7:
{
return x_6;
}
}
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_31; 
x_11 = lean_ctor_get(x_2, 0);
x_31 = !lean_is_exclusive(x_2);
if (x_31 == 0)
{
x_12 = x_2;
x_13 = x_31;
goto block_30;
}
else
{
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_obj_once(&l_USize_fromJson_x3f___closed__0, &l_USize_fromJson_x3f___closed__0_once, _init_l_USize_fromJson_x3f___closed__0);
x_15 = lean_nat_dec_le(x_14, x_11);
if (x_15 == 0)
{
size_t x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_16 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_17 = lean_box_usize(x_16);
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_17);
x_18 = x_12;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_17);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_11);
x_21 = ((lean_object*)(l_USize_fromJson_x3f___closed__1));
x_22 = lean_unsigned_to_nat(80u);
x_23 = l_Lean_Json_pretty(x_1, x_22);
x_24 = lean_string_append(x_21, x_23);
lean_dec_ref(x_23);
x_25 = ((lean_object*)(l_USize_fromJson_x3f___closed__2));
x_26 = lean_string_append(x_24, x_25);
if (x_13 == 0)
{
lean_ctor_set_tag(x_12, 0);
lean_ctor_set(x_12, 0, x_26);
x_27 = x_12;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_26);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonUSize___lam__0(size_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_usize_to_nat(x_1);
x_3 = l_Lean_bignumToJson(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonUSize___lam__0___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_3 = l_Lean_instToJsonUSize___lam__0(x_2);
return x_3;
}
}
static lean_object* _init_l_UInt64_fromJson_x3f___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_cstr_to_nat("18446744073709551616");
return x_1;
}
}
LEAN_EXPORT lean_object* l_UInt64_fromJson_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
lean_inc(x_1);
x_2 = l_Lean_bignumFromJson_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_10; 
lean_dec(x_1);
x_3 = lean_ctor_get(x_2, 0);
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
x_4 = x_2;
x_5 = x_10;
goto block_9;
}
else
{
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = x_10;
goto block_9;
}
block_9:
{
lean_object* x_6; 
if (x_5 == 0)
{
x_6 = x_4;
goto block_7;
}
else
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_3);
x_6 = x_8;
goto block_7;
}
block_7:
{
return x_6;
}
}
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_31; 
x_11 = lean_ctor_get(x_2, 0);
x_31 = !lean_is_exclusive(x_2);
if (x_31 == 0)
{
x_12 = x_2;
x_13 = x_31;
goto block_30;
}
else
{
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_obj_once(&l_UInt64_fromJson_x3f___closed__0, &l_UInt64_fromJson_x3f___closed__0_once, _init_l_UInt64_fromJson_x3f___closed__0);
x_15 = lean_nat_dec_le(x_14, x_11);
if (x_15 == 0)
{
uint64_t x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_16 = lean_uint64_of_nat(x_11);
lean_dec(x_11);
x_17 = lean_box_uint64(x_16);
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_17);
x_18 = x_12;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_17);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_11);
x_21 = ((lean_object*)(l_USize_fromJson_x3f___closed__1));
x_22 = lean_unsigned_to_nat(80u);
x_23 = l_Lean_Json_pretty(x_1, x_22);
x_24 = lean_string_append(x_21, x_23);
lean_dec_ref(x_23);
x_25 = ((lean_object*)(l_UInt64_fromJson_x3f___closed__1));
x_26 = lean_string_append(x_24, x_25);
if (x_13 == 0)
{
lean_ctor_set_tag(x_12, 0);
lean_ctor_set(x_12, 0, x_26);
x_27 = x_12;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_26);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonUInt64___lam__0(uint64_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_uint64_to_nat(x_1);
x_3 = l_Lean_bignumToJson(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonUInt64___lam__0___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint64(x_1);
lean_dec_ref(x_1);
x_3 = l_Lean_instToJsonUInt64___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Float_toJson(double x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonNumber_fromFloat_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_10; 
x_3 = lean_ctor_get(x_2, 0);
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
x_4 = x_2;
x_5 = x_10;
goto block_9;
}
else
{
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = x_10;
goto block_9;
}
block_9:
{
lean_object* x_6; 
if (x_5 == 0)
{
lean_ctor_set_tag(x_4, 3);
x_6 = x_4;
goto block_7;
}
else
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_3);
x_6 = x_8;
goto block_7;
}
block_7:
{
return x_6;
}
}
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_18; 
x_11 = lean_ctor_get(x_2, 0);
x_18 = !lean_is_exclusive(x_2);
if (x_18 == 0)
{
x_12 = x_2;
x_13 = x_18;
goto block_17;
}
else
{
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_14; 
if (x_13 == 0)
{
lean_ctor_set_tag(x_12, 2);
x_14 = x_12;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_16, 0, x_11);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Float_toJson___boxed(lean_object* x_1) {
_start:
{
double x_2; lean_object* x_3; 
x_2 = lean_unbox_float(x_1);
lean_dec_ref(x_1);
x_3 = l_Float_toJson(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Float_fromJson_x3f(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 3:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_43; 
x_4 = lean_ctor_get(x_1, 0);
x_43 = !lean_is_exclusive(x_1);
if (x_43 == 0)
{
x_5 = x_1;
x_6 = x_43;
goto block_42;
}
else
{
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_7; uint8_t x_8; 
x_7 = ((lean_object*)(l_Float_fromJson_x3f___closed__2));
x_8 = lean_string_dec_eq(x_4, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = ((lean_object*)(l_Float_fromJson_x3f___closed__3));
x_10 = lean_string_dec_eq(x_4, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = ((lean_object*)(l_Float_fromJson_x3f___closed__4));
x_12 = lean_string_dec_eq(x_4, x_11);
lean_dec_ref(x_4);
if (x_12 == 0)
{
lean_del_object(x_5);
goto block_3;
}
else
{
lean_object* x_13; lean_object* x_14; double x_15; double x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Float_ofScientific(x_13, x_12, x_14);
x_16 = lean_float_div(x_15, x_15);
x_17 = lean_box_float(x_16);
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_17);
x_18 = x_5;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_17);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; double x_23; double x_24; lean_object* x_25; double x_26; double x_27; lean_object* x_28; lean_object* x_29; 
lean_dec_ref(x_4);
x_21 = lean_unsigned_to_nat(10u);
x_22 = lean_unsigned_to_nat(1u);
x_23 = l_Float_ofScientific(x_21, x_10, x_22);
x_24 = lean_float_negate(x_23);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Float_ofScientific(x_25, x_10, x_22);
x_27 = lean_float_div(x_24, x_26);
x_28 = lean_box_float(x_27);
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_28);
x_29 = x_5;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_28);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; double x_34; lean_object* x_35; double x_36; double x_37; lean_object* x_38; lean_object* x_39; 
lean_dec_ref(x_4);
x_32 = lean_unsigned_to_nat(10u);
x_33 = lean_unsigned_to_nat(1u);
x_34 = l_Float_ofScientific(x_32, x_8, x_33);
x_35 = lean_unsigned_to_nat(0u);
x_36 = l_Float_ofScientific(x_35, x_8, x_33);
x_37 = lean_float_div(x_34, x_36);
x_38 = lean_box_float(x_37);
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_38);
x_39 = x_5;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_38);
x_39 = x_41;
goto block_40;
}
block_40:
{
return x_39;
}
}
}
}
case 2:
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_53; 
x_44 = lean_ctor_get(x_1, 0);
x_53 = !lean_is_exclusive(x_1);
if (x_53 == 0)
{
x_45 = x_1;
x_46 = x_53;
goto block_52;
}
else
{
lean_inc(x_44);
lean_dec(x_1);
x_45 = lean_box(0);
x_46 = x_53;
goto block_52;
}
block_52:
{
double x_47; lean_object* x_48; lean_object* x_49; 
x_47 = l_Lean_JsonNumber_toFloat(x_44);
x_48 = lean_box_float(x_47);
if (x_46 == 0)
{
lean_ctor_set_tag(x_45, 1);
lean_ctor_set(x_45, 0, x_48);
x_49 = x_45;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_48);
x_49 = x_51;
goto block_50;
}
block_50:
{
return x_49;
}
}
}
default: 
{
lean_dec(x_1);
goto block_3;
}
}
block_3:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Float_fromJson_x3f___closed__1));
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_fromJson_x3f(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; uint8_t x_10; 
x_2 = lean_ctor_get(x_1, 0);
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
x_3 = x_1;
x_4 = x_10;
goto block_9;
}
else
{
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_box(0);
x_4 = x_10;
goto block_9;
}
block_9:
{
lean_object* x_5; 
if (x_4 == 0)
{
lean_ctor_set_tag(x_3, 0);
x_5 = x_3;
goto block_7;
}
else
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_2);
x_5 = x_8;
goto block_7;
}
block_7:
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
}
case 5:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_19; 
x_11 = lean_ctor_get(x_1, 0);
x_19 = !lean_is_exclusive(x_1);
if (x_19 == 0)
{
x_12 = x_1;
x_13 = x_19;
goto block_18;
}
else
{
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_14; 
if (x_13 == 0)
{
lean_ctor_set_tag(x_12, 1);
x_14 = x_12;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_11);
x_14 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
default: 
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = ((lean_object*)(l_Lean_Json_Structured_fromJson_x3f___closed__0));
x_21 = lean_unsigned_to_nat(80u);
x_22 = l_Lean_Json_pretty(x_1, x_21);
x_23 = lean_string_append(x_20, x_22);
lean_dec_ref(x_22);
x_24 = ((lean_object*)(l_Array_fromJson_x3f___redArg___closed__11));
x_25 = lean_string_append(x_23, x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_toJson(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; uint8_t x_9; 
x_2 = lean_ctor_get(x_1, 0);
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
x_3 = x_1;
x_4 = x_9;
goto block_8;
}
else
{
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_box(0);
x_4 = x_9;
goto block_8;
}
block_8:
{
lean_object* x_5; 
if (x_4 == 0)
{
lean_ctor_set_tag(x_3, 4);
x_5 = x_3;
goto block_6;
}
else
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_7, 0, x_2);
x_5 = x_7;
goto block_6;
}
block_6:
{
return x_5;
}
}
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_17; 
x_10 = lean_ctor_get(x_1, 0);
x_17 = !lean_is_exclusive(x_1);
if (x_17 == 0)
{
x_11 = x_1;
x_12 = x_17;
goto block_16;
}
else
{
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_13; 
if (x_12 == 0)
{
lean_ctor_set_tag(x_11, 5);
x_13 = x_11;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_15, 0, x_10);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_apply_1(x_1, x_2);
x_4 = l_Lean_Json_Structured_fromJson_x3f(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Json_toStructured_x3f___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Json_getObjValD(x_1, x_3);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Json_getObjValAs_x3f___redArg(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Json_getObjValAs_x3f___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Json_getObjValAs_x3f(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_setObjValAs_x21___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_apply_1(x_2, x_4);
x_6 = l_Lean_Json_setObjVal_x21(x_1, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_setObjValAs_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Json_setObjValAs_x21___redArg(x_1, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = lean_apply_1(x_1, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Json_opt___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getTag_x3f(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 3:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; uint8_t x_9; 
x_2 = lean_ctor_get(x_1, 0);
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
x_3 = x_1;
x_4 = x_9;
goto block_8;
}
else
{
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_box(0);
x_4 = x_9;
goto block_8;
}
block_8:
{
lean_object* x_5; 
if (x_4 == 0)
{
lean_ctor_set_tag(x_3, 1);
x_5 = x_3;
goto block_6;
}
else
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_2);
x_5 = x_7;
goto block_6;
}
block_6:
{
return x_5;
}
}
}
case 5:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec_ref(x_1);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
x_11 = x_17;
goto block_16;
}
else
{
lean_object* x_18; 
x_18 = lean_unsigned_to_nat(0u);
x_11 = x_18;
goto block_16;
}
block_16:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_dec_eq(x_11, x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(x_10);
lean_dec(x_10);
return x_15;
}
}
}
default: 
{
lean_object* x_19; 
lean_dec(x_1);
x_19 = lean_box(0);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Json_parseTagged_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_array_uget_borrowed(x_2, x_4);
x_9 = l_Lean_Name_getString_x21(x_8);
lean_inc(x_1);
x_10 = l_Lean_Json_getObjVal_x3f(x_1, x_9);
lean_dec_ref(x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_18; 
lean_dec_ref(x_5);
lean_dec(x_1);
x_11 = lean_ctor_get(x_10, 0);
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
x_12 = x_10;
x_13 = x_18;
goto block_17;
}
else
{
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_14; 
if (x_13 == 0)
{
x_14 = x_12;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_11);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; 
x_19 = lean_ctor_get(x_10, 0);
lean_inc(x_19);
lean_dec_ref(x_10);
x_20 = lean_array_push(x_5, x_19);
x_21 = 1;
x_22 = lean_usize_add(x_4, x_21);
x_4 = x_22;
x_5 = x_20;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Json_parseTagged_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Json_parseTagged_spec__0(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_parseTagged(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = l_Lean_Json_getObjVal_x3f(x_1, x_2);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_15; 
lean_dec(x_3);
x_8 = lean_ctor_get(x_7, 0);
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
x_9 = x_7;
x_10 = x_15;
goto block_14;
}
else
{
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = x_15;
goto block_14;
}
block_14:
{
lean_object* x_11; 
if (x_10 == 0)
{
x_11 = x_9;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_8);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
}
else
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_46; 
x_16 = lean_ctor_get(x_7, 0);
x_46 = !lean_is_exclusive(x_7);
if (x_46 == 0)
{
x_17 = x_7;
x_18 = x_46;
goto block_45;
}
else
{
lean_inc(x_16);
lean_dec(x_7);
x_17 = lean_box(0);
x_18 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_dec_eq(x_3, x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_del_object(x_17);
x_21 = l_Lean_Json_getArr_x3f(x_16);
if (lean_obj_tag(x_21) == 0)
{
lean_dec(x_3);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_array_get_size(x_22);
lean_dec(x_22);
x_24 = lean_nat_dec_eq(x_23, x_3);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; uint8_t x_38; 
x_38 = !lean_is_exclusive(x_21);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_21, 0);
lean_dec(x_39);
x_25 = x_21;
x_26 = x_38;
goto block_37;
}
else
{
lean_dec(x_21);
x_25 = lean_box(0);
x_26 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_27 = ((lean_object*)(l_Lean_Json_parseTagged___closed__0));
x_28 = l_Nat_reprFast(x_23);
x_29 = lean_string_append(x_27, x_28);
lean_dec_ref(x_28);
x_30 = ((lean_object*)(l_Lean_Json_parseTagged___closed__1));
x_31 = lean_string_append(x_29, x_30);
x_32 = l_Nat_reprFast(x_3);
x_33 = lean_string_append(x_31, x_32);
lean_dec_ref(x_32);
if (x_26 == 0)
{
lean_ctor_set_tag(x_25, 0);
lean_ctor_set(x_25, 0, x_33);
x_34 = x_25;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_33);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
}
else
{
lean_dec(x_3);
return x_21;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_3);
x_40 = lean_mk_empty_array_with_capacity(x_19);
x_41 = lean_array_push(x_40, x_16);
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_41);
x_42 = x_17;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_41);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; size_t x_50; size_t x_51; lean_object* x_52; 
lean_dec(x_3);
x_47 = lean_ctor_get(x_7, 0);
lean_inc(x_47);
lean_dec_ref(x_7);
x_48 = lean_ctor_get(x_4, 0);
x_49 = ((lean_object*)(l_Lean_Json_parseTagged___closed__2));
x_50 = lean_array_size(x_48);
x_51 = 0;
x_52 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Json_parseTagged_spec__0(x_47, x_48, x_50, x_51, x_49);
return x_52;
}
}
}
else
{
lean_object* x_53; 
lean_dec(x_3);
x_53 = l_Lean_Json_getStr_x3f(x_1);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_61; 
x_54 = lean_ctor_get(x_53, 0);
x_61 = !lean_is_exclusive(x_53);
if (x_61 == 0)
{
x_55 = x_53;
x_56 = x_61;
goto block_60;
}
else
{
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_box(0);
x_56 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_57; 
if (x_56 == 0)
{
x_57 = x_55;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_54);
x_57 = x_59;
goto block_58;
}
block_58:
{
return x_57;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_76; 
x_62 = lean_ctor_get(x_53, 0);
x_76 = !lean_is_exclusive(x_53);
if (x_76 == 0)
{
x_63 = x_53;
x_64 = x_76;
goto block_75;
}
else
{
lean_inc(x_62);
lean_dec(x_53);
x_63 = lean_box(0);
x_64 = x_76;
goto block_75;
}
block_75:
{
uint8_t x_65; 
x_65 = lean_string_dec_eq(x_62, x_2);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_66 = ((lean_object*)(l_Lean_Json_parseTagged___closed__3));
x_67 = lean_string_append(x_66, x_62);
lean_dec(x_62);
x_68 = ((lean_object*)(l_Lean_Json_parseTagged___closed__1));
x_69 = lean_string_append(x_67, x_68);
x_70 = lean_string_append(x_69, x_2);
if (x_64 == 0)
{
lean_ctor_set_tag(x_63, 0);
lean_ctor_set(x_63, 0, x_70);
x_71 = x_63;
goto block_72;
}
else
{
lean_object* x_73; 
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_70);
x_71 = x_73;
goto block_72;
}
block_72:
{
return x_71;
}
}
else
{
lean_object* x_74; 
lean_del_object(x_63);
lean_dec(x_62);
x_74 = ((lean_object*)(l_Lean_Json_parseTagged___closed__4));
return x_74;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_parseTagged___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Json_parseTagged(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_parseCtorFields_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_array_uget_borrowed(x_4, x_3);
x_8 = l_Lean_Name_getString_x21(x_7);
lean_inc(x_1);
x_9 = l_Lean_Json_getObjVal_x3f(x_1, x_8);
lean_dec_ref(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_17; 
lean_dec_ref(x_4);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 0);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
x_11 = x_9;
x_12 = x_17;
goto block_16;
}
else
{
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_13; 
if (x_12 == 0)
{
x_13 = x_11;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_10);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_9, 0);
lean_inc(x_18);
lean_dec_ref(x_9);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_array_uset(x_4, x_3, x_19);
x_21 = 1;
x_22 = lean_usize_add(x_3, x_21);
x_23 = lean_array_uset(x_20, x_3, x_18);
x_3 = x_22;
x_4 = x_23;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_parseCtorFields_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_parseCtorFields_spec__0(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_parseCtorFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Json_getObjVal_x3f(x_1, x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_13; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_ctor_get(x_5, 0);
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
x_7 = x_5;
x_8 = x_13;
goto block_12;
}
else
{
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = x_13;
goto block_12;
}
block_12:
{
lean_object* x_9; 
if (x_8 == 0)
{
x_9 = x_7;
goto block_10;
}
else
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_6);
x_9 = x_11;
goto block_10;
}
block_10:
{
return x_9;
}
}
}
else
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_44; 
x_14 = lean_ctor_get(x_5, 0);
x_44 = !lean_is_exclusive(x_5);
if (x_44 == 0)
{
x_15 = x_5;
x_16 = x_44;
goto block_43;
}
else
{
lean_inc(x_14);
lean_dec(x_5);
x_15 = lean_box(0);
x_16 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_dec_eq(x_3, x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_del_object(x_15);
x_19 = l_Lean_Json_getArr_x3f(x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_dec(x_3);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_array_get_size(x_20);
lean_dec(x_20);
x_22 = lean_nat_dec_eq(x_21, x_3);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; uint8_t x_36; 
x_36 = !lean_is_exclusive(x_19);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_19, 0);
lean_dec(x_37);
x_23 = x_19;
x_24 = x_36;
goto block_35;
}
else
{
lean_dec(x_19);
x_23 = lean_box(0);
x_24 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_25 = ((lean_object*)(l_Lean_Json_parseTagged___closed__0));
x_26 = l_Nat_reprFast(x_21);
x_27 = lean_string_append(x_25, x_26);
lean_dec_ref(x_26);
x_28 = ((lean_object*)(l_Lean_Json_parseTagged___closed__1));
x_29 = lean_string_append(x_27, x_28);
x_30 = l_Nat_reprFast(x_3);
x_31 = lean_string_append(x_29, x_30);
lean_dec_ref(x_30);
if (x_24 == 0)
{
lean_ctor_set_tag(x_23, 0);
lean_ctor_set(x_23, 0, x_31);
x_32 = x_23;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_31);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
else
{
lean_dec(x_3);
return x_19;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_3);
x_38 = lean_mk_empty_array_with_capacity(x_17);
x_39 = lean_array_push(x_38, x_14);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_39);
x_40 = x_15;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_39);
x_40 = x_42;
goto block_41;
}
block_41:
{
return x_40;
}
}
}
}
else
{
lean_object* x_45; lean_object* x_46; size_t x_47; size_t x_48; lean_object* x_49; 
lean_dec(x_3);
x_45 = lean_ctor_get(x_5, 0);
lean_inc(x_45);
lean_dec_ref(x_5);
x_46 = lean_ctor_get(x_4, 0);
lean_inc(x_46);
lean_dec_ref(x_4);
x_47 = lean_array_size(x_46);
x_48 = 0;
x_49 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_parseCtorFields_spec__0(x_45, x_47, x_48, x_46);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_parseCtorFields___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Json_parseCtorFields(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
return x_5;
}
}
lean_object* runtime_initialize_Lean_Data_Json_Printer(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_GetLit(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Json_FromToJson_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Data_Json_Printer(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Macro(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_GetLit(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Json_FromToJson_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_Json_Printer(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* initialize_Init_Data_Array_GetLit(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Json_FromToJson_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Json_Printer(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Macro(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_GetLit(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Json_FromToJson_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Json_FromToJson_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Json_FromToJson_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
