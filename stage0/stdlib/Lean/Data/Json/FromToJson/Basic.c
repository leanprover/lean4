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
lean_object* l_Except_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_instMonad___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_instMonad___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_pure(lean_object*, lean_object*, lean_object*);
lean_object* l_Except_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_String_toName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_String_toSlice(lean_object*);
lean_object* l_Lean_Json_getObjVal_x3f(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Json_getArr_x3f(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Name_getString_x21(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* l_Function_comp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_setObjVal_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getInt_x3f(lean_object*);
lean_object* l_Lean_Json_getBool_x3f___boxed(lean_object*);
lean_object* l_Lean_JsonNumber_fromFloat_x3f(double);
lean_object* l_Lean_JsonNumber_fromInt(lean_object*);
double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
double lean_float_div(double, double);
double lean_float_negate(double);
double l_Lean_JsonNumber_toFloat(lean_object*);
lean_object* l_Lean_Syntax_decodeNatLitVal_x3f(lean_object*);
extern lean_object* l_System_Platform_numBits;
lean_object* lean_nat_pow(lean_object*, lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_uint64_to_nat(uint64_t);
lean_object* l_Lean_Json_getNat_x3f(lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_Json_getNum_x3f(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonJson___lam__0(lean_object*);
static const lean_closure_object l_Lean_instFromJsonJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instFromJsonJson___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonJson___closed__0 = (const lean_object*)&l_Lean_instFromJsonJson___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instFromJsonJson = (const lean_object*)&l_Lean_instFromJsonJson___closed__0_value;
static const lean_closure_object l_Lean_instToJsonJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_instToJsonJson___closed__0 = (const lean_object*)&l_Lean_instToJsonJson___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonJson = (const lean_object*)&l_Lean_instToJsonJson___closed__0_value;
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
LEAN_EXPORT lean_object* l_Lean_instFromJsonEmpty___lam__0(lean_object*);
static const lean_closure_object l_Lean_instFromJsonEmpty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instFromJsonEmpty___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonEmpty___closed__0 = (const lean_object*)&l_Lean_instFromJsonEmpty___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instFromJsonEmpty = (const lean_object*)&l_Lean_instFromJsonEmpty___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instToJsonEmpty___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_instToJsonEmpty___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_instToJsonEmpty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonEmpty___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonEmpty___closed__0 = (const lean_object*)&l_Lean_instToJsonEmpty___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonEmpty = (const lean_object*)&l_Lean_instToJsonEmpty___closed__0_value;
static const lean_closure_object l_Lean_instFromJsonBool___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Json_getBool_x3f___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonBool___closed__0 = (const lean_object*)&l_Lean_instFromJsonBool___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instFromJsonBool = (const lean_object*)&l_Lean_instFromJsonBool___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instToJsonBool___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_instToJsonBool___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_instToJsonBool___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonBool___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonBool___closed__0 = (const lean_object*)&l_Lean_instToJsonBool___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonBool = (const lean_object*)&l_Lean_instToJsonBool___closed__0_value;
static const lean_closure_object l_Lean_instFromJsonNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Json_getNat_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonNat___closed__0 = (const lean_object*)&l_Lean_instFromJsonNat___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instFromJsonNat = (const lean_object*)&l_Lean_instFromJsonNat___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instToJsonNat___lam__0(lean_object*);
static const lean_closure_object l_Lean_instToJsonNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonNat___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonNat___closed__0 = (const lean_object*)&l_Lean_instToJsonNat___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonNat = (const lean_object*)&l_Lean_instToJsonNat___closed__0_value;
static const lean_closure_object l_Lean_instFromJsonInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Json_getInt_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonInt___closed__0 = (const lean_object*)&l_Lean_instFromJsonInt___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instFromJsonInt = (const lean_object*)&l_Lean_instFromJsonInt___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instToJsonInt___lam__0(lean_object*);
static const lean_closure_object l_Lean_instToJsonInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonInt___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonInt___closed__0 = (const lean_object*)&l_Lean_instToJsonInt___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonInt = (const lean_object*)&l_Lean_instToJsonInt___closed__0_value;
static const lean_closure_object l_Lean_instFromJsonString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Json_getStr_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonString___closed__0 = (const lean_object*)&l_Lean_instFromJsonString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instFromJsonString = (const lean_object*)&l_Lean_instFromJsonString___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instToJsonString___lam__0(lean_object*);
static const lean_closure_object l_Lean_instToJsonString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonString___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonString___closed__0 = (const lean_object*)&l_Lean_instToJsonString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonString = (const lean_object*)&l_Lean_instToJsonString___closed__0_value;
static const lean_closure_object l_Lean_instFromJsonSlice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_toSlice, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonSlice___closed__0 = (const lean_object*)&l_Lean_instFromJsonSlice___closed__0_value;
static const lean_closure_object l_Lean_instFromJsonSlice___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_map, .m_arity = 5, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instFromJsonSlice___closed__0_value)} };
static const lean_object* l_Lean_instFromJsonSlice___closed__1 = (const lean_object*)&l_Lean_instFromJsonSlice___closed__1_value;
static const lean_closure_object l_Lean_instFromJsonSlice___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Function_comp, .m_arity = 6, .m_num_fixed = 5, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instFromJsonSlice___closed__1_value),((lean_object*)&l_Lean_instFromJsonString___closed__0_value)} };
static const lean_object* l_Lean_instFromJsonSlice___closed__2 = (const lean_object*)&l_Lean_instFromJsonSlice___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_instFromJsonSlice = (const lean_object*)&l_Lean_instFromJsonSlice___closed__2_value;
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
static const lean_closure_object l_Array_fromJson_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_fromJson_x3f___redArg___closed__0 = (const lean_object*)&l_Array_fromJson_x3f___redArg___closed__0_value;
static const lean_closure_object l_Array_fromJson_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_instMonad___lam__1, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_fromJson_x3f___redArg___closed__1 = (const lean_object*)&l_Array_fromJson_x3f___redArg___closed__1_value;
static const lean_closure_object l_Array_fromJson_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_instMonad___lam__2___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_fromJson_x3f___redArg___closed__2 = (const lean_object*)&l_Array_fromJson_x3f___redArg___closed__2_value;
static const lean_closure_object l_Array_fromJson_x3f___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_fromJson_x3f___redArg___closed__3 = (const lean_object*)&l_Array_fromJson_x3f___redArg___closed__3_value;
static const lean_closure_object l_Array_fromJson_x3f___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_map, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Array_fromJson_x3f___redArg___closed__4 = (const lean_object*)&l_Array_fromJson_x3f___redArg___closed__4_value;
static const lean_ctor_object l_Array_fromJson_x3f___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_fromJson_x3f___redArg___closed__4_value),((lean_object*)&l_Array_fromJson_x3f___redArg___closed__0_value)}};
static const lean_object* l_Array_fromJson_x3f___redArg___closed__5 = (const lean_object*)&l_Array_fromJson_x3f___redArg___closed__5_value;
static const lean_closure_object l_Array_fromJson_x3f___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_pure, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Array_fromJson_x3f___redArg___closed__6 = (const lean_object*)&l_Array_fromJson_x3f___redArg___closed__6_value;
static const lean_ctor_object l_Array_fromJson_x3f___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_fromJson_x3f___redArg___closed__5_value),((lean_object*)&l_Array_fromJson_x3f___redArg___closed__6_value),((lean_object*)&l_Array_fromJson_x3f___redArg___closed__1_value),((lean_object*)&l_Array_fromJson_x3f___redArg___closed__2_value),((lean_object*)&l_Array_fromJson_x3f___redArg___closed__3_value)}};
static const lean_object* l_Array_fromJson_x3f___redArg___closed__7 = (const lean_object*)&l_Array_fromJson_x3f___redArg___closed__7_value;
static const lean_closure_object l_Array_fromJson_x3f___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_bind, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Array_fromJson_x3f___redArg___closed__8 = (const lean_object*)&l_Array_fromJson_x3f___redArg___closed__8_value;
static const lean_ctor_object l_Array_fromJson_x3f___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_fromJson_x3f___redArg___closed__7_value),((lean_object*)&l_Array_fromJson_x3f___redArg___closed__8_value)}};
static const lean_object* l_Array_fromJson_x3f___redArg___closed__9 = (const lean_object*)&l_Array_fromJson_x3f___redArg___closed__9_value;
static const lean_string_object l_Array_fromJson_x3f___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Array_fromJson_x3f___redArg___closed__10 = (const lean_object*)&l_Array_fromJson_x3f___redArg___closed__10_value;
static const lean_string_object l_Array_fromJson_x3f___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Array_fromJson_x3f___redArg___closed__11 = (const lean_object*)&l_Array_fromJson_x3f___redArg___closed__11_value;
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Array_toJson___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_toJson___redArg___closed__0 = (const lean_object*)&l_Array_toJson___redArg___closed__0_value;
static const lean_closure_object l_Array_toJson___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_toJson___redArg___closed__1 = (const lean_object*)&l_Array_toJson___redArg___closed__1_value;
static const lean_closure_object l_Array_toJson___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_toJson___redArg___closed__2 = (const lean_object*)&l_Array_toJson___redArg___closed__2_value;
static const lean_closure_object l_Array_toJson___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_toJson___redArg___closed__3 = (const lean_object*)&l_Array_toJson___redArg___closed__3_value;
static const lean_closure_object l_Array_toJson___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_toJson___redArg___closed__4 = (const lean_object*)&l_Array_toJson___redArg___closed__4_value;
static const lean_closure_object l_Array_toJson___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_toJson___redArg___closed__5 = (const lean_object*)&l_Array_toJson___redArg___closed__5_value;
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
LEAN_EXPORT lean_object* l_List_fromJson_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_fromJson_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonList(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Prod_fromJson_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_fromJson_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonProd___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonProd(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Name_fromJson_x3f(lean_object*);
static const lean_closure_object l_Lean_instFromJsonName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_fromJson_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonName___closed__0 = (const lean_object*)&l_Lean_instFromJsonName___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instFromJsonName = (const lean_object*)&l_Lean_instFromJsonName___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instToJsonName___lam__0(lean_object*);
static const lean_closure_object l_Lean_instToJsonName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonName___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonName___closed__0 = (const lean_object*)&l_Lean_instToJsonName___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonName = (const lean_object*)&l_Lean_instToJsonName___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_NameMap_fromJson_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "expected a `NameMap`, got '"};
static const lean_object* l_Lean_NameMap_fromJson_x3f___redArg___closed__0 = (const lean_object*)&l_Lean_NameMap_fromJson_x3f___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonNameMap___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonNameMap(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_NameMap_toJson___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_NameMap_toJson___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_NameMap_toJson___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_NameMap_toJson___redArg___closed__0 = (const lean_object*)&l_Lean_NameMap_toJson___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToJsonNameMap___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToJsonNameMap(lean_object*, lean_object*);
static const lean_string_object l_Lean_bignumFromJson_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "expected a string-encoded number, got '"};
static const lean_object* l_Lean_bignumFromJson_x3f___closed__0 = (const lean_object*)&l_Lean_bignumFromJson_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_bignumFromJson_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_bignumToJson(lean_object*);
static lean_once_cell_t l_USize_fromJson_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_USize_fromJson_x3f___closed__0;
static const lean_string_object l_USize_fromJson_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "value '"};
static const lean_object* l_USize_fromJson_x3f___closed__1 = (const lean_object*)&l_USize_fromJson_x3f___closed__1_value;
static const lean_string_object l_USize_fromJson_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "' is too large for `USize`"};
static const lean_object* l_USize_fromJson_x3f___closed__2 = (const lean_object*)&l_USize_fromJson_x3f___closed__2_value;
LEAN_EXPORT lean_object* l_USize_fromJson_x3f(lean_object*);
static const lean_closure_object l_Lean_instFromJsonUSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_USize_fromJson_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonUSize___closed__0 = (const lean_object*)&l_Lean_instFromJsonUSize___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instFromJsonUSize = (const lean_object*)&l_Lean_instFromJsonUSize___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instToJsonUSize___lam__0(size_t);
LEAN_EXPORT lean_object* l_Lean_instToJsonUSize___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_instToJsonUSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonUSize___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonUSize___closed__0 = (const lean_object*)&l_Lean_instToJsonUSize___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonUSize = (const lean_object*)&l_Lean_instToJsonUSize___closed__0_value;
static lean_once_cell_t l_UInt64_fromJson_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_UInt64_fromJson_x3f___closed__0;
static const lean_string_object l_UInt64_fromJson_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "' is too large for `UInt64`"};
static const lean_object* l_UInt64_fromJson_x3f___closed__1 = (const lean_object*)&l_UInt64_fromJson_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_UInt64_fromJson_x3f(lean_object*);
static const lean_closure_object l_Lean_instFromJsonUInt64___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_fromJson_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonUInt64___closed__0 = (const lean_object*)&l_Lean_instFromJsonUInt64___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instFromJsonUInt64 = (const lean_object*)&l_Lean_instFromJsonUInt64___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instToJsonUInt64___lam__0(uint64_t);
LEAN_EXPORT lean_object* l_Lean_instToJsonUInt64___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_instToJsonUInt64___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonUInt64___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonUInt64___closed__0 = (const lean_object*)&l_Lean_instToJsonUInt64___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonUInt64 = (const lean_object*)&l_Lean_instToJsonUInt64___closed__0_value;
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
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_setObjValAs_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_setObjValAs_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getTag_x3f(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Json_parseTagged(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_parseTagged___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_parseCtorFields_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_parseCtorFields_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_parseCtorFields(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_parseCtorFields___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonJson___lam__0(lean_object* v_a_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2_, 0, v_a_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonJsonNumber___lam__0(lean_object* v_n_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_10_, 0, v_n_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonEmpty___lam__0(lean_object* v_j_15_){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_16_ = ((lean_object*)(l_Lean_instFromJsonEmpty___lam__0___closed__0));
v___x_17_ = lean_unsigned_to_nat(80u);
v___x_18_ = l_Lean_Json_pretty(v_j_15_, v___x_17_);
v___x_19_ = lean_string_append(v___x_16_, v___x_18_);
lean_dec_ref(v___x_18_);
v___x_20_ = ((lean_object*)(l_Lean_instFromJsonEmpty___lam__0___closed__1));
v___x_21_ = lean_string_append(v___x_19_, v___x_20_);
v___x_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_22_, 0, v___x_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonEmpty___lam__0(uint8_t v_a_25_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonEmpty___lam__0___boxed(lean_object* v_a_26_){
_start:
{
uint8_t v_a_6__boxed_27_; lean_object* v_res_28_; 
v_a_6__boxed_27_ = lean_unbox(v_a_26_);
v_res_28_ = l_Lean_instToJsonEmpty___lam__0(v_a_6__boxed_27_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBool___lam__0(uint8_t v_b_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_34_, 0, v_b_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBool___lam__0___boxed(lean_object* v_b_35_){
_start:
{
uint8_t v_b_boxed_36_; lean_object* v_res_37_; 
v_b_boxed_36_ = lean_unbox(v_b_35_);
v_res_37_ = l_Lean_instToJsonBool___lam__0(v_b_boxed_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonNat___lam__0(lean_object* v_n_42_){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_43_ = l_Lean_JsonNumber_fromNat(v_n_42_);
v___x_44_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_44_, 0, v___x_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonInt___lam__0(lean_object* v_n_49_){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_50_ = l_Lean_JsonNumber_fromInt(v_n_49_);
v___x_51_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_51_, 0, v___x_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonString___lam__0(lean_object* v_s_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_57_, 0, v_s_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonSlice___lam__0(lean_object* v_s_67_){
_start:
{
lean_object* v_str_68_; lean_object* v_startInclusive_69_; lean_object* v_endExclusive_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v_str_68_ = lean_ctor_get(v_s_67_, 0);
v_startInclusive_69_ = lean_ctor_get(v_s_67_, 1);
v_endExclusive_70_ = lean_ctor_get(v_s_67_, 2);
v___x_71_ = lean_string_utf8_extract(v_str_68_, v_startInclusive_69_, v_endExclusive_70_);
v___x_72_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_72_, 0, v___x_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonSlice___lam__0___boxed(lean_object* v_s_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l_Lean_instToJsonSlice___lam__0(v_s_73_);
lean_dec_ref(v_s_73_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonFilePath___lam__0(lean_object* v_j_77_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = l_Lean_Json_getStr_x3f(v_j_77_);
if (lean_obj_tag(v___x_78_) == 0)
{
lean_object* v_a_79_; lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_86_; 
v_a_79_ = lean_ctor_get(v___x_78_, 0);
v_isSharedCheck_86_ = !lean_is_exclusive(v___x_78_);
if (v_isSharedCheck_86_ == 0)
{
v___x_81_ = v___x_78_;
v_isShared_82_ = v_isSharedCheck_86_;
goto v_resetjp_80_;
}
else
{
lean_inc(v_a_79_);
lean_dec(v___x_78_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_86_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v___x_84_; 
if (v_isShared_82_ == 0)
{
v___x_84_ = v___x_81_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v_a_79_);
v___x_84_ = v_reuseFailAlloc_85_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
return v___x_84_;
}
}
}
else
{
lean_object* v_a_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_94_; 
v_a_87_ = lean_ctor_get(v___x_78_, 0);
v_isSharedCheck_94_ = !lean_is_exclusive(v___x_78_);
if (v_isSharedCheck_94_ == 0)
{
v___x_89_ = v___x_78_;
v_isShared_90_ = v_isSharedCheck_94_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_a_87_);
lean_dec(v___x_78_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_94_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_92_; 
if (v_isShared_90_ == 0)
{
v___x_92_ = v___x_89_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v_a_87_);
v___x_92_ = v_reuseFailAlloc_93_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
return v___x_92_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonFilePath___lam__0(lean_object* v_p_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_98_, 0, v_p_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___redArg(lean_object* v_inst_122_, lean_object* v_x_123_){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = ((lean_object*)(l_Array_fromJson_x3f___redArg___closed__9));
if (lean_obj_tag(v_x_123_) == 4)
{
lean_object* v_elems_125_; size_t v_sz_126_; size_t v___x_127_; lean_object* v___x_128_; 
v_elems_125_ = lean_ctor_get(v_x_123_, 0);
lean_inc_ref(v_elems_125_);
lean_dec_ref(v_x_123_);
v_sz_126_ = lean_array_size(v_elems_125_);
v___x_127_ = ((size_t)0ULL);
v___x_128_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_124_, v_inst_122_, v_sz_126_, v___x_127_, v_elems_125_);
return v___x_128_;
}
else
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
lean_dec_ref(v_inst_122_);
v___x_129_ = ((lean_object*)(l_Array_fromJson_x3f___redArg___closed__10));
v___x_130_ = lean_unsigned_to_nat(80u);
v___x_131_ = l_Lean_Json_pretty(v_x_123_, v___x_130_);
v___x_132_ = lean_string_append(v___x_129_, v___x_131_);
lean_dec_ref(v___x_131_);
v___x_133_ = ((lean_object*)(l_Array_fromJson_x3f___redArg___closed__11));
v___x_134_ = lean_string_append(v___x_132_, v___x_133_);
v___x_135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
return v___x_135_;
}
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f(lean_object* v_00_u03b1_136_, lean_object* v_inst_137_, lean_object* v_x_138_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = l_Array_fromJson_x3f___redArg(v_inst_137_, v_x_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonArray___redArg(lean_object* v_inst_140_){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = lean_alloc_closure((void*)(l_Array_fromJson_x3f), 3, 2);
lean_closure_set(v___x_141_, 0, lean_box(0));
lean_closure_set(v___x_141_, 1, v_inst_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonArray(lean_object* v_00_u03b1_142_, lean_object* v_inst_143_){
_start:
{
lean_object* v___x_144_; 
v___x_144_ = lean_alloc_closure((void*)(l_Array_fromJson_x3f), 3, 2);
lean_closure_set(v___x_144_, 0, lean_box(0));
lean_closure_set(v___x_144_, 1, v_inst_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___redArg___lam__0(lean_object* v_inst_145_, lean_object* v_x_146_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = lean_apply_1(v_inst_145_, v_x_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___redArg(lean_object* v_inst_167_, lean_object* v_a_168_){
_start:
{
lean_object* v___f_169_; lean_object* v___x_170_; size_t v_sz_171_; size_t v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___f_169_ = lean_alloc_closure((void*)(l_Array_toJson___redArg___lam__0), 2, 1);
lean_closure_set(v___f_169_, 0, v_inst_167_);
v___x_170_ = ((lean_object*)(l_Array_toJson___redArg___closed__9));
v_sz_171_ = lean_array_size(v_a_168_);
v___x_172_ = ((size_t)0ULL);
v___x_173_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_170_, v___f_169_, v_sz_171_, v___x_172_, v_a_168_);
v___x_174_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_174_, 0, v___x_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson(lean_object* v_00_u03b1_175_, lean_object* v_inst_176_, lean_object* v_a_177_){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = l_Array_toJson___redArg(v_inst_176_, v_a_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonArray___redArg(lean_object* v_inst_179_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = lean_alloc_closure((void*)(l_Array_toJson), 3, 2);
lean_closure_set(v___x_180_, 0, lean_box(0));
lean_closure_set(v___x_180_, 1, v_inst_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonArray(lean_object* v_00_u03b1_181_, lean_object* v_inst_182_){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = lean_alloc_closure((void*)(l_Array_toJson), 3, 2);
lean_closure_set(v___x_183_, 0, lean_box(0));
lean_closure_set(v___x_183_, 1, v_inst_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_List_fromJson_x3f___redArg(lean_object* v_inst_184_, lean_object* v_j_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l_Array_fromJson_x3f___redArg(v_inst_184_, v_j_185_);
if (lean_obj_tag(v___x_186_) == 0)
{
lean_object* v_a_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_194_; 
v_a_187_ = lean_ctor_get(v___x_186_, 0);
v_isSharedCheck_194_ = !lean_is_exclusive(v___x_186_);
if (v_isSharedCheck_194_ == 0)
{
v___x_189_ = v___x_186_;
v_isShared_190_ = v_isSharedCheck_194_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_a_187_);
lean_dec(v___x_186_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_194_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___x_192_; 
if (v_isShared_190_ == 0)
{
v___x_192_ = v___x_189_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v_a_187_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
return v___x_192_;
}
}
}
else
{
lean_object* v_a_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_203_; 
v_a_195_ = lean_ctor_get(v___x_186_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_186_);
if (v_isSharedCheck_203_ == 0)
{
v___x_197_ = v___x_186_;
v_isShared_198_ = v_isSharedCheck_203_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_a_195_);
lean_dec(v___x_186_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_203_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_199_; lean_object* v___x_201_; 
v___x_199_ = lean_array_to_list(v_a_195_);
if (v_isShared_198_ == 0)
{
lean_ctor_set(v___x_197_, 0, v___x_199_);
v___x_201_ = v___x_197_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v___x_199_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_fromJson_x3f(lean_object* v_00_u03b1_204_, lean_object* v_inst_205_, lean_object* v_j_206_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = l_List_fromJson_x3f___redArg(v_inst_205_, v_j_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonList___redArg(lean_object* v_inst_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = lean_alloc_closure((void*)(l_List_fromJson_x3f), 3, 2);
lean_closure_set(v___x_209_, 0, lean_box(0));
lean_closure_set(v___x_209_, 1, v_inst_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonList(lean_object* v_00_u03b1_210_, lean_object* v_inst_211_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = lean_alloc_closure((void*)(l_List_fromJson_x3f), 3, 2);
lean_closure_set(v___x_212_, 0, lean_box(0));
lean_closure_set(v___x_212_, 1, v_inst_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_List_toJson___redArg(lean_object* v_inst_213_, lean_object* v_a_214_){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_215_ = lean_array_mk(v_a_214_);
v___x_216_ = l_Array_toJson___redArg(v_inst_213_, v___x_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_List_toJson(lean_object* v_00_u03b1_217_, lean_object* v_inst_218_, lean_object* v_a_219_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = l_List_toJson___redArg(v_inst_218_, v_a_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonList___redArg(lean_object* v_inst_221_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = lean_alloc_closure((void*)(l_List_toJson), 3, 2);
lean_closure_set(v___x_222_, 0, lean_box(0));
lean_closure_set(v___x_222_, 1, v_inst_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonList(lean_object* v_00_u03b1_223_, lean_object* v_inst_224_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = lean_alloc_closure((void*)(l_List_toJson), 3, 2);
lean_closure_set(v___x_225_, 0, lean_box(0));
lean_closure_set(v___x_225_, 1, v_inst_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___redArg(lean_object* v_inst_228_, lean_object* v_x_229_){
_start:
{
if (lean_obj_tag(v_x_229_) == 0)
{
lean_object* v___x_230_; 
lean_dec_ref(v_inst_228_);
v___x_230_ = ((lean_object*)(l_Option_fromJson_x3f___redArg___closed__0));
return v___x_230_;
}
else
{
lean_object* v___x_231_; 
v___x_231_ = lean_apply_1(v_inst_228_, v_x_229_);
if (lean_obj_tag(v___x_231_) == 0)
{
lean_object* v_a_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_239_; 
v_a_232_ = lean_ctor_get(v___x_231_, 0);
v_isSharedCheck_239_ = !lean_is_exclusive(v___x_231_);
if (v_isSharedCheck_239_ == 0)
{
v___x_234_ = v___x_231_;
v_isShared_235_ = v_isSharedCheck_239_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_a_232_);
lean_dec(v___x_231_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_239_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v___x_237_; 
if (v_isShared_235_ == 0)
{
v___x_237_ = v___x_234_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v_a_232_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
}
else
{
lean_object* v_a_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_248_; 
v_a_240_ = lean_ctor_get(v___x_231_, 0);
v_isSharedCheck_248_ = !lean_is_exclusive(v___x_231_);
if (v_isSharedCheck_248_ == 0)
{
v___x_242_ = v___x_231_;
v_isShared_243_ = v_isSharedCheck_248_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_a_240_);
lean_dec(v___x_231_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_248_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_244_; lean_object* v___x_246_; 
v___x_244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_244_, 0, v_a_240_);
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 0, v___x_244_);
v___x_246_ = v___x_242_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v___x_244_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
return v___x_246_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f(lean_object* v_00_u03b1_249_, lean_object* v_inst_250_, lean_object* v_x_251_){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = l_Option_fromJson_x3f___redArg(v_inst_250_, v_x_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonOption___redArg(lean_object* v_inst_253_){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = lean_alloc_closure((void*)(l_Option_fromJson_x3f), 3, 2);
lean_closure_set(v___x_254_, 0, lean_box(0));
lean_closure_set(v___x_254_, 1, v_inst_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonOption(lean_object* v_00_u03b1_255_, lean_object* v_inst_256_){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = lean_alloc_closure((void*)(l_Option_fromJson_x3f), 3, 2);
lean_closure_set(v___x_257_, 0, lean_box(0));
lean_closure_set(v___x_257_, 1, v_inst_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Option_toJson___redArg(lean_object* v_inst_258_, lean_object* v_x_259_){
_start:
{
if (lean_obj_tag(v_x_259_) == 0)
{
lean_object* v___x_260_; 
lean_dec_ref(v_inst_258_);
v___x_260_ = lean_box(0);
return v___x_260_;
}
else
{
lean_object* v_val_261_; lean_object* v___x_262_; 
v_val_261_ = lean_ctor_get(v_x_259_, 0);
lean_inc(v_val_261_);
lean_dec_ref(v_x_259_);
v___x_262_ = lean_apply_1(v_inst_258_, v_val_261_);
return v___x_262_;
}
}
}
LEAN_EXPORT lean_object* l_Option_toJson(lean_object* v_00_u03b1_263_, lean_object* v_inst_264_, lean_object* v_x_265_){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = l_Option_toJson___redArg(v_inst_264_, v_x_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonOption___redArg(lean_object* v_inst_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = lean_alloc_closure((void*)(l_Option_toJson), 3, 2);
lean_closure_set(v___x_268_, 0, lean_box(0));
lean_closure_set(v___x_268_, 1, v_inst_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonOption(lean_object* v_00_u03b1_269_, lean_object* v_inst_270_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = lean_alloc_closure((void*)(l_Option_toJson), 3, 2);
lean_closure_set(v___x_271_, 0, lean_box(0));
lean_closure_set(v___x_271_, 1, v_inst_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Prod_fromJson_x3f___redArg(lean_object* v_inst_273_, lean_object* v_inst_274_, lean_object* v_x_275_){
_start:
{
lean_object* v_j_277_; 
if (lean_obj_tag(v_x_275_) == 4)
{
lean_object* v_elems_285_; lean_object* v___x_286_; lean_object* v___x_287_; uint8_t v___x_288_; 
v_elems_285_ = lean_ctor_get(v_x_275_, 0);
v___x_286_ = lean_array_get_size(v_elems_285_);
v___x_287_ = lean_unsigned_to_nat(2u);
v___x_288_ = lean_nat_dec_eq(v___x_286_, v___x_287_);
if (v___x_288_ == 0)
{
lean_dec_ref(v_inst_274_);
lean_dec_ref(v_inst_273_);
v_j_277_ = v_x_275_;
goto v___jp_276_;
}
else
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
lean_inc_ref(v_elems_285_);
lean_dec_ref(v_x_275_);
v___x_289_ = lean_unsigned_to_nat(0u);
v___x_290_ = lean_array_fget_borrowed(v_elems_285_, v___x_289_);
lean_inc(v___x_290_);
v___x_291_ = lean_apply_1(v_inst_273_, v___x_290_);
if (lean_obj_tag(v___x_291_) == 0)
{
lean_object* v_a_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_299_; 
lean_dec_ref(v_elems_285_);
lean_dec_ref(v_inst_274_);
v_a_292_ = lean_ctor_get(v___x_291_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v___x_291_);
if (v_isSharedCheck_299_ == 0)
{
v___x_294_ = v___x_291_;
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_a_292_);
lean_dec(v___x_291_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_297_; 
if (v_isShared_295_ == 0)
{
v___x_297_ = v___x_294_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_a_292_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
else
{
lean_object* v_a_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v_a_300_ = lean_ctor_get(v___x_291_, 0);
lean_inc(v_a_300_);
lean_dec_ref(v___x_291_);
v___x_301_ = lean_unsigned_to_nat(1u);
v___x_302_ = lean_array_fget(v_elems_285_, v___x_301_);
lean_dec_ref(v_elems_285_);
v___x_303_ = lean_apply_1(v_inst_274_, v___x_302_);
if (lean_obj_tag(v___x_303_) == 0)
{
lean_object* v_a_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_311_; 
lean_dec(v_a_300_);
v_a_304_ = lean_ctor_get(v___x_303_, 0);
v_isSharedCheck_311_ = !lean_is_exclusive(v___x_303_);
if (v_isSharedCheck_311_ == 0)
{
v___x_306_ = v___x_303_;
v_isShared_307_ = v_isSharedCheck_311_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_a_304_);
lean_dec(v___x_303_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_311_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___x_309_; 
if (v_isShared_307_ == 0)
{
v___x_309_ = v___x_306_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v_a_304_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
}
}
}
else
{
lean_object* v_a_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_320_; 
v_a_312_ = lean_ctor_get(v___x_303_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_303_);
if (v_isSharedCheck_320_ == 0)
{
v___x_314_ = v___x_303_;
v_isShared_315_ = v_isSharedCheck_320_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_a_312_);
lean_dec(v___x_303_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_320_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_316_; lean_object* v___x_318_; 
v___x_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_316_, 0, v_a_300_);
lean_ctor_set(v___x_316_, 1, v_a_312_);
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 0, v___x_316_);
v___x_318_ = v___x_314_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v___x_316_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_inst_274_);
lean_dec_ref(v_inst_273_);
v_j_277_ = v_x_275_;
goto v___jp_276_;
}
v___jp_276_:
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_278_ = ((lean_object*)(l_Prod_fromJson_x3f___redArg___closed__0));
v___x_279_ = lean_unsigned_to_nat(80u);
v___x_280_ = l_Lean_Json_pretty(v_j_277_, v___x_279_);
v___x_281_ = lean_string_append(v___x_278_, v___x_280_);
lean_dec_ref(v___x_280_);
v___x_282_ = ((lean_object*)(l_Array_fromJson_x3f___redArg___closed__11));
v___x_283_ = lean_string_append(v___x_281_, v___x_282_);
v___x_284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
return v___x_284_;
}
}
}
LEAN_EXPORT lean_object* l_Prod_fromJson_x3f(lean_object* v_00_u03b1_321_, lean_object* v_00_u03b2_322_, lean_object* v_inst_323_, lean_object* v_inst_324_, lean_object* v_x_325_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l_Prod_fromJson_x3f___redArg(v_inst_323_, v_inst_324_, v_x_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonProd___redArg(lean_object* v_inst_327_, lean_object* v_inst_328_){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = lean_alloc_closure((void*)(l_Prod_fromJson_x3f), 5, 4);
lean_closure_set(v___x_329_, 0, lean_box(0));
lean_closure_set(v___x_329_, 1, lean_box(0));
lean_closure_set(v___x_329_, 2, v_inst_327_);
lean_closure_set(v___x_329_, 3, v_inst_328_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonProd(lean_object* v_00_u03b1_330_, lean_object* v_00_u03b2_331_, lean_object* v_inst_332_, lean_object* v_inst_333_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = lean_alloc_closure((void*)(l_Prod_fromJson_x3f), 5, 4);
lean_closure_set(v___x_334_, 0, lean_box(0));
lean_closure_set(v___x_334_, 1, lean_box(0));
lean_closure_set(v___x_334_, 2, v_inst_332_);
lean_closure_set(v___x_334_, 3, v_inst_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Prod_toJson___redArg(lean_object* v_inst_335_, lean_object* v_inst_336_, lean_object* v_x_337_){
_start:
{
lean_object* v_fst_338_; lean_object* v_snd_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v_fst_338_ = lean_ctor_get(v_x_337_, 0);
lean_inc(v_fst_338_);
v_snd_339_ = lean_ctor_get(v_x_337_, 1);
lean_inc(v_snd_339_);
lean_dec_ref(v_x_337_);
v___x_340_ = lean_apply_1(v_inst_335_, v_fst_338_);
v___x_341_ = lean_apply_1(v_inst_336_, v_snd_339_);
v___x_342_ = lean_unsigned_to_nat(2u);
v___x_343_ = lean_mk_empty_array_with_capacity(v___x_342_);
v___x_344_ = lean_array_push(v___x_343_, v___x_340_);
v___x_345_ = lean_array_push(v___x_344_, v___x_341_);
v___x_346_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Prod_toJson(lean_object* v_00_u03b1_347_, lean_object* v_00_u03b2_348_, lean_object* v_inst_349_, lean_object* v_inst_350_, lean_object* v_x_351_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = l_Prod_toJson___redArg(v_inst_349_, v_inst_350_, v_x_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonProd___redArg(lean_object* v_inst_353_, lean_object* v_inst_354_){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = lean_alloc_closure((void*)(l_Prod_toJson), 5, 4);
lean_closure_set(v___x_355_, 0, lean_box(0));
lean_closure_set(v___x_355_, 1, lean_box(0));
lean_closure_set(v___x_355_, 2, v_inst_353_);
lean_closure_set(v___x_355_, 3, v_inst_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonProd(lean_object* v_00_u03b1_356_, lean_object* v_00_u03b2_357_, lean_object* v_inst_358_, lean_object* v_inst_359_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = lean_alloc_closure((void*)(l_Prod_toJson), 5, 4);
lean_closure_set(v___x_360_, 0, lean_box(0));
lean_closure_set(v___x_360_, 1, lean_box(0));
lean_closure_set(v___x_360_, 2, v_inst_358_);
lean_closure_set(v___x_360_, 3, v_inst_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_fromJson_x3f(lean_object* v_j_365_){
_start:
{
lean_object* v___x_366_; 
lean_inc(v_j_365_);
v___x_366_ = l_Lean_Json_getStr_x3f(v_j_365_);
if (lean_obj_tag(v___x_366_) == 0)
{
lean_object* v_a_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_374_; 
lean_dec(v_j_365_);
v_a_367_ = lean_ctor_get(v___x_366_, 0);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_374_ == 0)
{
v___x_369_ = v___x_366_;
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_a_367_);
lean_dec(v___x_366_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_372_; 
if (v_isShared_370_ == 0)
{
v___x_372_ = v___x_369_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_a_367_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
else
{
lean_object* v_a_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_396_; 
v_a_375_ = lean_ctor_get(v___x_366_, 0);
v_isSharedCheck_396_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_396_ == 0)
{
v___x_377_ = v___x_366_;
v_isShared_378_ = v_isSharedCheck_396_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_a_375_);
lean_dec(v___x_366_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_396_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_379_; uint8_t v___x_380_; 
v___x_379_ = ((lean_object*)(l_Lean_Name_fromJson_x3f___closed__0));
v___x_380_ = lean_string_dec_eq(v_a_375_, v___x_379_);
if (v___x_380_ == 0)
{
lean_object* v___x_381_; uint8_t v___x_382_; 
v___x_381_ = l_String_toName(v_a_375_);
v___x_382_ = l_Lean_Name_isAnonymous(v___x_381_);
if (v___x_382_ == 0)
{
lean_object* v___x_384_; 
lean_dec(v_j_365_);
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 0, v___x_381_);
v___x_384_ = v___x_377_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v___x_381_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
return v___x_384_;
}
}
else
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_393_; 
lean_dec(v___x_381_);
v___x_386_ = ((lean_object*)(l_Lean_Name_fromJson_x3f___closed__1));
v___x_387_ = lean_unsigned_to_nat(80u);
v___x_388_ = l_Lean_Json_pretty(v_j_365_, v___x_387_);
v___x_389_ = lean_string_append(v___x_386_, v___x_388_);
lean_dec_ref(v___x_388_);
v___x_390_ = ((lean_object*)(l_Array_fromJson_x3f___redArg___closed__11));
v___x_391_ = lean_string_append(v___x_389_, v___x_390_);
if (v_isShared_378_ == 0)
{
lean_ctor_set_tag(v___x_377_, 0);
lean_ctor_set(v___x_377_, 0, v___x_391_);
v___x_393_ = v___x_377_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v___x_391_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
}
else
{
lean_object* v___x_395_; 
lean_del_object(v___x_377_);
lean_dec(v_a_375_);
lean_dec(v_j_365_);
v___x_395_ = ((lean_object*)(l_Lean_Name_fromJson_x3f___closed__2));
return v___x_395_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonName___lam__0(lean_object* v_n_399_){
_start:
{
uint8_t v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_400_ = 1;
v___x_401_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_399_, v___x_400_);
v___x_402_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_402_, 0, v___x_401_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f___redArg___lam__0(lean_object* v_inst_405_, lean_object* v_m_406_, lean_object* v_k_407_, lean_object* v_v_408_){
_start:
{
lean_object* v___x_409_; uint8_t v___x_410_; 
v___x_409_ = ((lean_object*)(l_Lean_Name_fromJson_x3f___closed__0));
v___x_410_ = lean_string_dec_eq(v_k_407_, v___x_409_);
if (v___x_410_ == 0)
{
lean_object* v_n_411_; uint8_t v___x_412_; 
lean_inc_ref(v_k_407_);
v_n_411_ = l_String_toName(v_k_407_);
v___x_412_ = l_Lean_Name_isAnonymous(v_n_411_);
if (v___x_412_ == 0)
{
lean_object* v___x_413_; 
lean_dec_ref(v_k_407_);
v___x_413_ = lean_apply_1(v_inst_405_, v_v_408_);
if (lean_obj_tag(v___x_413_) == 0)
{
lean_object* v_a_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_421_; 
lean_dec(v_n_411_);
lean_dec(v_m_406_);
v_a_414_ = lean_ctor_get(v___x_413_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_421_ == 0)
{
v___x_416_ = v___x_413_;
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_a_414_);
lean_dec(v___x_413_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_419_; 
if (v_isShared_417_ == 0)
{
v___x_419_ = v___x_416_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_a_414_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
else
{
lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_430_; 
v_a_422_ = lean_ctor_get(v___x_413_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_430_ == 0)
{
v___x_424_ = v___x_413_;
v_isShared_425_ = v_isSharedCheck_430_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_413_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_430_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_426_; lean_object* v___x_428_; 
v___x_426_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_n_411_, v_a_422_, v_m_406_);
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 0, v___x_426_);
v___x_428_ = v___x_424_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v___x_426_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
}
else
{
lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
lean_dec(v_n_411_);
lean_dec(v_v_408_);
lean_dec(v_m_406_);
lean_dec_ref(v_inst_405_);
v___x_431_ = ((lean_object*)(l_Lean_Name_fromJson_x3f___closed__1));
v___x_432_ = lean_string_append(v___x_431_, v_k_407_);
lean_dec_ref(v_k_407_);
v___x_433_ = ((lean_object*)(l_Array_fromJson_x3f___redArg___closed__11));
v___x_434_ = lean_string_append(v___x_432_, v___x_433_);
v___x_435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_435_, 0, v___x_434_);
return v___x_435_;
}
}
else
{
lean_object* v___x_436_; 
lean_dec_ref(v_k_407_);
v___x_436_ = lean_apply_1(v_inst_405_, v_v_408_);
if (lean_obj_tag(v___x_436_) == 0)
{
lean_object* v_a_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_444_; 
lean_dec(v_m_406_);
v_a_437_ = lean_ctor_get(v___x_436_, 0);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_436_);
if (v_isSharedCheck_444_ == 0)
{
v___x_439_ = v___x_436_;
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_a_437_);
lean_dec(v___x_436_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_442_; 
if (v_isShared_440_ == 0)
{
v___x_442_ = v___x_439_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_a_437_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
else
{
lean_object* v_a_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_454_; 
v_a_445_ = lean_ctor_get(v___x_436_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_436_);
if (v_isSharedCheck_454_ == 0)
{
v___x_447_ = v___x_436_;
v_isShared_448_ = v_isSharedCheck_454_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_a_445_);
lean_dec(v___x_436_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_454_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_452_; 
v___x_449_ = lean_box(0);
v___x_450_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_449_, v_a_445_, v_m_406_);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 0, v___x_450_);
v___x_452_ = v___x_447_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v___x_450_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f___redArg(lean_object* v_inst_456_, lean_object* v_x_457_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = ((lean_object*)(l_Array_fromJson_x3f___redArg___closed__9));
if (lean_obj_tag(v_x_457_) == 5)
{
lean_object* v_kvPairs_459_; lean_object* v___f_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v_kvPairs_459_ = lean_ctor_get(v_x_457_, 0);
lean_inc(v_kvPairs_459_);
lean_dec_ref(v_x_457_);
v___f_460_ = lean_alloc_closure((void*)(l_Lean_NameMap_fromJson_x3f___redArg___lam__0), 4, 1);
lean_closure_set(v___f_460_, 0, v_inst_456_);
v___x_461_ = lean_box(1);
v___x_462_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v___x_458_, v___f_460_, v___x_461_, v_kvPairs_459_);
return v___x_462_;
}
else
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
lean_dec_ref(v_inst_456_);
v___x_463_ = ((lean_object*)(l_Lean_NameMap_fromJson_x3f___redArg___closed__0));
v___x_464_ = lean_unsigned_to_nat(80u);
v___x_465_ = l_Lean_Json_pretty(v_x_457_, v___x_464_);
v___x_466_ = lean_string_append(v___x_463_, v___x_465_);
lean_dec_ref(v___x_465_);
v___x_467_ = ((lean_object*)(l_Array_fromJson_x3f___redArg___closed__11));
v___x_468_ = lean_string_append(v___x_466_, v___x_467_);
v___x_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_469_, 0, v___x_468_);
return v___x_469_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f(lean_object* v_00_u03b1_470_, lean_object* v_inst_471_, lean_object* v_x_472_){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = l_Lean_NameMap_fromJson_x3f___redArg(v_inst_471_, v_x_472_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonNameMap___redArg(lean_object* v_inst_474_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = lean_alloc_closure((void*)(l_Lean_NameMap_fromJson_x3f), 3, 2);
lean_closure_set(v___x_475_, 0, lean_box(0));
lean_closure_set(v___x_475_, 1, v_inst_474_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonNameMap(lean_object* v_00_u03b1_476_, lean_object* v_inst_477_){
_start:
{
lean_object* v___x_478_; 
v___x_478_ = lean_alloc_closure((void*)(l_Lean_NameMap_fromJson_x3f), 3, 2);
lean_closure_set(v___x_478_, 0, lean_box(0));
lean_closure_set(v___x_478_, 1, v_inst_477_);
return v___x_478_;
}
}
LEAN_EXPORT uint8_t l_Lean_NameMap_toJson___redArg___lam__0(lean_object* v_x_479_, lean_object* v_y_480_){
_start:
{
uint8_t v___x_481_; 
v___x_481_ = lean_string_dec_lt(v_x_479_, v_y_480_);
if (v___x_481_ == 0)
{
uint8_t v___x_482_; 
v___x_482_ = lean_string_dec_eq(v_x_479_, v_y_480_);
if (v___x_482_ == 0)
{
uint8_t v___x_483_; 
v___x_483_ = 2;
return v___x_483_;
}
else
{
uint8_t v___x_484_; 
v___x_484_ = 1;
return v___x_484_;
}
}
else
{
uint8_t v___x_485_; 
v___x_485_ = 0;
return v___x_485_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___redArg___lam__0___boxed(lean_object* v_x_486_, lean_object* v_y_487_){
_start:
{
uint8_t v_res_488_; lean_object* v_r_489_; 
v_res_488_ = l_Lean_NameMap_toJson___redArg___lam__0(v_x_486_, v_y_487_);
lean_dec_ref(v_y_487_);
lean_dec_ref(v_x_486_);
v_r_489_ = lean_box(v_res_488_);
return v_r_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___redArg___lam__1(lean_object* v_inst_490_, lean_object* v___f_491_, lean_object* v_n_492_, lean_object* v_k_493_, lean_object* v_v_494_){
_start:
{
uint8_t v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_495_ = 1;
v___x_496_ = l_Lean_Name_toString(v_k_493_, v___x_495_);
v___x_497_ = lean_apply_1(v_inst_490_, v_v_494_);
v___x_498_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v___f_491_, v___x_496_, v___x_497_, v_n_492_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___redArg(lean_object* v_inst_500_, lean_object* v_m_501_){
_start:
{
lean_object* v___f_502_; lean_object* v___f_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v___f_502_ = ((lean_object*)(l_Lean_NameMap_toJson___redArg___closed__0));
v___f_503_ = lean_alloc_closure((void*)(l_Lean_NameMap_toJson___redArg___lam__1), 5, 2);
lean_closure_set(v___f_503_, 0, v_inst_500_);
lean_closure_set(v___f_503_, 1, v___f_502_);
v___x_504_ = lean_box(1);
v___x_505_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_503_, v___x_504_, v_m_501_);
v___x_506_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_506_, 0, v___x_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson(lean_object* v_00_u03b1_507_, lean_object* v_inst_508_, lean_object* v_m_509_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = l_Lean_NameMap_toJson___redArg(v_inst_508_, v_m_509_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonNameMap___redArg(lean_object* v_inst_511_){
_start:
{
lean_object* v___x_512_; 
v___x_512_ = lean_alloc_closure((void*)(l_Lean_NameMap_toJson), 3, 2);
lean_closure_set(v___x_512_, 0, lean_box(0));
lean_closure_set(v___x_512_, 1, v_inst_511_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonNameMap(lean_object* v_00_u03b1_513_, lean_object* v_inst_514_){
_start:
{
lean_object* v___x_515_; 
v___x_515_ = lean_alloc_closure((void*)(l_Lean_NameMap_toJson), 3, 2);
lean_closure_set(v___x_515_, 0, lean_box(0));
lean_closure_set(v___x_515_, 1, v_inst_514_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_bignumFromJson_x3f(lean_object* v_j_517_){
_start:
{
lean_object* v___x_518_; 
lean_inc(v_j_517_);
v___x_518_ = l_Lean_Json_getStr_x3f(v_j_517_);
if (lean_obj_tag(v___x_518_) == 0)
{
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_526_; 
lean_dec(v_j_517_);
v_a_519_ = lean_ctor_get(v___x_518_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_526_ == 0)
{
v___x_521_ = v___x_518_;
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v___x_518_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_524_; 
if (v_isShared_522_ == 0)
{
v___x_524_ = v___x_521_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_a_519_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
else
{
lean_object* v_a_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_545_; 
v_a_527_ = lean_ctor_get(v___x_518_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_545_ == 0)
{
v___x_529_ = v___x_518_;
v_isShared_530_ = v_isSharedCheck_545_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_a_527_);
lean_dec(v___x_518_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_545_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_531_; 
v___x_531_ = l_Lean_Syntax_decodeNatLitVal_x3f(v_a_527_);
lean_dec(v_a_527_);
if (lean_obj_tag(v___x_531_) == 1)
{
lean_object* v_val_532_; lean_object* v___x_534_; 
lean_dec(v_j_517_);
v_val_532_ = lean_ctor_get(v___x_531_, 0);
lean_inc(v_val_532_);
lean_dec_ref(v___x_531_);
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 0, v_val_532_);
v___x_534_ = v___x_529_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_val_532_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
else
{
lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_543_; 
lean_dec(v___x_531_);
v___x_536_ = ((lean_object*)(l_Lean_bignumFromJson_x3f___closed__0));
v___x_537_ = lean_unsigned_to_nat(80u);
v___x_538_ = l_Lean_Json_pretty(v_j_517_, v___x_537_);
v___x_539_ = lean_string_append(v___x_536_, v___x_538_);
lean_dec_ref(v___x_538_);
v___x_540_ = ((lean_object*)(l_Array_fromJson_x3f___redArg___closed__11));
v___x_541_ = lean_string_append(v___x_539_, v___x_540_);
if (v_isShared_530_ == 0)
{
lean_ctor_set_tag(v___x_529_, 0);
lean_ctor_set(v___x_529_, 0, v___x_541_);
v___x_543_ = v___x_529_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v___x_541_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_bignumToJson(lean_object* v_n_546_){
_start:
{
lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_547_ = l_Nat_reprFast(v_n_546_);
v___x_548_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
return v___x_548_;
}
}
static lean_object* _init_l_USize_fromJson_x3f___closed__0(void){
_start:
{
lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_549_ = l_System_Platform_numBits;
v___x_550_ = lean_unsigned_to_nat(2u);
v___x_551_ = lean_nat_pow(v___x_550_, v___x_549_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_USize_fromJson_x3f(lean_object* v_j_554_){
_start:
{
lean_object* v___x_555_; 
lean_inc(v_j_554_);
v___x_555_ = l_Lean_bignumFromJson_x3f(v_j_554_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_object* v_a_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_563_; 
lean_dec(v_j_554_);
v_a_556_ = lean_ctor_get(v___x_555_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_563_ == 0)
{
v___x_558_ = v___x_555_;
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_a_556_);
lean_dec(v___x_555_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_561_; 
if (v_isShared_559_ == 0)
{
v___x_561_ = v___x_558_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_a_556_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
else
{
lean_object* v_a_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_584_; 
v_a_564_ = lean_ctor_get(v___x_555_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_584_ == 0)
{
v___x_566_ = v___x_555_;
v_isShared_567_ = v_isSharedCheck_584_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_a_564_);
lean_dec(v___x_555_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_584_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_568_; uint8_t v___x_569_; 
v___x_568_ = lean_obj_once(&l_USize_fromJson_x3f___closed__0, &l_USize_fromJson_x3f___closed__0_once, _init_l_USize_fromJson_x3f___closed__0);
v___x_569_ = lean_nat_dec_le(v___x_568_, v_a_564_);
if (v___x_569_ == 0)
{
size_t v___x_570_; lean_object* v___x_571_; lean_object* v___x_573_; 
lean_dec(v_j_554_);
v___x_570_ = lean_usize_of_nat(v_a_564_);
lean_dec(v_a_564_);
v___x_571_ = lean_box_usize(v___x_570_);
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 0, v___x_571_);
v___x_573_ = v___x_566_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v___x_571_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
else
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_582_; 
lean_dec(v_a_564_);
v___x_575_ = ((lean_object*)(l_USize_fromJson_x3f___closed__1));
v___x_576_ = lean_unsigned_to_nat(80u);
v___x_577_ = l_Lean_Json_pretty(v_j_554_, v___x_576_);
v___x_578_ = lean_string_append(v___x_575_, v___x_577_);
lean_dec_ref(v___x_577_);
v___x_579_ = ((lean_object*)(l_USize_fromJson_x3f___closed__2));
v___x_580_ = lean_string_append(v___x_578_, v___x_579_);
if (v_isShared_567_ == 0)
{
lean_ctor_set_tag(v___x_566_, 0);
lean_ctor_set(v___x_566_, 0, v___x_580_);
v___x_582_ = v___x_566_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v___x_580_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonUSize___lam__0(size_t v_v_587_){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_588_ = lean_usize_to_nat(v_v_587_);
v___x_589_ = l_Lean_bignumToJson(v___x_588_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonUSize___lam__0___boxed(lean_object* v_v_590_){
_start:
{
size_t v_v_boxed_591_; lean_object* v_res_592_; 
v_v_boxed_591_ = lean_unbox_usize(v_v_590_);
lean_dec(v_v_590_);
v_res_592_ = l_Lean_instToJsonUSize___lam__0(v_v_boxed_591_);
return v_res_592_;
}
}
static lean_object* _init_l_UInt64_fromJson_x3f___closed__0(void){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = lean_cstr_to_nat("18446744073709551616");
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_UInt64_fromJson_x3f(lean_object* v_j_597_){
_start:
{
lean_object* v___x_598_; 
lean_inc(v_j_597_);
v___x_598_ = l_Lean_bignumFromJson_x3f(v_j_597_);
if (lean_obj_tag(v___x_598_) == 0)
{
lean_object* v_a_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_606_; 
lean_dec(v_j_597_);
v_a_599_ = lean_ctor_get(v___x_598_, 0);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_606_ == 0)
{
v___x_601_ = v___x_598_;
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_a_599_);
lean_dec(v___x_598_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_604_; 
if (v_isShared_602_ == 0)
{
v___x_604_ = v___x_601_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v_a_599_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
}
else
{
lean_object* v_a_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_627_; 
v_a_607_ = lean_ctor_get(v___x_598_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_627_ == 0)
{
v___x_609_ = v___x_598_;
v_isShared_610_ = v_isSharedCheck_627_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_a_607_);
lean_dec(v___x_598_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_627_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_611_; uint8_t v___x_612_; 
v___x_611_ = lean_obj_once(&l_UInt64_fromJson_x3f___closed__0, &l_UInt64_fromJson_x3f___closed__0_once, _init_l_UInt64_fromJson_x3f___closed__0);
v___x_612_ = lean_nat_dec_le(v___x_611_, v_a_607_);
if (v___x_612_ == 0)
{
uint64_t v___x_613_; lean_object* v___x_614_; lean_object* v___x_616_; 
lean_dec(v_j_597_);
v___x_613_ = lean_uint64_of_nat(v_a_607_);
lean_dec(v_a_607_);
v___x_614_ = lean_box_uint64(v___x_613_);
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 0, v___x_614_);
v___x_616_ = v___x_609_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_614_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
else
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_625_; 
lean_dec(v_a_607_);
v___x_618_ = ((lean_object*)(l_USize_fromJson_x3f___closed__1));
v___x_619_ = lean_unsigned_to_nat(80u);
v___x_620_ = l_Lean_Json_pretty(v_j_597_, v___x_619_);
v___x_621_ = lean_string_append(v___x_618_, v___x_620_);
lean_dec_ref(v___x_620_);
v___x_622_ = ((lean_object*)(l_UInt64_fromJson_x3f___closed__1));
v___x_623_ = lean_string_append(v___x_621_, v___x_622_);
if (v_isShared_610_ == 0)
{
lean_ctor_set_tag(v___x_609_, 0);
lean_ctor_set(v___x_609_, 0, v___x_623_);
v___x_625_ = v___x_609_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_623_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonUInt64___lam__0(uint64_t v_v_630_){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_631_ = lean_uint64_to_nat(v_v_630_);
v___x_632_ = l_Lean_bignumToJson(v___x_631_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonUInt64___lam__0___boxed(lean_object* v_v_633_){
_start:
{
uint64_t v_v_boxed_634_; lean_object* v_res_635_; 
v_v_boxed_634_ = lean_unbox_uint64(v_v_633_);
lean_dec_ref(v_v_633_);
v_res_635_ = l_Lean_instToJsonUInt64___lam__0(v_v_boxed_634_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l_Float_toJson(double v_x_638_){
_start:
{
lean_object* v___x_639_; 
v___x_639_ = l_Lean_JsonNumber_fromFloat_x3f(v_x_638_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v_val_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_647_; 
v_val_640_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_647_ == 0)
{
v___x_642_ = v___x_639_;
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_val_640_);
lean_dec(v___x_639_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_645_; 
if (v_isShared_643_ == 0)
{
lean_ctor_set_tag(v___x_642_, 3);
v___x_645_ = v___x_642_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_val_640_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
else
{
lean_object* v_val_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_655_; 
v_val_648_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_655_ == 0)
{
v___x_650_ = v___x_639_;
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_val_648_);
lean_dec(v___x_639_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_653_; 
if (v_isShared_651_ == 0)
{
lean_ctor_set_tag(v___x_650_, 2);
v___x_653_ = v___x_650_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_val_648_);
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
LEAN_EXPORT lean_object* l_Float_toJson___boxed(lean_object* v_x_656_){
_start:
{
double v_x_boxed_657_; lean_object* v_res_658_; 
v_x_boxed_657_ = lean_unbox_float(v_x_656_);
lean_dec_ref(v_x_656_);
v_res_658_ = l_Float_toJson(v_x_boxed_657_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l_Float_fromJson_x3f(lean_object* v_x_667_){
_start:
{
switch(lean_obj_tag(v_x_667_))
{
case 3:
{
lean_object* v_s_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_709_; 
v_s_670_ = lean_ctor_get(v_x_667_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v_x_667_);
if (v_isSharedCheck_709_ == 0)
{
v___x_672_ = v_x_667_;
v_isShared_673_ = v_isSharedCheck_709_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_s_670_);
lean_dec(v_x_667_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_709_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_674_; uint8_t v___x_675_; 
v___x_674_ = ((lean_object*)(l_Float_fromJson_x3f___closed__2));
v___x_675_ = lean_string_dec_eq(v_s_670_, v___x_674_);
if (v___x_675_ == 0)
{
lean_object* v___x_676_; uint8_t v___x_677_; 
v___x_676_ = ((lean_object*)(l_Float_fromJson_x3f___closed__3));
v___x_677_ = lean_string_dec_eq(v_s_670_, v___x_676_);
if (v___x_677_ == 0)
{
lean_object* v___x_678_; uint8_t v___x_679_; 
v___x_678_ = ((lean_object*)(l_Float_fromJson_x3f___closed__4));
v___x_679_ = lean_string_dec_eq(v_s_670_, v___x_678_);
lean_dec_ref(v_s_670_);
if (v___x_679_ == 0)
{
lean_del_object(v___x_672_);
goto v___jp_668_;
}
else
{
lean_object* v___x_680_; lean_object* v___x_681_; double v___x_682_; double v___x_683_; lean_object* v___x_684_; lean_object* v___x_686_; 
v___x_680_ = lean_unsigned_to_nat(0u);
v___x_681_ = lean_unsigned_to_nat(1u);
v___x_682_ = l_Float_ofScientific(v___x_680_, v___x_679_, v___x_681_);
v___x_683_ = lean_float_div(v___x_682_, v___x_682_);
v___x_684_ = lean_box_float(v___x_683_);
if (v_isShared_673_ == 0)
{
lean_ctor_set_tag(v___x_672_, 1);
lean_ctor_set(v___x_672_, 0, v___x_684_);
v___x_686_ = v___x_672_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v___x_684_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
else
{
lean_object* v___x_688_; lean_object* v___x_689_; double v___x_690_; double v___x_691_; lean_object* v___x_692_; double v___x_693_; double v___x_694_; lean_object* v___x_695_; lean_object* v___x_697_; 
lean_dec_ref(v_s_670_);
v___x_688_ = lean_unsigned_to_nat(10u);
v___x_689_ = lean_unsigned_to_nat(1u);
v___x_690_ = l_Float_ofScientific(v___x_688_, v___x_677_, v___x_689_);
v___x_691_ = lean_float_negate(v___x_690_);
v___x_692_ = lean_unsigned_to_nat(0u);
v___x_693_ = l_Float_ofScientific(v___x_692_, v___x_677_, v___x_689_);
v___x_694_ = lean_float_div(v___x_691_, v___x_693_);
v___x_695_ = lean_box_float(v___x_694_);
if (v_isShared_673_ == 0)
{
lean_ctor_set_tag(v___x_672_, 1);
lean_ctor_set(v___x_672_, 0, v___x_695_);
v___x_697_ = v___x_672_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_695_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
else
{
lean_object* v___x_699_; lean_object* v___x_700_; double v___x_701_; lean_object* v___x_702_; double v___x_703_; double v___x_704_; lean_object* v___x_705_; lean_object* v___x_707_; 
lean_dec_ref(v_s_670_);
v___x_699_ = lean_unsigned_to_nat(10u);
v___x_700_ = lean_unsigned_to_nat(1u);
v___x_701_ = l_Float_ofScientific(v___x_699_, v___x_675_, v___x_700_);
v___x_702_ = lean_unsigned_to_nat(0u);
v___x_703_ = l_Float_ofScientific(v___x_702_, v___x_675_, v___x_700_);
v___x_704_ = lean_float_div(v___x_701_, v___x_703_);
v___x_705_ = lean_box_float(v___x_704_);
if (v_isShared_673_ == 0)
{
lean_ctor_set_tag(v___x_672_, 1);
lean_ctor_set(v___x_672_, 0, v___x_705_);
v___x_707_ = v___x_672_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v___x_705_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
}
case 2:
{
lean_object* v_n_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_719_; 
v_n_710_ = lean_ctor_get(v_x_667_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v_x_667_);
if (v_isSharedCheck_719_ == 0)
{
v___x_712_ = v_x_667_;
v_isShared_713_ = v_isSharedCheck_719_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_n_710_);
lean_dec(v_x_667_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_719_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
double v___x_714_; lean_object* v___x_715_; lean_object* v___x_717_; 
v___x_714_ = l_Lean_JsonNumber_toFloat(v_n_710_);
v___x_715_ = lean_box_float(v___x_714_);
if (v_isShared_713_ == 0)
{
lean_ctor_set_tag(v___x_712_, 1);
lean_ctor_set(v___x_712_, 0, v___x_715_);
v___x_717_ = v___x_712_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v___x_715_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
default: 
{
lean_dec(v_x_667_);
goto v___jp_668_;
}
}
v___jp_668_:
{
lean_object* v___x_669_; 
v___x_669_ = ((lean_object*)(l_Float_fromJson_x3f___closed__1));
return v___x_669_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_fromJson_x3f(lean_object* v_x_723_){
_start:
{
switch(lean_obj_tag(v_x_723_))
{
case 4:
{
lean_object* v_elems_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_732_; 
v_elems_724_ = lean_ctor_get(v_x_723_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v_x_723_);
if (v_isSharedCheck_732_ == 0)
{
v___x_726_ = v_x_723_;
v_isShared_727_ = v_isSharedCheck_732_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_elems_724_);
lean_dec(v_x_723_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_732_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_729_; 
if (v_isShared_727_ == 0)
{
lean_ctor_set_tag(v___x_726_, 0);
v___x_729_ = v___x_726_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_elems_724_);
v___x_729_ = v_reuseFailAlloc_731_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
lean_object* v___x_730_; 
v___x_730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_730_, 0, v___x_729_);
return v___x_730_;
}
}
}
case 5:
{
lean_object* v_kvPairs_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_741_; 
v_kvPairs_733_ = lean_ctor_get(v_x_723_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v_x_723_);
if (v_isSharedCheck_741_ == 0)
{
v___x_735_ = v_x_723_;
v_isShared_736_ = v_isSharedCheck_741_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_kvPairs_733_);
lean_dec(v_x_723_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_741_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_738_; 
if (v_isShared_736_ == 0)
{
lean_ctor_set_tag(v___x_735_, 1);
v___x_738_ = v___x_735_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_kvPairs_733_);
v___x_738_ = v_reuseFailAlloc_740_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
lean_object* v___x_739_; 
v___x_739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_739_, 0, v___x_738_);
return v___x_739_;
}
}
}
default: 
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_742_ = ((lean_object*)(l_Lean_Json_Structured_fromJson_x3f___closed__0));
v___x_743_ = lean_unsigned_to_nat(80u);
v___x_744_ = l_Lean_Json_pretty(v_x_723_, v___x_743_);
v___x_745_ = lean_string_append(v___x_742_, v___x_744_);
lean_dec_ref(v___x_744_);
v___x_746_ = ((lean_object*)(l_Array_fromJson_x3f___redArg___closed__11));
v___x_747_ = lean_string_append(v___x_745_, v___x_746_);
v___x_748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_748_, 0, v___x_747_);
return v___x_748_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_toJson(lean_object* v_x_751_){
_start:
{
if (lean_obj_tag(v_x_751_) == 0)
{
lean_object* v_elems_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_759_; 
v_elems_752_ = lean_ctor_get(v_x_751_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v_x_751_);
if (v_isSharedCheck_759_ == 0)
{
v___x_754_ = v_x_751_;
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_elems_752_);
lean_dec(v_x_751_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_757_; 
if (v_isShared_755_ == 0)
{
lean_ctor_set_tag(v___x_754_, 4);
v___x_757_ = v___x_754_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_elems_752_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
else
{
lean_object* v_kvPairs_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_767_; 
v_kvPairs_760_ = lean_ctor_get(v_x_751_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v_x_751_);
if (v_isSharedCheck_767_ == 0)
{
v___x_762_ = v_x_751_;
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_kvPairs_760_);
lean_dec(v_x_751_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_765_; 
if (v_isShared_763_ == 0)
{
lean_ctor_set_tag(v___x_762_, 5);
v___x_765_ = v___x_762_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_kvPairs_760_);
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
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___redArg(lean_object* v_inst_770_, lean_object* v_v_771_){
_start:
{
lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_772_ = lean_apply_1(v_inst_770_, v_v_771_);
v___x_773_ = l_Lean_Json_Structured_fromJson_x3f(v___x_772_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f(lean_object* v_00_u03b1_774_, lean_object* v_inst_775_, lean_object* v_v_776_){
_start:
{
lean_object* v___x_777_; 
v___x_777_ = l_Lean_Json_toStructured_x3f___redArg(v_inst_775_, v_v_776_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___redArg(lean_object* v_j_778_, lean_object* v_inst_779_, lean_object* v_k_780_){
_start:
{
lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_781_ = l_Lean_Json_getObjValD(v_j_778_, v_k_780_);
v___x_782_ = lean_apply_1(v_inst_779_, v___x_781_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___redArg___boxed(lean_object* v_j_783_, lean_object* v_inst_784_, lean_object* v_k_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_783_, v_inst_784_, v_k_785_);
lean_dec_ref(v_k_785_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f(lean_object* v_j_787_, lean_object* v_00_u03b1_788_, lean_object* v_inst_789_, lean_object* v_k_790_){
_start:
{
lean_object* v___x_791_; 
v___x_791_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_787_, v_inst_789_, v_k_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___boxed(lean_object* v_j_792_, lean_object* v_00_u03b1_793_, lean_object* v_inst_794_, lean_object* v_k_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l_Lean_Json_getObjValAs_x3f(v_j_792_, v_00_u03b1_793_, v_inst_794_, v_k_795_);
lean_dec_ref(v_k_795_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_setObjValAs_x21___redArg(lean_object* v_j_797_, lean_object* v_inst_798_, lean_object* v_k_799_, lean_object* v_v_800_){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_801_ = lean_apply_1(v_inst_798_, v_v_800_);
v___x_802_ = l_Lean_Json_setObjVal_x21(v_j_797_, v_k_799_, v___x_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_setObjValAs_x21(lean_object* v_j_803_, lean_object* v_00_u03b1_804_, lean_object* v_inst_805_, lean_object* v_k_806_, lean_object* v_v_807_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = l_Lean_Json_setObjValAs_x21___redArg(v_j_803_, v_inst_805_, v_k_806_, v_v_807_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___redArg(lean_object* v_inst_809_, lean_object* v_k_810_, lean_object* v_x_811_){
_start:
{
if (lean_obj_tag(v_x_811_) == 0)
{
lean_object* v___x_812_; 
lean_dec_ref(v_k_810_);
lean_dec_ref(v_inst_809_);
v___x_812_ = lean_box(0);
return v___x_812_;
}
else
{
lean_object* v_val_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v_val_813_ = lean_ctor_get(v_x_811_, 0);
lean_inc(v_val_813_);
lean_dec_ref(v_x_811_);
v___x_814_ = lean_apply_1(v_inst_809_, v_val_813_);
v___x_815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_815_, 0, v_k_810_);
lean_ctor_set(v___x_815_, 1, v___x_814_);
v___x_816_ = lean_box(0);
v___x_817_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_817_, 0, v___x_815_);
lean_ctor_set(v___x_817_, 1, v___x_816_);
return v___x_817_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt(lean_object* v_00_u03b1_818_, lean_object* v_inst_819_, lean_object* v_k_820_, lean_object* v_x_821_){
_start:
{
lean_object* v___x_822_; 
v___x_822_ = l_Lean_Json_opt___redArg(v_inst_819_, v_k_820_, v_x_821_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getTag_x3f(lean_object* v_x_823_){
_start:
{
switch(lean_obj_tag(v_x_823_))
{
case 3:
{
lean_object* v_s_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_831_; 
v_s_824_ = lean_ctor_get(v_x_823_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v_x_823_);
if (v_isSharedCheck_831_ == 0)
{
v___x_826_ = v_x_823_;
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_s_824_);
lean_dec(v_x_823_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_829_; 
if (v_isShared_827_ == 0)
{
lean_ctor_set_tag(v___x_826_, 1);
v___x_829_ = v___x_826_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_s_824_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
case 5:
{
lean_object* v_kvPairs_832_; lean_object* v___y_834_; 
v_kvPairs_832_ = lean_ctor_get(v_x_823_, 0);
lean_inc(v_kvPairs_832_);
lean_dec_ref(v_x_823_);
if (lean_obj_tag(v_kvPairs_832_) == 0)
{
lean_object* v_size_839_; 
v_size_839_ = lean_ctor_get(v_kvPairs_832_, 0);
lean_inc(v_size_839_);
v___y_834_ = v_size_839_;
goto v___jp_833_;
}
else
{
lean_object* v___x_840_; 
v___x_840_ = lean_unsigned_to_nat(0u);
v___y_834_ = v___x_840_;
goto v___jp_833_;
}
v___jp_833_:
{
lean_object* v___x_835_; uint8_t v___x_836_; 
v___x_835_ = lean_unsigned_to_nat(1u);
v___x_836_ = lean_nat_dec_eq(v___y_834_, v___x_835_);
lean_dec(v___y_834_);
if (v___x_836_ == 0)
{
lean_object* v___x_837_; 
lean_dec(v_kvPairs_832_);
v___x_837_ = lean_box(0);
return v___x_837_;
}
else
{
lean_object* v___x_838_; 
v___x_838_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_kvPairs_832_);
lean_dec(v_kvPairs_832_);
return v___x_838_;
}
}
}
default: 
{
lean_object* v___x_841_; 
lean_dec(v_x_823_);
v___x_841_ = lean_box(0);
return v___x_841_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Json_parseTagged_spec__0(lean_object* v_a_842_, lean_object* v_as_843_, size_t v_sz_844_, size_t v_i_845_, lean_object* v_b_846_){
_start:
{
uint8_t v___x_847_; 
v___x_847_ = lean_usize_dec_lt(v_i_845_, v_sz_844_);
if (v___x_847_ == 0)
{
lean_object* v___x_848_; 
lean_dec(v_a_842_);
v___x_848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_848_, 0, v_b_846_);
return v___x_848_;
}
else
{
lean_object* v_a_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v_a_849_ = lean_array_uget_borrowed(v_as_843_, v_i_845_);
v___x_850_ = l_Lean_Name_getString_x21(v_a_849_);
lean_inc(v_a_842_);
v___x_851_ = l_Lean_Json_getObjVal_x3f(v_a_842_, v___x_850_);
lean_dec_ref(v___x_850_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_859_; 
lean_dec_ref(v_b_846_);
lean_dec(v_a_842_);
v_a_852_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_859_ == 0)
{
v___x_854_ = v___x_851_;
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_dec(v___x_851_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_857_; 
if (v_isShared_855_ == 0)
{
v___x_857_ = v___x_854_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_a_852_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
else
{
lean_object* v_a_860_; lean_object* v___x_861_; size_t v___x_862_; size_t v___x_863_; 
v_a_860_ = lean_ctor_get(v___x_851_, 0);
lean_inc(v_a_860_);
lean_dec_ref(v___x_851_);
v___x_861_ = lean_array_push(v_b_846_, v_a_860_);
v___x_862_ = ((size_t)1ULL);
v___x_863_ = lean_usize_add(v_i_845_, v___x_862_);
v_i_845_ = v___x_863_;
v_b_846_ = v___x_861_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Json_parseTagged_spec__0___boxed(lean_object* v_a_865_, lean_object* v_as_866_, lean_object* v_sz_867_, lean_object* v_i_868_, lean_object* v_b_869_){
_start:
{
size_t v_sz_boxed_870_; size_t v_i_boxed_871_; lean_object* v_res_872_; 
v_sz_boxed_870_ = lean_unbox_usize(v_sz_867_);
lean_dec(v_sz_867_);
v_i_boxed_871_ = lean_unbox_usize(v_i_868_);
lean_dec(v_i_868_);
v_res_872_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Json_parseTagged_spec__0(v_a_865_, v_as_866_, v_sz_boxed_870_, v_i_boxed_871_, v_b_869_);
lean_dec_ref(v_as_866_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_parseTagged(lean_object* v_json_880_, lean_object* v_tag_881_, lean_object* v_nFields_882_, lean_object* v_fieldNames_x3f_883_){
_start:
{
lean_object* v___x_884_; uint8_t v___x_885_; 
v___x_884_ = lean_unsigned_to_nat(0u);
v___x_885_ = lean_nat_dec_eq(v_nFields_882_, v___x_884_);
if (v___x_885_ == 0)
{
lean_object* v___x_886_; 
v___x_886_ = l_Lean_Json_getObjVal_x3f(v_json_880_, v_tag_881_);
if (lean_obj_tag(v___x_886_) == 0)
{
lean_object* v_a_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_894_; 
lean_dec(v_nFields_882_);
v_a_887_ = lean_ctor_get(v___x_886_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_894_ == 0)
{
v___x_889_ = v___x_886_;
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_a_887_);
lean_dec(v___x_886_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_892_; 
if (v_isShared_890_ == 0)
{
v___x_892_ = v___x_889_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_a_887_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
else
{
if (lean_obj_tag(v_fieldNames_x3f_883_) == 0)
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_925_; 
v_a_895_ = lean_ctor_get(v___x_886_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_925_ == 0)
{
v___x_897_ = v___x_886_;
v_isShared_898_ = v_isSharedCheck_925_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_886_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_925_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_899_; uint8_t v___x_900_; 
v___x_899_ = lean_unsigned_to_nat(1u);
v___x_900_ = lean_nat_dec_eq(v_nFields_882_, v___x_899_);
if (v___x_900_ == 0)
{
lean_object* v___x_901_; 
lean_del_object(v___x_897_);
v___x_901_ = l_Lean_Json_getArr_x3f(v_a_895_);
if (lean_obj_tag(v___x_901_) == 0)
{
lean_dec(v_nFields_882_);
return v___x_901_;
}
else
{
lean_object* v_a_902_; lean_object* v___x_903_; uint8_t v___x_904_; 
v_a_902_ = lean_ctor_get(v___x_901_, 0);
lean_inc(v_a_902_);
v___x_903_ = lean_array_get_size(v_a_902_);
lean_dec(v_a_902_);
v___x_904_ = lean_nat_dec_eq(v___x_903_, v_nFields_882_);
if (v___x_904_ == 0)
{
lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_918_; 
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_918_ == 0)
{
lean_object* v_unused_919_; 
v_unused_919_ = lean_ctor_get(v___x_901_, 0);
lean_dec(v_unused_919_);
v___x_906_ = v___x_901_;
v_isShared_907_ = v_isSharedCheck_918_;
goto v_resetjp_905_;
}
else
{
lean_dec(v___x_901_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_918_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_916_; 
v___x_908_ = ((lean_object*)(l_Lean_Json_parseTagged___closed__0));
v___x_909_ = l_Nat_reprFast(v___x_903_);
v___x_910_ = lean_string_append(v___x_908_, v___x_909_);
lean_dec_ref(v___x_909_);
v___x_911_ = ((lean_object*)(l_Lean_Json_parseTagged___closed__1));
v___x_912_ = lean_string_append(v___x_910_, v___x_911_);
v___x_913_ = l_Nat_reprFast(v_nFields_882_);
v___x_914_ = lean_string_append(v___x_912_, v___x_913_);
lean_dec_ref(v___x_913_);
if (v_isShared_907_ == 0)
{
lean_ctor_set_tag(v___x_906_, 0);
lean_ctor_set(v___x_906_, 0, v___x_914_);
v___x_916_ = v___x_906_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v___x_914_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
else
{
lean_dec(v_nFields_882_);
return v___x_901_;
}
}
}
else
{
lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_923_; 
lean_dec(v_nFields_882_);
v___x_920_ = lean_mk_empty_array_with_capacity(v___x_899_);
v___x_921_ = lean_array_push(v___x_920_, v_a_895_);
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 0, v___x_921_);
v___x_923_ = v___x_897_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_921_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
else
{
lean_object* v_a_926_; lean_object* v_val_927_; lean_object* v_fields_928_; size_t v_sz_929_; size_t v___x_930_; lean_object* v___x_931_; 
lean_dec(v_nFields_882_);
v_a_926_ = lean_ctor_get(v___x_886_, 0);
lean_inc(v_a_926_);
lean_dec_ref(v___x_886_);
v_val_927_ = lean_ctor_get(v_fieldNames_x3f_883_, 0);
v_fields_928_ = ((lean_object*)(l_Lean_Json_parseTagged___closed__2));
v_sz_929_ = lean_array_size(v_val_927_);
v___x_930_ = ((size_t)0ULL);
v___x_931_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Json_parseTagged_spec__0(v_a_926_, v_val_927_, v_sz_929_, v___x_930_, v_fields_928_);
return v___x_931_;
}
}
}
else
{
lean_object* v___x_932_; 
lean_dec(v_nFields_882_);
v___x_932_ = l_Lean_Json_getStr_x3f(v_json_880_);
if (lean_obj_tag(v___x_932_) == 0)
{
lean_object* v_a_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_940_; 
v_a_933_ = lean_ctor_get(v___x_932_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_940_ == 0)
{
v___x_935_ = v___x_932_;
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_a_933_);
lean_dec(v___x_932_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_938_; 
if (v_isShared_936_ == 0)
{
v___x_938_ = v___x_935_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_a_933_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
else
{
lean_object* v_a_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_955_; 
v_a_941_ = lean_ctor_get(v___x_932_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_955_ == 0)
{
v___x_943_ = v___x_932_;
v_isShared_944_ = v_isSharedCheck_955_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_dec(v___x_932_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_955_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
uint8_t v___x_945_; 
v___x_945_ = lean_string_dec_eq(v_a_941_, v_tag_881_);
if (v___x_945_ == 0)
{
lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_952_; 
v___x_946_ = ((lean_object*)(l_Lean_Json_parseTagged___closed__3));
v___x_947_ = lean_string_append(v___x_946_, v_a_941_);
lean_dec(v_a_941_);
v___x_948_ = ((lean_object*)(l_Lean_Json_parseTagged___closed__1));
v___x_949_ = lean_string_append(v___x_947_, v___x_948_);
v___x_950_ = lean_string_append(v___x_949_, v_tag_881_);
if (v_isShared_944_ == 0)
{
lean_ctor_set_tag(v___x_943_, 0);
lean_ctor_set(v___x_943_, 0, v___x_950_);
v___x_952_ = v___x_943_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v___x_950_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
else
{
lean_object* v___x_954_; 
lean_del_object(v___x_943_);
lean_dec(v_a_941_);
v___x_954_ = ((lean_object*)(l_Lean_Json_parseTagged___closed__4));
return v___x_954_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_parseTagged___boxed(lean_object* v_json_956_, lean_object* v_tag_957_, lean_object* v_nFields_958_, lean_object* v_fieldNames_x3f_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_Lean_Json_parseTagged(v_json_956_, v_tag_957_, v_nFields_958_, v_fieldNames_x3f_959_);
lean_dec(v_fieldNames_x3f_959_);
lean_dec_ref(v_tag_957_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_parseCtorFields_spec__0(lean_object* v_a_961_, size_t v_sz_962_, size_t v_i_963_, lean_object* v_bs_964_){
_start:
{
uint8_t v___x_965_; 
v___x_965_ = lean_usize_dec_lt(v_i_963_, v_sz_962_);
if (v___x_965_ == 0)
{
lean_object* v___x_966_; 
lean_dec(v_a_961_);
v___x_966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_966_, 0, v_bs_964_);
return v___x_966_;
}
else
{
lean_object* v_v_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v_v_967_ = lean_array_uget_borrowed(v_bs_964_, v_i_963_);
v___x_968_ = l_Lean_Name_getString_x21(v_v_967_);
lean_inc(v_a_961_);
v___x_969_ = l_Lean_Json_getObjVal_x3f(v_a_961_, v___x_968_);
lean_dec_ref(v___x_968_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v_a_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_977_; 
lean_dec_ref(v_bs_964_);
lean_dec(v_a_961_);
v_a_970_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_977_ == 0)
{
v___x_972_ = v___x_969_;
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_dec(v___x_969_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_975_; 
if (v_isShared_973_ == 0)
{
v___x_975_ = v___x_972_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_a_970_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
else
{
lean_object* v_a_978_; lean_object* v___x_979_; lean_object* v_bs_x27_980_; size_t v___x_981_; size_t v___x_982_; lean_object* v___x_983_; 
v_a_978_ = lean_ctor_get(v___x_969_, 0);
lean_inc(v_a_978_);
lean_dec_ref(v___x_969_);
v___x_979_ = lean_unsigned_to_nat(0u);
v_bs_x27_980_ = lean_array_uset(v_bs_964_, v_i_963_, v___x_979_);
v___x_981_ = ((size_t)1ULL);
v___x_982_ = lean_usize_add(v_i_963_, v___x_981_);
v___x_983_ = lean_array_uset(v_bs_x27_980_, v_i_963_, v_a_978_);
v_i_963_ = v___x_982_;
v_bs_964_ = v___x_983_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_parseCtorFields_spec__0___boxed(lean_object* v_a_985_, lean_object* v_sz_986_, lean_object* v_i_987_, lean_object* v_bs_988_){
_start:
{
size_t v_sz_boxed_989_; size_t v_i_boxed_990_; lean_object* v_res_991_; 
v_sz_boxed_989_ = lean_unbox_usize(v_sz_986_);
lean_dec(v_sz_986_);
v_i_boxed_990_ = lean_unbox_usize(v_i_987_);
lean_dec(v_i_987_);
v_res_991_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_parseCtorFields_spec__0(v_a_985_, v_sz_boxed_989_, v_i_boxed_990_, v_bs_988_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_parseCtorFields(lean_object* v_json_992_, lean_object* v_tag_993_, lean_object* v_nFields_994_, lean_object* v_fieldNames_x3f_995_){
_start:
{
lean_object* v___x_996_; 
v___x_996_ = l_Lean_Json_getObjVal_x3f(v_json_992_, v_tag_993_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1004_; 
lean_dec(v_fieldNames_x3f_995_);
lean_dec(v_nFields_994_);
v_a_997_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1004_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_999_ = v___x_996_;
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_dec(v___x_996_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1002_; 
if (v_isShared_1000_ == 0)
{
v___x_1002_ = v___x_999_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_a_997_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
}
else
{
if (lean_obj_tag(v_fieldNames_x3f_995_) == 0)
{
lean_object* v_a_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1035_; 
v_a_1005_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1007_ = v___x_996_;
v_isShared_1008_ = v_isSharedCheck_1035_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_a_1005_);
lean_dec(v___x_996_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1035_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v___x_1009_; uint8_t v___x_1010_; 
v___x_1009_ = lean_unsigned_to_nat(1u);
v___x_1010_ = lean_nat_dec_eq(v_nFields_994_, v___x_1009_);
if (v___x_1010_ == 0)
{
lean_object* v___x_1011_; 
lean_del_object(v___x_1007_);
v___x_1011_ = l_Lean_Json_getArr_x3f(v_a_1005_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_dec(v_nFields_994_);
return v___x_1011_;
}
else
{
lean_object* v_a_1012_; lean_object* v___x_1013_; uint8_t v___x_1014_; 
v_a_1012_ = lean_ctor_get(v___x_1011_, 0);
lean_inc(v_a_1012_);
v___x_1013_ = lean_array_get_size(v_a_1012_);
lean_dec(v_a_1012_);
v___x_1014_ = lean_nat_dec_eq(v___x_1013_, v_nFields_994_);
if (v___x_1014_ == 0)
{
lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1028_; 
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1028_ == 0)
{
lean_object* v_unused_1029_; 
v_unused_1029_ = lean_ctor_get(v___x_1011_, 0);
lean_dec(v_unused_1029_);
v___x_1016_ = v___x_1011_;
v_isShared_1017_ = v_isSharedCheck_1028_;
goto v_resetjp_1015_;
}
else
{
lean_dec(v___x_1011_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1028_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1026_; 
v___x_1018_ = ((lean_object*)(l_Lean_Json_parseTagged___closed__0));
v___x_1019_ = l_Nat_reprFast(v___x_1013_);
v___x_1020_ = lean_string_append(v___x_1018_, v___x_1019_);
lean_dec_ref(v___x_1019_);
v___x_1021_ = ((lean_object*)(l_Lean_Json_parseTagged___closed__1));
v___x_1022_ = lean_string_append(v___x_1020_, v___x_1021_);
v___x_1023_ = l_Nat_reprFast(v_nFields_994_);
v___x_1024_ = lean_string_append(v___x_1022_, v___x_1023_);
lean_dec_ref(v___x_1023_);
if (v_isShared_1017_ == 0)
{
lean_ctor_set_tag(v___x_1016_, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1024_);
v___x_1026_ = v___x_1016_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v___x_1024_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
else
{
lean_dec(v_nFields_994_);
return v___x_1011_;
}
}
}
else
{
lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1033_; 
lean_dec(v_nFields_994_);
v___x_1030_ = lean_mk_empty_array_with_capacity(v___x_1009_);
v___x_1031_ = lean_array_push(v___x_1030_, v_a_1005_);
if (v_isShared_1008_ == 0)
{
lean_ctor_set(v___x_1007_, 0, v___x_1031_);
v___x_1033_ = v___x_1007_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v___x_1031_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
}
}
else
{
lean_object* v_a_1036_; lean_object* v_val_1037_; size_t v_sz_1038_; size_t v___x_1039_; lean_object* v___x_1040_; 
lean_dec(v_nFields_994_);
v_a_1036_ = lean_ctor_get(v___x_996_, 0);
lean_inc(v_a_1036_);
lean_dec_ref(v___x_996_);
v_val_1037_ = lean_ctor_get(v_fieldNames_x3f_995_, 0);
lean_inc(v_val_1037_);
lean_dec_ref(v_fieldNames_x3f_995_);
v_sz_1038_ = lean_array_size(v_val_1037_);
v___x_1039_ = ((size_t)0ULL);
v___x_1040_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_parseCtorFields_spec__0(v_a_1036_, v_sz_1038_, v___x_1039_, v_val_1037_);
return v___x_1040_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_parseCtorFields___boxed(lean_object* v_json_1041_, lean_object* v_tag_1042_, lean_object* v_nFields_1043_, lean_object* v_fieldNames_x3f_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = l_Lean_Json_parseCtorFields(v_json_1041_, v_tag_1042_, v_nFields_1043_, v_fieldNames_x3f_1044_);
lean_dec_ref(v_tag_1042_);
return v_res_1045_;
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
res = runtime_initialize_Lean_Data_Json_Printer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_GetLit(builtin);
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
res = initialize_Lean_Data_Json_Printer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_GetLit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Json_FromToJson_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Json_FromToJson_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Json_FromToJson_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
