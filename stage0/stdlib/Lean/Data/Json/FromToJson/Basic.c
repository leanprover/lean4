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
lean_object* l_String_compare___boxed(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_instFromJsonUnit___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "expected {} to decode Unit, got "};
static const lean_object* l_Lean_instFromJsonUnit___lam__0___closed__0 = (const lean_object*)&l_Lean_instFromJsonUnit___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_instFromJsonUnit___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_instFromJsonUnit___lam__0___closed__1 = (const lean_object*)&l_Lean_instFromJsonUnit___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_instFromJsonUnit___lam__0(lean_object*);
static const lean_closure_object l_Lean_instFromJsonUnit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instFromJsonUnit___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonUnit___closed__0 = (const lean_object*)&l_Lean_instFromJsonUnit___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instFromJsonUnit = (const lean_object*)&l_Lean_instFromJsonUnit___closed__0_value;
static const lean_ctor_object l_Lean_instToJsonUnit___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instToJsonUnit___lam__0___closed__0 = (const lean_object*)&l_Lean_instToJsonUnit___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instToJsonUnit___lam__0(lean_object*);
static const lean_closure_object l_Lean_instToJsonUnit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonUnit___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonUnit___closed__0 = (const lean_object*)&l_Lean_instToJsonUnit___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonUnit = (const lean_object*)&l_Lean_instToJsonUnit___closed__0_value;
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
static const lean_closure_object l_Lean_NameMap_toJson___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_compare___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_NameMap_toJson___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_NameMap_toJson___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_instFromJsonUnit___lam__0(lean_object* v_x_16_){
_start:
{
if (lean_obj_tag(v_x_16_) == 5)
{
lean_object* v_kvPairs_23_; 
v_kvPairs_23_ = lean_ctor_get(v_x_16_, 0);
if (lean_obj_tag(v_kvPairs_23_) == 1)
{
lean_object* v___x_24_; 
lean_dec_ref_known(v_x_16_, 1);
v___x_24_ = ((lean_object*)(l_Lean_instFromJsonUnit___lam__0___closed__1));
return v___x_24_;
}
else
{
goto v___jp_17_;
}
}
else
{
goto v___jp_17_;
}
v___jp_17_:
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_18_ = ((lean_object*)(l_Lean_instFromJsonUnit___lam__0___closed__0));
v___x_19_ = lean_unsigned_to_nat(80u);
v___x_20_ = l_Lean_Json_pretty(v_x_16_, v___x_19_);
v___x_21_ = lean_string_append(v___x_18_, v___x_20_);
lean_dec_ref(v___x_20_);
v___x_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_22_, 0, v___x_21_);
return v___x_22_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonUnit___lam__0(lean_object* v_x_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = ((lean_object*)(l_Lean_instToJsonUnit___lam__0___closed__0));
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonEmpty___lam__0(lean_object* v_j_35_){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_36_ = ((lean_object*)(l_Lean_instFromJsonEmpty___lam__0___closed__0));
v___x_37_ = lean_unsigned_to_nat(80u);
v___x_38_ = l_Lean_Json_pretty(v_j_35_, v___x_37_);
v___x_39_ = lean_string_append(v___x_36_, v___x_38_);
lean_dec_ref(v___x_38_);
v___x_40_ = ((lean_object*)(l_Lean_instFromJsonEmpty___lam__0___closed__1));
v___x_41_ = lean_string_append(v___x_39_, v___x_40_);
v___x_42_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_42_, 0, v___x_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonEmpty___lam__0(uint8_t v_a_45_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonEmpty___lam__0___boxed(lean_object* v_a_46_){
_start:
{
uint8_t v_a_6__boxed_47_; lean_object* v_res_48_; 
v_a_6__boxed_47_ = lean_unbox(v_a_46_);
v_res_48_ = l_Lean_instToJsonEmpty___lam__0(v_a_6__boxed_47_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBool___lam__0(uint8_t v_b_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_54_, 0, v_b_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBool___lam__0___boxed(lean_object* v_b_55_){
_start:
{
uint8_t v_b_boxed_56_; lean_object* v_res_57_; 
v_b_boxed_56_ = lean_unbox(v_b_55_);
v_res_57_ = l_Lean_instToJsonBool___lam__0(v_b_boxed_56_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonNat___lam__0(lean_object* v_n_62_){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_63_ = l_Lean_JsonNumber_fromNat(v_n_62_);
v___x_64_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_64_, 0, v___x_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonInt___lam__0(lean_object* v_n_69_){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_70_ = l_Lean_JsonNumber_fromInt(v_n_69_);
v___x_71_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonString___lam__0(lean_object* v_s_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_77_, 0, v_s_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonSlice___lam__0(lean_object* v_s_87_){
_start:
{
lean_object* v_str_88_; lean_object* v_startInclusive_89_; lean_object* v_endExclusive_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v_str_88_ = lean_ctor_get(v_s_87_, 0);
v_startInclusive_89_ = lean_ctor_get(v_s_87_, 1);
v_endExclusive_90_ = lean_ctor_get(v_s_87_, 2);
v___x_91_ = lean_string_utf8_extract(v_str_88_, v_startInclusive_89_, v_endExclusive_90_);
v___x_92_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_92_, 0, v___x_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonSlice___lam__0___boxed(lean_object* v_s_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Lean_instToJsonSlice___lam__0(v_s_93_);
lean_dec_ref(v_s_93_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonFilePath___lam__0(lean_object* v_j_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l_Lean_Json_getStr_x3f(v_j_97_);
if (lean_obj_tag(v___x_98_) == 0)
{
lean_object* v_a_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_106_; 
v_a_99_ = lean_ctor_get(v___x_98_, 0);
v_isSharedCheck_106_ = !lean_is_exclusive(v___x_98_);
if (v_isSharedCheck_106_ == 0)
{
v___x_101_ = v___x_98_;
v_isShared_102_ = v_isSharedCheck_106_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_a_99_);
lean_dec(v___x_98_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_106_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v___x_104_; 
if (v_isShared_102_ == 0)
{
v___x_104_ = v___x_101_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v_a_99_);
v___x_104_ = v_reuseFailAlloc_105_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
return v___x_104_;
}
}
}
else
{
lean_object* v_a_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_114_; 
v_a_107_ = lean_ctor_get(v___x_98_, 0);
v_isSharedCheck_114_ = !lean_is_exclusive(v___x_98_);
if (v_isSharedCheck_114_ == 0)
{
v___x_109_ = v___x_98_;
v_isShared_110_ = v_isSharedCheck_114_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_a_107_);
lean_dec(v___x_98_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_114_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_112_; 
if (v_isShared_110_ == 0)
{
v___x_112_ = v___x_109_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v_a_107_);
v___x_112_ = v_reuseFailAlloc_113_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
return v___x_112_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonFilePath___lam__0(lean_object* v_p_117_){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_118_, 0, v_p_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___redArg(lean_object* v_inst_142_, lean_object* v_x_143_){
_start:
{
lean_object* v___x_144_; 
v___x_144_ = ((lean_object*)(l_Array_fromJson_x3f___redArg___closed__9));
if (lean_obj_tag(v_x_143_) == 4)
{
lean_object* v_elems_145_; size_t v_sz_146_; size_t v___x_147_; lean_object* v___x_148_; 
v_elems_145_ = lean_ctor_get(v_x_143_, 0);
lean_inc_ref(v_elems_145_);
lean_dec_ref_known(v_x_143_, 1);
v_sz_146_ = lean_array_size(v_elems_145_);
v___x_147_ = ((size_t)0ULL);
v___x_148_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_144_, v_inst_142_, v_sz_146_, v___x_147_, v_elems_145_);
return v___x_148_;
}
else
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
lean_dec_ref(v_inst_142_);
v___x_149_ = ((lean_object*)(l_Array_fromJson_x3f___redArg___closed__10));
v___x_150_ = lean_unsigned_to_nat(80u);
v___x_151_ = l_Lean_Json_pretty(v_x_143_, v___x_150_);
v___x_152_ = lean_string_append(v___x_149_, v___x_151_);
lean_dec_ref(v___x_151_);
v___x_153_ = ((lean_object*)(l_Array_fromJson_x3f___redArg___closed__11));
v___x_154_ = lean_string_append(v___x_152_, v___x_153_);
v___x_155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_155_, 0, v___x_154_);
return v___x_155_;
}
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f(lean_object* v_00_u03b1_156_, lean_object* v_inst_157_, lean_object* v_x_158_){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = l_Array_fromJson_x3f___redArg(v_inst_157_, v_x_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonArray___redArg(lean_object* v_inst_160_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = lean_alloc_closure((void*)(l_Array_fromJson_x3f), 3, 2);
lean_closure_set(v___x_161_, 0, lean_box(0));
lean_closure_set(v___x_161_, 1, v_inst_160_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonArray(lean_object* v_00_u03b1_162_, lean_object* v_inst_163_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = lean_alloc_closure((void*)(l_Array_fromJson_x3f), 3, 2);
lean_closure_set(v___x_164_, 0, lean_box(0));
lean_closure_set(v___x_164_, 1, v_inst_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___redArg___lam__0(lean_object* v_inst_165_, lean_object* v_x_166_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = lean_apply_1(v_inst_165_, v_x_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___redArg(lean_object* v_inst_187_, lean_object* v_a_188_){
_start:
{
lean_object* v___f_189_; lean_object* v___x_190_; size_t v_sz_191_; size_t v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v___f_189_ = lean_alloc_closure((void*)(l_Array_toJson___redArg___lam__0), 2, 1);
lean_closure_set(v___f_189_, 0, v_inst_187_);
v___x_190_ = ((lean_object*)(l_Array_toJson___redArg___closed__9));
v_sz_191_ = lean_array_size(v_a_188_);
v___x_192_ = ((size_t)0ULL);
v___x_193_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_190_, v___f_189_, v_sz_191_, v___x_192_, v_a_188_);
v___x_194_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_194_, 0, v___x_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson(lean_object* v_00_u03b1_195_, lean_object* v_inst_196_, lean_object* v_a_197_){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = l_Array_toJson___redArg(v_inst_196_, v_a_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonArray___redArg(lean_object* v_inst_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = lean_alloc_closure((void*)(l_Array_toJson), 3, 2);
lean_closure_set(v___x_200_, 0, lean_box(0));
lean_closure_set(v___x_200_, 1, v_inst_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonArray(lean_object* v_00_u03b1_201_, lean_object* v_inst_202_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = lean_alloc_closure((void*)(l_Array_toJson), 3, 2);
lean_closure_set(v___x_203_, 0, lean_box(0));
lean_closure_set(v___x_203_, 1, v_inst_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_List_fromJson_x3f___redArg(lean_object* v_inst_204_, lean_object* v_j_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l_Array_fromJson_x3f___redArg(v_inst_204_, v_j_205_);
if (lean_obj_tag(v___x_206_) == 0)
{
lean_object* v_a_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_214_; 
v_a_207_ = lean_ctor_get(v___x_206_, 0);
v_isSharedCheck_214_ = !lean_is_exclusive(v___x_206_);
if (v_isSharedCheck_214_ == 0)
{
v___x_209_ = v___x_206_;
v_isShared_210_ = v_isSharedCheck_214_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_a_207_);
lean_dec(v___x_206_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_214_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_212_; 
if (v_isShared_210_ == 0)
{
v___x_212_ = v___x_209_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v_a_207_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
return v___x_212_;
}
}
}
else
{
lean_object* v_a_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_223_; 
v_a_215_ = lean_ctor_get(v___x_206_, 0);
v_isSharedCheck_223_ = !lean_is_exclusive(v___x_206_);
if (v_isSharedCheck_223_ == 0)
{
v___x_217_ = v___x_206_;
v_isShared_218_ = v_isSharedCheck_223_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_a_215_);
lean_dec(v___x_206_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_223_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_219_; lean_object* v___x_221_; 
v___x_219_ = lean_array_to_list(v_a_215_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 0, v___x_219_);
v___x_221_ = v___x_217_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v___x_219_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_fromJson_x3f(lean_object* v_00_u03b1_224_, lean_object* v_inst_225_, lean_object* v_j_226_){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = l_List_fromJson_x3f___redArg(v_inst_225_, v_j_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonList___redArg(lean_object* v_inst_228_){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = lean_alloc_closure((void*)(l_List_fromJson_x3f), 3, 2);
lean_closure_set(v___x_229_, 0, lean_box(0));
lean_closure_set(v___x_229_, 1, v_inst_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonList(lean_object* v_00_u03b1_230_, lean_object* v_inst_231_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = lean_alloc_closure((void*)(l_List_fromJson_x3f), 3, 2);
lean_closure_set(v___x_232_, 0, lean_box(0));
lean_closure_set(v___x_232_, 1, v_inst_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_List_toJson___redArg(lean_object* v_inst_233_, lean_object* v_a_234_){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_235_ = lean_array_mk(v_a_234_);
v___x_236_ = l_Array_toJson___redArg(v_inst_233_, v___x_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_List_toJson(lean_object* v_00_u03b1_237_, lean_object* v_inst_238_, lean_object* v_a_239_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = l_List_toJson___redArg(v_inst_238_, v_a_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonList___redArg(lean_object* v_inst_241_){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = lean_alloc_closure((void*)(l_List_toJson), 3, 2);
lean_closure_set(v___x_242_, 0, lean_box(0));
lean_closure_set(v___x_242_, 1, v_inst_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonList(lean_object* v_00_u03b1_243_, lean_object* v_inst_244_){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = lean_alloc_closure((void*)(l_List_toJson), 3, 2);
lean_closure_set(v___x_245_, 0, lean_box(0));
lean_closure_set(v___x_245_, 1, v_inst_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___redArg(lean_object* v_inst_248_, lean_object* v_x_249_){
_start:
{
if (lean_obj_tag(v_x_249_) == 0)
{
lean_object* v___x_250_; 
lean_dec_ref(v_inst_248_);
v___x_250_ = ((lean_object*)(l_Option_fromJson_x3f___redArg___closed__0));
return v___x_250_;
}
else
{
lean_object* v___x_251_; 
v___x_251_ = lean_apply_1(v_inst_248_, v_x_249_);
if (lean_obj_tag(v___x_251_) == 0)
{
lean_object* v_a_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_259_; 
v_a_252_ = lean_ctor_get(v___x_251_, 0);
v_isSharedCheck_259_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_259_ == 0)
{
v___x_254_ = v___x_251_;
v_isShared_255_ = v_isSharedCheck_259_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_a_252_);
lean_dec(v___x_251_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_259_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_257_; 
if (v_isShared_255_ == 0)
{
v___x_257_ = v___x_254_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v_a_252_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
return v___x_257_;
}
}
}
else
{
lean_object* v_a_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_268_; 
v_a_260_ = lean_ctor_get(v___x_251_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_268_ == 0)
{
v___x_262_ = v___x_251_;
v_isShared_263_ = v_isSharedCheck_268_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_a_260_);
lean_dec(v___x_251_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_268_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_264_; lean_object* v___x_266_; 
v___x_264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_264_, 0, v_a_260_);
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 0, v___x_264_);
v___x_266_ = v___x_262_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v___x_264_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f(lean_object* v_00_u03b1_269_, lean_object* v_inst_270_, lean_object* v_x_271_){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = l_Option_fromJson_x3f___redArg(v_inst_270_, v_x_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonOption___redArg(lean_object* v_inst_273_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = lean_alloc_closure((void*)(l_Option_fromJson_x3f), 3, 2);
lean_closure_set(v___x_274_, 0, lean_box(0));
lean_closure_set(v___x_274_, 1, v_inst_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonOption(lean_object* v_00_u03b1_275_, lean_object* v_inst_276_){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = lean_alloc_closure((void*)(l_Option_fromJson_x3f), 3, 2);
lean_closure_set(v___x_277_, 0, lean_box(0));
lean_closure_set(v___x_277_, 1, v_inst_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Option_toJson___redArg(lean_object* v_inst_278_, lean_object* v_x_279_){
_start:
{
if (lean_obj_tag(v_x_279_) == 0)
{
lean_object* v___x_280_; 
lean_dec_ref(v_inst_278_);
v___x_280_ = lean_box(0);
return v___x_280_;
}
else
{
lean_object* v_val_281_; lean_object* v___x_282_; 
v_val_281_ = lean_ctor_get(v_x_279_, 0);
lean_inc(v_val_281_);
lean_dec_ref_known(v_x_279_, 1);
v___x_282_ = lean_apply_1(v_inst_278_, v_val_281_);
return v___x_282_;
}
}
}
LEAN_EXPORT lean_object* l_Option_toJson(lean_object* v_00_u03b1_283_, lean_object* v_inst_284_, lean_object* v_x_285_){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = l_Option_toJson___redArg(v_inst_284_, v_x_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonOption___redArg(lean_object* v_inst_287_){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = lean_alloc_closure((void*)(l_Option_toJson), 3, 2);
lean_closure_set(v___x_288_, 0, lean_box(0));
lean_closure_set(v___x_288_, 1, v_inst_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonOption(lean_object* v_00_u03b1_289_, lean_object* v_inst_290_){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = lean_alloc_closure((void*)(l_Option_toJson), 3, 2);
lean_closure_set(v___x_291_, 0, lean_box(0));
lean_closure_set(v___x_291_, 1, v_inst_290_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Prod_fromJson_x3f___redArg(lean_object* v_inst_293_, lean_object* v_inst_294_, lean_object* v_x_295_){
_start:
{
lean_object* v_j_297_; 
if (lean_obj_tag(v_x_295_) == 4)
{
lean_object* v_elems_305_; lean_object* v___x_306_; lean_object* v___x_307_; uint8_t v___x_308_; 
v_elems_305_ = lean_ctor_get(v_x_295_, 0);
v___x_306_ = lean_array_get_size(v_elems_305_);
v___x_307_ = lean_unsigned_to_nat(2u);
v___x_308_ = lean_nat_dec_eq(v___x_306_, v___x_307_);
if (v___x_308_ == 0)
{
lean_dec_ref(v_inst_294_);
lean_dec_ref(v_inst_293_);
v_j_297_ = v_x_295_;
goto v___jp_296_;
}
else
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
lean_inc_ref(v_elems_305_);
lean_dec_ref_known(v_x_295_, 1);
v___x_309_ = lean_unsigned_to_nat(0u);
v___x_310_ = lean_array_fget_borrowed(v_elems_305_, v___x_309_);
lean_inc(v___x_310_);
v___x_311_ = lean_apply_1(v_inst_293_, v___x_310_);
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v_a_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_319_; 
lean_dec_ref(v_elems_305_);
lean_dec_ref(v_inst_294_);
v_a_312_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_319_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_319_ == 0)
{
v___x_314_ = v___x_311_;
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_a_312_);
lean_dec(v___x_311_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_317_; 
if (v_isShared_315_ == 0)
{
v___x_317_ = v___x_314_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_a_312_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
else
{
lean_object* v_a_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v_a_320_ = lean_ctor_get(v___x_311_, 0);
lean_inc(v_a_320_);
lean_dec_ref_known(v___x_311_, 1);
v___x_321_ = lean_unsigned_to_nat(1u);
v___x_322_ = lean_array_fget(v_elems_305_, v___x_321_);
lean_dec_ref(v_elems_305_);
v___x_323_ = lean_apply_1(v_inst_294_, v___x_322_);
if (lean_obj_tag(v___x_323_) == 0)
{
lean_object* v_a_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_331_; 
lean_dec(v_a_320_);
v_a_324_ = lean_ctor_get(v___x_323_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_323_);
if (v_isSharedCheck_331_ == 0)
{
v___x_326_ = v___x_323_;
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_a_324_);
lean_dec(v___x_323_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_329_; 
if (v_isShared_327_ == 0)
{
v___x_329_ = v___x_326_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_a_324_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
else
{
lean_object* v_a_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_340_; 
v_a_332_ = lean_ctor_get(v___x_323_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v___x_323_);
if (v_isSharedCheck_340_ == 0)
{
v___x_334_ = v___x_323_;
v_isShared_335_ = v_isSharedCheck_340_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_a_332_);
lean_dec(v___x_323_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_340_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_336_; lean_object* v___x_338_; 
v___x_336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_336_, 0, v_a_320_);
lean_ctor_set(v___x_336_, 1, v_a_332_);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 0, v___x_336_);
v___x_338_ = v___x_334_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v___x_336_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_inst_294_);
lean_dec_ref(v_inst_293_);
v_j_297_ = v_x_295_;
goto v___jp_296_;
}
v___jp_296_:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_298_ = ((lean_object*)(l_Prod_fromJson_x3f___redArg___closed__0));
v___x_299_ = lean_unsigned_to_nat(80u);
v___x_300_ = l_Lean_Json_pretty(v_j_297_, v___x_299_);
v___x_301_ = lean_string_append(v___x_298_, v___x_300_);
lean_dec_ref(v___x_300_);
v___x_302_ = ((lean_object*)(l_Array_fromJson_x3f___redArg___closed__11));
v___x_303_ = lean_string_append(v___x_301_, v___x_302_);
v___x_304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_304_, 0, v___x_303_);
return v___x_304_;
}
}
}
LEAN_EXPORT lean_object* l_Prod_fromJson_x3f(lean_object* v_00_u03b1_341_, lean_object* v_00_u03b2_342_, lean_object* v_inst_343_, lean_object* v_inst_344_, lean_object* v_x_345_){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = l_Prod_fromJson_x3f___redArg(v_inst_343_, v_inst_344_, v_x_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonProd___redArg(lean_object* v_inst_347_, lean_object* v_inst_348_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = lean_alloc_closure((void*)(l_Prod_fromJson_x3f), 5, 4);
lean_closure_set(v___x_349_, 0, lean_box(0));
lean_closure_set(v___x_349_, 1, lean_box(0));
lean_closure_set(v___x_349_, 2, v_inst_347_);
lean_closure_set(v___x_349_, 3, v_inst_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonProd(lean_object* v_00_u03b1_350_, lean_object* v_00_u03b2_351_, lean_object* v_inst_352_, lean_object* v_inst_353_){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = lean_alloc_closure((void*)(l_Prod_fromJson_x3f), 5, 4);
lean_closure_set(v___x_354_, 0, lean_box(0));
lean_closure_set(v___x_354_, 1, lean_box(0));
lean_closure_set(v___x_354_, 2, v_inst_352_);
lean_closure_set(v___x_354_, 3, v_inst_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Prod_toJson___redArg(lean_object* v_inst_355_, lean_object* v_inst_356_, lean_object* v_x_357_){
_start:
{
lean_object* v_fst_358_; lean_object* v_snd_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v_fst_358_ = lean_ctor_get(v_x_357_, 0);
lean_inc(v_fst_358_);
v_snd_359_ = lean_ctor_get(v_x_357_, 1);
lean_inc(v_snd_359_);
lean_dec_ref(v_x_357_);
v___x_360_ = lean_apply_1(v_inst_355_, v_fst_358_);
v___x_361_ = lean_apply_1(v_inst_356_, v_snd_359_);
v___x_362_ = lean_unsigned_to_nat(2u);
v___x_363_ = lean_mk_empty_array_with_capacity(v___x_362_);
v___x_364_ = lean_array_push(v___x_363_, v___x_360_);
v___x_365_ = lean_array_push(v___x_364_, v___x_361_);
v___x_366_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_366_, 0, v___x_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Prod_toJson(lean_object* v_00_u03b1_367_, lean_object* v_00_u03b2_368_, lean_object* v_inst_369_, lean_object* v_inst_370_, lean_object* v_x_371_){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = l_Prod_toJson___redArg(v_inst_369_, v_inst_370_, v_x_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonProd___redArg(lean_object* v_inst_373_, lean_object* v_inst_374_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = lean_alloc_closure((void*)(l_Prod_toJson), 5, 4);
lean_closure_set(v___x_375_, 0, lean_box(0));
lean_closure_set(v___x_375_, 1, lean_box(0));
lean_closure_set(v___x_375_, 2, v_inst_373_);
lean_closure_set(v___x_375_, 3, v_inst_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonProd(lean_object* v_00_u03b1_376_, lean_object* v_00_u03b2_377_, lean_object* v_inst_378_, lean_object* v_inst_379_){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = lean_alloc_closure((void*)(l_Prod_toJson), 5, 4);
lean_closure_set(v___x_380_, 0, lean_box(0));
lean_closure_set(v___x_380_, 1, lean_box(0));
lean_closure_set(v___x_380_, 2, v_inst_378_);
lean_closure_set(v___x_380_, 3, v_inst_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_fromJson_x3f(lean_object* v_j_385_){
_start:
{
lean_object* v___x_386_; 
lean_inc(v_j_385_);
v___x_386_ = l_Lean_Json_getStr_x3f(v_j_385_);
if (lean_obj_tag(v___x_386_) == 0)
{
lean_object* v_a_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_394_; 
lean_dec(v_j_385_);
v_a_387_ = lean_ctor_get(v___x_386_, 0);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_394_ == 0)
{
v___x_389_ = v___x_386_;
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_a_387_);
lean_dec(v___x_386_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_392_; 
if (v_isShared_390_ == 0)
{
v___x_392_ = v___x_389_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_a_387_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
}
else
{
lean_object* v_a_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_416_; 
v_a_395_ = lean_ctor_get(v___x_386_, 0);
v_isSharedCheck_416_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_416_ == 0)
{
v___x_397_ = v___x_386_;
v_isShared_398_ = v_isSharedCheck_416_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_a_395_);
lean_dec(v___x_386_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_416_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_399_; uint8_t v___x_400_; 
v___x_399_ = ((lean_object*)(l_Lean_Name_fromJson_x3f___closed__0));
v___x_400_ = lean_string_dec_eq(v_a_395_, v___x_399_);
if (v___x_400_ == 0)
{
lean_object* v___x_401_; uint8_t v___x_402_; 
v___x_401_ = l_String_toName(v_a_395_);
v___x_402_ = l_Lean_Name_isAnonymous(v___x_401_);
if (v___x_402_ == 0)
{
lean_object* v___x_404_; 
lean_dec(v_j_385_);
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 0, v___x_401_);
v___x_404_ = v___x_397_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_401_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
else
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_413_; 
lean_dec(v___x_401_);
v___x_406_ = ((lean_object*)(l_Lean_Name_fromJson_x3f___closed__1));
v___x_407_ = lean_unsigned_to_nat(80u);
v___x_408_ = l_Lean_Json_pretty(v_j_385_, v___x_407_);
v___x_409_ = lean_string_append(v___x_406_, v___x_408_);
lean_dec_ref(v___x_408_);
v___x_410_ = ((lean_object*)(l_Array_fromJson_x3f___redArg___closed__11));
v___x_411_ = lean_string_append(v___x_409_, v___x_410_);
if (v_isShared_398_ == 0)
{
lean_ctor_set_tag(v___x_397_, 0);
lean_ctor_set(v___x_397_, 0, v___x_411_);
v___x_413_ = v___x_397_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v___x_411_);
v___x_413_ = v_reuseFailAlloc_414_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
return v___x_413_;
}
}
}
else
{
lean_object* v___x_415_; 
lean_del_object(v___x_397_);
lean_dec(v_a_395_);
lean_dec(v_j_385_);
v___x_415_ = ((lean_object*)(l_Lean_Name_fromJson_x3f___closed__2));
return v___x_415_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonName___lam__0(lean_object* v_n_419_){
_start:
{
uint8_t v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_420_ = 1;
v___x_421_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_419_, v___x_420_);
v___x_422_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_422_, 0, v___x_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f___redArg___lam__0(lean_object* v_inst_425_, lean_object* v_m_426_, lean_object* v_k_427_, lean_object* v_v_428_){
_start:
{
lean_object* v___x_429_; uint8_t v___x_430_; 
v___x_429_ = ((lean_object*)(l_Lean_Name_fromJson_x3f___closed__0));
v___x_430_ = lean_string_dec_eq(v_k_427_, v___x_429_);
if (v___x_430_ == 0)
{
lean_object* v_n_431_; uint8_t v___x_432_; 
lean_inc_ref(v_k_427_);
v_n_431_ = l_String_toName(v_k_427_);
v___x_432_ = l_Lean_Name_isAnonymous(v_n_431_);
if (v___x_432_ == 0)
{
lean_object* v___x_433_; 
lean_dec_ref(v_k_427_);
v___x_433_ = lean_apply_1(v_inst_425_, v_v_428_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v_a_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_441_; 
lean_dec(v_n_431_);
lean_dec(v_m_426_);
v_a_434_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_441_ == 0)
{
v___x_436_ = v___x_433_;
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_a_434_);
lean_dec(v___x_433_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_439_; 
if (v_isShared_437_ == 0)
{
v___x_439_ = v___x_436_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_a_434_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
else
{
lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_450_; 
v_a_442_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_450_ == 0)
{
v___x_444_ = v___x_433_;
v_isShared_445_ = v_isSharedCheck_450_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_dec(v___x_433_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_450_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_446_; lean_object* v___x_448_; 
v___x_446_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_n_431_, v_a_442_, v_m_426_);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 0, v___x_446_);
v___x_448_ = v___x_444_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v___x_446_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
}
else
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
lean_dec(v_n_431_);
lean_dec(v_v_428_);
lean_dec(v_m_426_);
lean_dec_ref(v_inst_425_);
v___x_451_ = ((lean_object*)(l_Lean_Name_fromJson_x3f___closed__1));
v___x_452_ = lean_string_append(v___x_451_, v_k_427_);
lean_dec_ref(v_k_427_);
v___x_453_ = ((lean_object*)(l_Array_fromJson_x3f___redArg___closed__11));
v___x_454_ = lean_string_append(v___x_452_, v___x_453_);
v___x_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
return v___x_455_;
}
}
else
{
lean_object* v___x_456_; 
lean_dec_ref(v_k_427_);
v___x_456_ = lean_apply_1(v_inst_425_, v_v_428_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v_a_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_464_; 
lean_dec(v_m_426_);
v_a_457_ = lean_ctor_get(v___x_456_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_464_ == 0)
{
v___x_459_ = v___x_456_;
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_a_457_);
lean_dec(v___x_456_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_462_; 
if (v_isShared_460_ == 0)
{
v___x_462_ = v___x_459_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_a_457_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
else
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_474_; 
v_a_465_ = lean_ctor_get(v___x_456_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_474_ == 0)
{
v___x_467_ = v___x_456_;
v_isShared_468_ = v_isSharedCheck_474_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_456_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_474_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_472_; 
v___x_469_ = lean_box(0);
v___x_470_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_469_, v_a_465_, v_m_426_);
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 0, v___x_470_);
v___x_472_ = v___x_467_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v___x_470_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f___redArg(lean_object* v_inst_476_, lean_object* v_x_477_){
_start:
{
lean_object* v___x_478_; 
v___x_478_ = ((lean_object*)(l_Array_fromJson_x3f___redArg___closed__9));
if (lean_obj_tag(v_x_477_) == 5)
{
lean_object* v_kvPairs_479_; lean_object* v___f_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
v_kvPairs_479_ = lean_ctor_get(v_x_477_, 0);
lean_inc(v_kvPairs_479_);
lean_dec_ref_known(v_x_477_, 1);
v___f_480_ = lean_alloc_closure((void*)(l_Lean_NameMap_fromJson_x3f___redArg___lam__0), 4, 1);
lean_closure_set(v___f_480_, 0, v_inst_476_);
v___x_481_ = lean_box(1);
v___x_482_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v___x_478_, v___f_480_, v___x_481_, v_kvPairs_479_);
return v___x_482_;
}
else
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
lean_dec_ref(v_inst_476_);
v___x_483_ = ((lean_object*)(l_Lean_NameMap_fromJson_x3f___redArg___closed__0));
v___x_484_ = lean_unsigned_to_nat(80u);
v___x_485_ = l_Lean_Json_pretty(v_x_477_, v___x_484_);
v___x_486_ = lean_string_append(v___x_483_, v___x_485_);
lean_dec_ref(v___x_485_);
v___x_487_ = ((lean_object*)(l_Array_fromJson_x3f___redArg___closed__11));
v___x_488_ = lean_string_append(v___x_486_, v___x_487_);
v___x_489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
return v___x_489_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f(lean_object* v_00_u03b1_490_, lean_object* v_inst_491_, lean_object* v_x_492_){
_start:
{
lean_object* v___x_493_; 
v___x_493_ = l_Lean_NameMap_fromJson_x3f___redArg(v_inst_491_, v_x_492_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonNameMap___redArg(lean_object* v_inst_494_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = lean_alloc_closure((void*)(l_Lean_NameMap_fromJson_x3f), 3, 2);
lean_closure_set(v___x_495_, 0, lean_box(0));
lean_closure_set(v___x_495_, 1, v_inst_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonNameMap(lean_object* v_00_u03b1_496_, lean_object* v_inst_497_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = lean_alloc_closure((void*)(l_Lean_NameMap_fromJson_x3f), 3, 2);
lean_closure_set(v___x_498_, 0, lean_box(0));
lean_closure_set(v___x_498_, 1, v_inst_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___redArg___lam__0(lean_object* v_inst_500_, lean_object* v_n_501_, lean_object* v_k_502_, lean_object* v_v_503_){
_start:
{
lean_object* v___x_504_; uint8_t v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_504_ = ((lean_object*)(l_Lean_NameMap_toJson___redArg___lam__0___closed__0));
v___x_505_ = 1;
v___x_506_ = l_Lean_Name_toString(v_k_502_, v___x_505_);
v___x_507_ = lean_apply_1(v_inst_500_, v_v_503_);
v___x_508_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v___x_504_, v___x_506_, v___x_507_, v_n_501_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___redArg(lean_object* v_inst_509_, lean_object* v_m_510_){
_start:
{
lean_object* v___f_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v___f_511_ = lean_alloc_closure((void*)(l_Lean_NameMap_toJson___redArg___lam__0), 4, 1);
lean_closure_set(v___f_511_, 0, v_inst_509_);
v___x_512_ = lean_box(1);
v___x_513_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_511_, v___x_512_, v_m_510_);
v___x_514_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_514_, 0, v___x_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson(lean_object* v_00_u03b1_515_, lean_object* v_inst_516_, lean_object* v_m_517_){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = l_Lean_NameMap_toJson___redArg(v_inst_516_, v_m_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonNameMap___redArg(lean_object* v_inst_519_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = lean_alloc_closure((void*)(l_Lean_NameMap_toJson), 3, 2);
lean_closure_set(v___x_520_, 0, lean_box(0));
lean_closure_set(v___x_520_, 1, v_inst_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonNameMap(lean_object* v_00_u03b1_521_, lean_object* v_inst_522_){
_start:
{
lean_object* v___x_523_; 
v___x_523_ = lean_alloc_closure((void*)(l_Lean_NameMap_toJson), 3, 2);
lean_closure_set(v___x_523_, 0, lean_box(0));
lean_closure_set(v___x_523_, 1, v_inst_522_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_bignumFromJson_x3f(lean_object* v_j_525_){
_start:
{
lean_object* v___x_526_; 
lean_inc(v_j_525_);
v___x_526_ = l_Lean_Json_getStr_x3f(v_j_525_);
if (lean_obj_tag(v___x_526_) == 0)
{
lean_object* v_a_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_534_; 
lean_dec(v_j_525_);
v_a_527_ = lean_ctor_get(v___x_526_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_534_ == 0)
{
v___x_529_ = v___x_526_;
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_a_527_);
lean_dec(v___x_526_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_532_; 
if (v_isShared_530_ == 0)
{
v___x_532_ = v___x_529_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_a_527_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
else
{
lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_553_; 
v_a_535_ = lean_ctor_get(v___x_526_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_553_ == 0)
{
v___x_537_ = v___x_526_;
v_isShared_538_ = v_isSharedCheck_553_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_dec(v___x_526_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_553_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_539_; 
v___x_539_ = l_Lean_Syntax_decodeNatLitVal_x3f(v_a_535_);
lean_dec(v_a_535_);
if (lean_obj_tag(v___x_539_) == 1)
{
lean_object* v_val_540_; lean_object* v___x_542_; 
lean_dec(v_j_525_);
v_val_540_ = lean_ctor_get(v___x_539_, 0);
lean_inc(v_val_540_);
lean_dec_ref_known(v___x_539_, 1);
if (v_isShared_538_ == 0)
{
lean_ctor_set(v___x_537_, 0, v_val_540_);
v___x_542_ = v___x_537_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_val_540_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
else
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_551_; 
lean_dec(v___x_539_);
v___x_544_ = ((lean_object*)(l_Lean_bignumFromJson_x3f___closed__0));
v___x_545_ = lean_unsigned_to_nat(80u);
v___x_546_ = l_Lean_Json_pretty(v_j_525_, v___x_545_);
v___x_547_ = lean_string_append(v___x_544_, v___x_546_);
lean_dec_ref(v___x_546_);
v___x_548_ = ((lean_object*)(l_Array_fromJson_x3f___redArg___closed__11));
v___x_549_ = lean_string_append(v___x_547_, v___x_548_);
if (v_isShared_538_ == 0)
{
lean_ctor_set_tag(v___x_537_, 0);
lean_ctor_set(v___x_537_, 0, v___x_549_);
v___x_551_ = v___x_537_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_549_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_bignumToJson(lean_object* v_n_554_){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_555_ = l_Nat_reprFast(v_n_554_);
v___x_556_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
return v___x_556_;
}
}
static lean_object* _init_l_USize_fromJson_x3f___closed__0(void){
_start:
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_557_ = l_System_Platform_numBits;
v___x_558_ = lean_unsigned_to_nat(2u);
v___x_559_ = lean_nat_pow(v___x_558_, v___x_557_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_USize_fromJson_x3f(lean_object* v_j_562_){
_start:
{
lean_object* v___x_563_; 
lean_inc(v_j_562_);
v___x_563_ = l_Lean_bignumFromJson_x3f(v_j_562_);
if (lean_obj_tag(v___x_563_) == 0)
{
lean_object* v_a_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_571_; 
lean_dec(v_j_562_);
v_a_564_ = lean_ctor_get(v___x_563_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_563_);
if (v_isSharedCheck_571_ == 0)
{
v___x_566_ = v___x_563_;
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_a_564_);
lean_dec(v___x_563_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_569_; 
if (v_isShared_567_ == 0)
{
v___x_569_ = v___x_566_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_a_564_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
}
else
{
lean_object* v_a_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_592_; 
v_a_572_ = lean_ctor_get(v___x_563_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_563_);
if (v_isSharedCheck_592_ == 0)
{
v___x_574_ = v___x_563_;
v_isShared_575_ = v_isSharedCheck_592_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_a_572_);
lean_dec(v___x_563_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_592_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_576_; uint8_t v___x_577_; 
v___x_576_ = lean_obj_once(&l_USize_fromJson_x3f___closed__0, &l_USize_fromJson_x3f___closed__0_once, _init_l_USize_fromJson_x3f___closed__0);
v___x_577_ = lean_nat_dec_le(v___x_576_, v_a_572_);
if (v___x_577_ == 0)
{
size_t v___x_578_; lean_object* v___x_579_; lean_object* v___x_581_; 
lean_dec(v_j_562_);
v___x_578_ = lean_usize_of_nat(v_a_572_);
lean_dec(v_a_572_);
v___x_579_ = lean_box_usize(v___x_578_);
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 0, v___x_579_);
v___x_581_ = v___x_574_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v___x_579_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
else
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_590_; 
lean_dec(v_a_572_);
v___x_583_ = ((lean_object*)(l_USize_fromJson_x3f___closed__1));
v___x_584_ = lean_unsigned_to_nat(80u);
v___x_585_ = l_Lean_Json_pretty(v_j_562_, v___x_584_);
v___x_586_ = lean_string_append(v___x_583_, v___x_585_);
lean_dec_ref(v___x_585_);
v___x_587_ = ((lean_object*)(l_USize_fromJson_x3f___closed__2));
v___x_588_ = lean_string_append(v___x_586_, v___x_587_);
if (v_isShared_575_ == 0)
{
lean_ctor_set_tag(v___x_574_, 0);
lean_ctor_set(v___x_574_, 0, v___x_588_);
v___x_590_ = v___x_574_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 1, 0);
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
}
LEAN_EXPORT lean_object* l_Lean_instToJsonUSize___lam__0(size_t v_v_595_){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_596_ = lean_usize_to_nat(v_v_595_);
v___x_597_ = l_Lean_bignumToJson(v___x_596_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonUSize___lam__0___boxed(lean_object* v_v_598_){
_start:
{
size_t v_v_boxed_599_; lean_object* v_res_600_; 
v_v_boxed_599_ = lean_unbox_usize(v_v_598_);
lean_dec(v_v_598_);
v_res_600_ = l_Lean_instToJsonUSize___lam__0(v_v_boxed_599_);
return v_res_600_;
}
}
static lean_object* _init_l_UInt64_fromJson_x3f___closed__0(void){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = lean_cstr_to_nat("18446744073709551616");
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_UInt64_fromJson_x3f(lean_object* v_j_605_){
_start:
{
lean_object* v___x_606_; 
lean_inc(v_j_605_);
v___x_606_ = l_Lean_bignumFromJson_x3f(v_j_605_);
if (lean_obj_tag(v___x_606_) == 0)
{
lean_object* v_a_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_614_; 
lean_dec(v_j_605_);
v_a_607_ = lean_ctor_get(v___x_606_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_614_ == 0)
{
v___x_609_ = v___x_606_;
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_a_607_);
lean_dec(v___x_606_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_612_; 
if (v_isShared_610_ == 0)
{
v___x_612_ = v___x_609_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_a_607_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
else
{
lean_object* v_a_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_635_; 
v_a_615_ = lean_ctor_get(v___x_606_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_635_ == 0)
{
v___x_617_ = v___x_606_;
v_isShared_618_ = v_isSharedCheck_635_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_a_615_);
lean_dec(v___x_606_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_635_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_619_; uint8_t v___x_620_; 
v___x_619_ = lean_obj_once(&l_UInt64_fromJson_x3f___closed__0, &l_UInt64_fromJson_x3f___closed__0_once, _init_l_UInt64_fromJson_x3f___closed__0);
v___x_620_ = lean_nat_dec_le(v___x_619_, v_a_615_);
if (v___x_620_ == 0)
{
uint64_t v___x_621_; lean_object* v___x_622_; lean_object* v___x_624_; 
lean_dec(v_j_605_);
v___x_621_ = lean_uint64_of_nat(v_a_615_);
lean_dec(v_a_615_);
v___x_622_ = lean_box_uint64(v___x_621_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 0, v___x_622_);
v___x_624_ = v___x_617_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v___x_622_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
else
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_633_; 
lean_dec(v_a_615_);
v___x_626_ = ((lean_object*)(l_USize_fromJson_x3f___closed__1));
v___x_627_ = lean_unsigned_to_nat(80u);
v___x_628_ = l_Lean_Json_pretty(v_j_605_, v___x_627_);
v___x_629_ = lean_string_append(v___x_626_, v___x_628_);
lean_dec_ref(v___x_628_);
v___x_630_ = ((lean_object*)(l_UInt64_fromJson_x3f___closed__1));
v___x_631_ = lean_string_append(v___x_629_, v___x_630_);
if (v_isShared_618_ == 0)
{
lean_ctor_set_tag(v___x_617_, 0);
lean_ctor_set(v___x_617_, 0, v___x_631_);
v___x_633_ = v___x_617_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v___x_631_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonUInt64___lam__0(uint64_t v_v_638_){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_639_ = lean_uint64_to_nat(v_v_638_);
v___x_640_ = l_Lean_bignumToJson(v___x_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonUInt64___lam__0___boxed(lean_object* v_v_641_){
_start:
{
uint64_t v_v_boxed_642_; lean_object* v_res_643_; 
v_v_boxed_642_ = lean_unbox_uint64(v_v_641_);
lean_dec(v_v_641_);
v_res_643_ = l_Lean_instToJsonUInt64___lam__0(v_v_boxed_642_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Float_toJson(double v_x_646_){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = l_Lean_JsonNumber_fromFloat_x3f(v_x_646_);
if (lean_obj_tag(v___x_647_) == 0)
{
lean_object* v_val_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_655_; 
v_val_648_ = lean_ctor_get(v___x_647_, 0);
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_655_ == 0)
{
v___x_650_ = v___x_647_;
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_val_648_);
lean_dec(v___x_647_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_653_; 
if (v_isShared_651_ == 0)
{
lean_ctor_set_tag(v___x_650_, 3);
v___x_653_ = v___x_650_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(3, 1, 0);
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
else
{
lean_object* v_val_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_663_; 
v_val_656_ = lean_ctor_get(v___x_647_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_663_ == 0)
{
v___x_658_ = v___x_647_;
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_val_656_);
lean_dec(v___x_647_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_661_; 
if (v_isShared_659_ == 0)
{
lean_ctor_set_tag(v___x_658_, 2);
v___x_661_ = v___x_658_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_val_656_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Float_toJson___boxed(lean_object* v_x_664_){
_start:
{
double v_x_boxed_665_; lean_object* v_res_666_; 
v_x_boxed_665_ = lean_unbox_float(v_x_664_);
lean_dec_ref(v_x_664_);
v_res_666_ = l_Float_toJson(v_x_boxed_665_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l_Float_fromJson_x3f(lean_object* v_x_675_){
_start:
{
switch(lean_obj_tag(v_x_675_))
{
case 3:
{
lean_object* v_s_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_717_; 
v_s_678_ = lean_ctor_get(v_x_675_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v_x_675_);
if (v_isSharedCheck_717_ == 0)
{
v___x_680_ = v_x_675_;
v_isShared_681_ = v_isSharedCheck_717_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_s_678_);
lean_dec(v_x_675_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_717_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___x_682_; uint8_t v___x_683_; 
v___x_682_ = ((lean_object*)(l_Float_fromJson_x3f___closed__2));
v___x_683_ = lean_string_dec_eq(v_s_678_, v___x_682_);
if (v___x_683_ == 0)
{
lean_object* v___x_684_; uint8_t v___x_685_; 
v___x_684_ = ((lean_object*)(l_Float_fromJson_x3f___closed__3));
v___x_685_ = lean_string_dec_eq(v_s_678_, v___x_684_);
if (v___x_685_ == 0)
{
lean_object* v___x_686_; uint8_t v___x_687_; 
v___x_686_ = ((lean_object*)(l_Float_fromJson_x3f___closed__4));
v___x_687_ = lean_string_dec_eq(v_s_678_, v___x_686_);
lean_dec_ref(v_s_678_);
if (v___x_687_ == 0)
{
lean_del_object(v___x_680_);
goto v___jp_676_;
}
else
{
lean_object* v___x_688_; lean_object* v___x_689_; double v___x_690_; double v___x_691_; lean_object* v___x_692_; lean_object* v___x_694_; 
v___x_688_ = lean_unsigned_to_nat(0u);
v___x_689_ = lean_unsigned_to_nat(1u);
v___x_690_ = l_Float_ofScientific(v___x_688_, v___x_687_, v___x_689_);
v___x_691_ = lean_float_div(v___x_690_, v___x_690_);
v___x_692_ = lean_box_float(v___x_691_);
if (v_isShared_681_ == 0)
{
lean_ctor_set_tag(v___x_680_, 1);
lean_ctor_set(v___x_680_, 0, v___x_692_);
v___x_694_ = v___x_680_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_692_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
else
{
lean_object* v___x_696_; lean_object* v___x_697_; double v___x_698_; double v___x_699_; lean_object* v___x_700_; double v___x_701_; double v___x_702_; lean_object* v___x_703_; lean_object* v___x_705_; 
lean_dec_ref(v_s_678_);
v___x_696_ = lean_unsigned_to_nat(10u);
v___x_697_ = lean_unsigned_to_nat(1u);
v___x_698_ = l_Float_ofScientific(v___x_696_, v___x_685_, v___x_697_);
v___x_699_ = lean_float_negate(v___x_698_);
v___x_700_ = lean_unsigned_to_nat(0u);
v___x_701_ = l_Float_ofScientific(v___x_700_, v___x_685_, v___x_697_);
v___x_702_ = lean_float_div(v___x_699_, v___x_701_);
v___x_703_ = lean_box_float(v___x_702_);
if (v_isShared_681_ == 0)
{
lean_ctor_set_tag(v___x_680_, 1);
lean_ctor_set(v___x_680_, 0, v___x_703_);
v___x_705_ = v___x_680_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_703_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
else
{
lean_object* v___x_707_; lean_object* v___x_708_; double v___x_709_; lean_object* v___x_710_; double v___x_711_; double v___x_712_; lean_object* v___x_713_; lean_object* v___x_715_; 
lean_dec_ref(v_s_678_);
v___x_707_ = lean_unsigned_to_nat(10u);
v___x_708_ = lean_unsigned_to_nat(1u);
v___x_709_ = l_Float_ofScientific(v___x_707_, v___x_683_, v___x_708_);
v___x_710_ = lean_unsigned_to_nat(0u);
v___x_711_ = l_Float_ofScientific(v___x_710_, v___x_683_, v___x_708_);
v___x_712_ = lean_float_div(v___x_709_, v___x_711_);
v___x_713_ = lean_box_float(v___x_712_);
if (v_isShared_681_ == 0)
{
lean_ctor_set_tag(v___x_680_, 1);
lean_ctor_set(v___x_680_, 0, v___x_713_);
v___x_715_ = v___x_680_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_713_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
}
case 2:
{
lean_object* v_n_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_727_; 
v_n_718_ = lean_ctor_get(v_x_675_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v_x_675_);
if (v_isSharedCheck_727_ == 0)
{
v___x_720_ = v_x_675_;
v_isShared_721_ = v_isSharedCheck_727_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_n_718_);
lean_dec(v_x_675_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_727_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
double v___x_722_; lean_object* v___x_723_; lean_object* v___x_725_; 
v___x_722_ = l_Lean_JsonNumber_toFloat(v_n_718_);
v___x_723_ = lean_box_float(v___x_722_);
if (v_isShared_721_ == 0)
{
lean_ctor_set_tag(v___x_720_, 1);
lean_ctor_set(v___x_720_, 0, v___x_723_);
v___x_725_ = v___x_720_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v___x_723_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
default: 
{
lean_dec(v_x_675_);
goto v___jp_676_;
}
}
v___jp_676_:
{
lean_object* v___x_677_; 
v___x_677_ = ((lean_object*)(l_Float_fromJson_x3f___closed__1));
return v___x_677_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_fromJson_x3f(lean_object* v_x_731_){
_start:
{
switch(lean_obj_tag(v_x_731_))
{
case 4:
{
lean_object* v_elems_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_740_; 
v_elems_732_ = lean_ctor_get(v_x_731_, 0);
v_isSharedCheck_740_ = !lean_is_exclusive(v_x_731_);
if (v_isSharedCheck_740_ == 0)
{
v___x_734_ = v_x_731_;
v_isShared_735_ = v_isSharedCheck_740_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_elems_732_);
lean_dec(v_x_731_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_740_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_737_; 
if (v_isShared_735_ == 0)
{
lean_ctor_set_tag(v___x_734_, 0);
v___x_737_ = v___x_734_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_elems_732_);
v___x_737_ = v_reuseFailAlloc_739_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
lean_object* v___x_738_; 
v___x_738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_738_, 0, v___x_737_);
return v___x_738_;
}
}
}
case 5:
{
lean_object* v_kvPairs_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_749_; 
v_kvPairs_741_ = lean_ctor_get(v_x_731_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v_x_731_);
if (v_isSharedCheck_749_ == 0)
{
v___x_743_ = v_x_731_;
v_isShared_744_ = v_isSharedCheck_749_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_kvPairs_741_);
lean_dec(v_x_731_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_749_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_746_; 
if (v_isShared_744_ == 0)
{
lean_ctor_set_tag(v___x_743_, 1);
v___x_746_ = v___x_743_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_kvPairs_741_);
v___x_746_ = v_reuseFailAlloc_748_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
lean_object* v___x_747_; 
v___x_747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_747_, 0, v___x_746_);
return v___x_747_;
}
}
}
default: 
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_750_ = ((lean_object*)(l_Lean_Json_Structured_fromJson_x3f___closed__0));
v___x_751_ = lean_unsigned_to_nat(80u);
v___x_752_ = l_Lean_Json_pretty(v_x_731_, v___x_751_);
v___x_753_ = lean_string_append(v___x_750_, v___x_752_);
lean_dec_ref(v___x_752_);
v___x_754_ = ((lean_object*)(l_Array_fromJson_x3f___redArg___closed__11));
v___x_755_ = lean_string_append(v___x_753_, v___x_754_);
v___x_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_756_, 0, v___x_755_);
return v___x_756_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_toJson(lean_object* v_x_759_){
_start:
{
if (lean_obj_tag(v_x_759_) == 0)
{
lean_object* v_elems_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_767_; 
v_elems_760_ = lean_ctor_get(v_x_759_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v_x_759_);
if (v_isSharedCheck_767_ == 0)
{
v___x_762_ = v_x_759_;
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_elems_760_);
lean_dec(v_x_759_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_765_; 
if (v_isShared_763_ == 0)
{
lean_ctor_set_tag(v___x_762_, 4);
v___x_765_ = v___x_762_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_elems_760_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
}
else
{
lean_object* v_kvPairs_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_775_; 
v_kvPairs_768_ = lean_ctor_get(v_x_759_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v_x_759_);
if (v_isSharedCheck_775_ == 0)
{
v___x_770_ = v_x_759_;
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_kvPairs_768_);
lean_dec(v_x_759_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_773_; 
if (v_isShared_771_ == 0)
{
lean_ctor_set_tag(v___x_770_, 5);
v___x_773_ = v___x_770_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_kvPairs_768_);
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
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___redArg(lean_object* v_inst_778_, lean_object* v_v_779_){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = lean_apply_1(v_inst_778_, v_v_779_);
v___x_781_ = l_Lean_Json_Structured_fromJson_x3f(v___x_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f(lean_object* v_00_u03b1_782_, lean_object* v_inst_783_, lean_object* v_v_784_){
_start:
{
lean_object* v___x_785_; 
v___x_785_ = l_Lean_Json_toStructured_x3f___redArg(v_inst_783_, v_v_784_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___redArg(lean_object* v_j_786_, lean_object* v_inst_787_, lean_object* v_k_788_){
_start:
{
lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_789_ = l_Lean_Json_getObjValD(v_j_786_, v_k_788_);
v___x_790_ = lean_apply_1(v_inst_787_, v___x_789_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___redArg___boxed(lean_object* v_j_791_, lean_object* v_inst_792_, lean_object* v_k_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_791_, v_inst_792_, v_k_793_);
lean_dec_ref(v_k_793_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f(lean_object* v_j_795_, lean_object* v_00_u03b1_796_, lean_object* v_inst_797_, lean_object* v_k_798_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_795_, v_inst_797_, v_k_798_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___boxed(lean_object* v_j_800_, lean_object* v_00_u03b1_801_, lean_object* v_inst_802_, lean_object* v_k_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Lean_Json_getObjValAs_x3f(v_j_800_, v_00_u03b1_801_, v_inst_802_, v_k_803_);
lean_dec_ref(v_k_803_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_setObjValAs_x21___redArg(lean_object* v_j_805_, lean_object* v_inst_806_, lean_object* v_k_807_, lean_object* v_v_808_){
_start:
{
lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_809_ = lean_apply_1(v_inst_806_, v_v_808_);
v___x_810_ = l_Lean_Json_setObjVal_x21(v_j_805_, v_k_807_, v___x_809_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_setObjValAs_x21(lean_object* v_j_811_, lean_object* v_00_u03b1_812_, lean_object* v_inst_813_, lean_object* v_k_814_, lean_object* v_v_815_){
_start:
{
lean_object* v___x_816_; 
v___x_816_ = l_Lean_Json_setObjValAs_x21___redArg(v_j_811_, v_inst_813_, v_k_814_, v_v_815_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___redArg(lean_object* v_inst_817_, lean_object* v_k_818_, lean_object* v_x_819_){
_start:
{
if (lean_obj_tag(v_x_819_) == 0)
{
lean_object* v___x_820_; 
lean_dec_ref(v_k_818_);
lean_dec_ref(v_inst_817_);
v___x_820_ = lean_box(0);
return v___x_820_;
}
else
{
lean_object* v_val_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v_val_821_ = lean_ctor_get(v_x_819_, 0);
lean_inc(v_val_821_);
lean_dec_ref_known(v_x_819_, 1);
v___x_822_ = lean_apply_1(v_inst_817_, v_val_821_);
v___x_823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_823_, 0, v_k_818_);
lean_ctor_set(v___x_823_, 1, v___x_822_);
v___x_824_ = lean_box(0);
v___x_825_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_825_, 0, v___x_823_);
lean_ctor_set(v___x_825_, 1, v___x_824_);
return v___x_825_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt(lean_object* v_00_u03b1_826_, lean_object* v_inst_827_, lean_object* v_k_828_, lean_object* v_x_829_){
_start:
{
lean_object* v___x_830_; 
v___x_830_ = l_Lean_Json_opt___redArg(v_inst_827_, v_k_828_, v_x_829_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getTag_x3f(lean_object* v_x_831_){
_start:
{
switch(lean_obj_tag(v_x_831_))
{
case 3:
{
lean_object* v_s_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_839_; 
v_s_832_ = lean_ctor_get(v_x_831_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v_x_831_);
if (v_isSharedCheck_839_ == 0)
{
v___x_834_ = v_x_831_;
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_s_832_);
lean_dec(v_x_831_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_837_; 
if (v_isShared_835_ == 0)
{
lean_ctor_set_tag(v___x_834_, 1);
v___x_837_ = v___x_834_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_s_832_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
case 5:
{
lean_object* v_kvPairs_840_; lean_object* v___y_842_; 
v_kvPairs_840_ = lean_ctor_get(v_x_831_, 0);
lean_inc(v_kvPairs_840_);
lean_dec_ref_known(v_x_831_, 1);
if (lean_obj_tag(v_kvPairs_840_) == 0)
{
lean_object* v_size_847_; 
v_size_847_ = lean_ctor_get(v_kvPairs_840_, 0);
lean_inc(v_size_847_);
v___y_842_ = v_size_847_;
goto v___jp_841_;
}
else
{
lean_object* v___x_848_; 
v___x_848_ = lean_unsigned_to_nat(0u);
v___y_842_ = v___x_848_;
goto v___jp_841_;
}
v___jp_841_:
{
lean_object* v___x_843_; uint8_t v___x_844_; 
v___x_843_ = lean_unsigned_to_nat(1u);
v___x_844_ = lean_nat_dec_eq(v___y_842_, v___x_843_);
lean_dec(v___y_842_);
if (v___x_844_ == 0)
{
lean_object* v___x_845_; 
lean_dec(v_kvPairs_840_);
v___x_845_ = lean_box(0);
return v___x_845_;
}
else
{
lean_object* v___x_846_; 
v___x_846_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_kvPairs_840_);
lean_dec(v_kvPairs_840_);
return v___x_846_;
}
}
}
default: 
{
lean_object* v___x_849_; 
lean_dec(v_x_831_);
v___x_849_ = lean_box(0);
return v___x_849_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Json_parseTagged_spec__0(lean_object* v_a_850_, lean_object* v_as_851_, size_t v_sz_852_, size_t v_i_853_, lean_object* v_b_854_){
_start:
{
uint8_t v___x_855_; 
v___x_855_ = lean_usize_dec_lt(v_i_853_, v_sz_852_);
if (v___x_855_ == 0)
{
lean_object* v___x_856_; 
lean_dec(v_a_850_);
v___x_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_856_, 0, v_b_854_);
return v___x_856_;
}
else
{
lean_object* v_a_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
v_a_857_ = lean_array_uget_borrowed(v_as_851_, v_i_853_);
v___x_858_ = l_Lean_Name_getString_x21(v_a_857_);
lean_inc(v_a_850_);
v___x_859_ = l_Lean_Json_getObjVal_x3f(v_a_850_, v___x_858_);
lean_dec_ref(v___x_858_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v_a_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_867_; 
lean_dec_ref(v_b_854_);
lean_dec(v_a_850_);
v_a_860_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_867_ == 0)
{
v___x_862_ = v___x_859_;
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_dec(v___x_859_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_865_; 
if (v_isShared_863_ == 0)
{
v___x_865_ = v___x_862_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_a_860_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
else
{
lean_object* v_a_868_; lean_object* v___x_869_; size_t v___x_870_; size_t v___x_871_; 
v_a_868_ = lean_ctor_get(v___x_859_, 0);
lean_inc(v_a_868_);
lean_dec_ref_known(v___x_859_, 1);
v___x_869_ = lean_array_push(v_b_854_, v_a_868_);
v___x_870_ = ((size_t)1ULL);
v___x_871_ = lean_usize_add(v_i_853_, v___x_870_);
v_i_853_ = v___x_871_;
v_b_854_ = v___x_869_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Json_parseTagged_spec__0___boxed(lean_object* v_a_873_, lean_object* v_as_874_, lean_object* v_sz_875_, lean_object* v_i_876_, lean_object* v_b_877_){
_start:
{
size_t v_sz_boxed_878_; size_t v_i_boxed_879_; lean_object* v_res_880_; 
v_sz_boxed_878_ = lean_unbox_usize(v_sz_875_);
lean_dec(v_sz_875_);
v_i_boxed_879_ = lean_unbox_usize(v_i_876_);
lean_dec(v_i_876_);
v_res_880_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Json_parseTagged_spec__0(v_a_873_, v_as_874_, v_sz_boxed_878_, v_i_boxed_879_, v_b_877_);
lean_dec_ref(v_as_874_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_parseTagged(lean_object* v_json_888_, lean_object* v_tag_889_, lean_object* v_nFields_890_, lean_object* v_fieldNames_x3f_891_){
_start:
{
lean_object* v___x_892_; uint8_t v___x_893_; 
v___x_892_ = lean_unsigned_to_nat(0u);
v___x_893_ = lean_nat_dec_eq(v_nFields_890_, v___x_892_);
if (v___x_893_ == 0)
{
lean_object* v___x_894_; 
v___x_894_ = l_Lean_Json_getObjVal_x3f(v_json_888_, v_tag_889_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_902_; 
lean_dec(v_nFields_890_);
v_a_895_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_902_ == 0)
{
v___x_897_ = v___x_894_;
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_894_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_900_; 
if (v_isShared_898_ == 0)
{
v___x_900_ = v___x_897_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_a_895_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
else
{
if (lean_obj_tag(v_fieldNames_x3f_891_) == 0)
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_933_; 
v_a_903_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_933_ == 0)
{
v___x_905_ = v___x_894_;
v_isShared_906_ = v_isSharedCheck_933_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_a_903_);
lean_dec(v___x_894_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_933_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_907_; uint8_t v___x_908_; 
v___x_907_ = lean_unsigned_to_nat(1u);
v___x_908_ = lean_nat_dec_eq(v_nFields_890_, v___x_907_);
if (v___x_908_ == 0)
{
lean_object* v___x_909_; 
lean_del_object(v___x_905_);
v___x_909_ = l_Lean_Json_getArr_x3f(v_a_903_);
if (lean_obj_tag(v___x_909_) == 0)
{
lean_dec(v_nFields_890_);
return v___x_909_;
}
else
{
lean_object* v_a_910_; lean_object* v___x_911_; uint8_t v___x_912_; 
v_a_910_ = lean_ctor_get(v___x_909_, 0);
lean_inc(v_a_910_);
v___x_911_ = lean_array_get_size(v_a_910_);
lean_dec(v_a_910_);
v___x_912_ = lean_nat_dec_eq(v___x_911_, v_nFields_890_);
if (v___x_912_ == 0)
{
lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_926_; 
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_909_);
if (v_isSharedCheck_926_ == 0)
{
lean_object* v_unused_927_; 
v_unused_927_ = lean_ctor_get(v___x_909_, 0);
lean_dec(v_unused_927_);
v___x_914_ = v___x_909_;
v_isShared_915_ = v_isSharedCheck_926_;
goto v_resetjp_913_;
}
else
{
lean_dec(v___x_909_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_926_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_924_; 
v___x_916_ = ((lean_object*)(l_Lean_Json_parseTagged___closed__0));
v___x_917_ = l_Nat_reprFast(v___x_911_);
v___x_918_ = lean_string_append(v___x_916_, v___x_917_);
lean_dec_ref(v___x_917_);
v___x_919_ = ((lean_object*)(l_Lean_Json_parseTagged___closed__1));
v___x_920_ = lean_string_append(v___x_918_, v___x_919_);
v___x_921_ = l_Nat_reprFast(v_nFields_890_);
v___x_922_ = lean_string_append(v___x_920_, v___x_921_);
lean_dec_ref(v___x_921_);
if (v_isShared_915_ == 0)
{
lean_ctor_set_tag(v___x_914_, 0);
lean_ctor_set(v___x_914_, 0, v___x_922_);
v___x_924_ = v___x_914_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_922_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
else
{
lean_dec(v_nFields_890_);
return v___x_909_;
}
}
}
else
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_931_; 
lean_dec(v_nFields_890_);
v___x_928_ = lean_mk_empty_array_with_capacity(v___x_907_);
v___x_929_ = lean_array_push(v___x_928_, v_a_903_);
if (v_isShared_906_ == 0)
{
lean_ctor_set(v___x_905_, 0, v___x_929_);
v___x_931_ = v___x_905_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v___x_929_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
else
{
lean_object* v_a_934_; lean_object* v_val_935_; lean_object* v_fields_936_; size_t v_sz_937_; size_t v___x_938_; lean_object* v___x_939_; 
lean_dec(v_nFields_890_);
v_a_934_ = lean_ctor_get(v___x_894_, 0);
lean_inc(v_a_934_);
lean_dec_ref_known(v___x_894_, 1);
v_val_935_ = lean_ctor_get(v_fieldNames_x3f_891_, 0);
v_fields_936_ = ((lean_object*)(l_Lean_Json_parseTagged___closed__2));
v_sz_937_ = lean_array_size(v_val_935_);
v___x_938_ = ((size_t)0ULL);
v___x_939_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Json_parseTagged_spec__0(v_a_934_, v_val_935_, v_sz_937_, v___x_938_, v_fields_936_);
return v___x_939_;
}
}
}
else
{
lean_object* v___x_940_; 
lean_dec(v_nFields_890_);
v___x_940_ = l_Lean_Json_getStr_x3f(v_json_888_);
if (lean_obj_tag(v___x_940_) == 0)
{
lean_object* v_a_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_948_; 
v_a_941_ = lean_ctor_get(v___x_940_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_948_ == 0)
{
v___x_943_ = v___x_940_;
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_dec(v___x_940_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_946_; 
if (v_isShared_944_ == 0)
{
v___x_946_ = v___x_943_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_a_941_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
else
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_963_; 
v_a_949_ = lean_ctor_get(v___x_940_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_963_ == 0)
{
v___x_951_ = v___x_940_;
v_isShared_952_ = v_isSharedCheck_963_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_940_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_963_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
uint8_t v___x_953_; 
v___x_953_ = lean_string_dec_eq(v_a_949_, v_tag_889_);
if (v___x_953_ == 0)
{
lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_960_; 
v___x_954_ = ((lean_object*)(l_Lean_Json_parseTagged___closed__3));
v___x_955_ = lean_string_append(v___x_954_, v_a_949_);
lean_dec(v_a_949_);
v___x_956_ = ((lean_object*)(l_Lean_Json_parseTagged___closed__1));
v___x_957_ = lean_string_append(v___x_955_, v___x_956_);
v___x_958_ = lean_string_append(v___x_957_, v_tag_889_);
if (v_isShared_952_ == 0)
{
lean_ctor_set_tag(v___x_951_, 0);
lean_ctor_set(v___x_951_, 0, v___x_958_);
v___x_960_ = v___x_951_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v___x_958_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
else
{
lean_object* v___x_962_; 
lean_del_object(v___x_951_);
lean_dec(v_a_949_);
v___x_962_ = ((lean_object*)(l_Lean_Json_parseTagged___closed__4));
return v___x_962_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_parseTagged___boxed(lean_object* v_json_964_, lean_object* v_tag_965_, lean_object* v_nFields_966_, lean_object* v_fieldNames_x3f_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Lean_Json_parseTagged(v_json_964_, v_tag_965_, v_nFields_966_, v_fieldNames_x3f_967_);
lean_dec(v_fieldNames_x3f_967_);
lean_dec_ref(v_tag_965_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_parseCtorFields_spec__0(lean_object* v_a_969_, size_t v_sz_970_, size_t v_i_971_, lean_object* v_bs_972_){
_start:
{
uint8_t v___x_973_; 
v___x_973_ = lean_usize_dec_lt(v_i_971_, v_sz_970_);
if (v___x_973_ == 0)
{
lean_object* v___x_974_; 
lean_dec(v_a_969_);
v___x_974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_974_, 0, v_bs_972_);
return v___x_974_;
}
else
{
lean_object* v_v_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v_v_975_ = lean_array_uget_borrowed(v_bs_972_, v_i_971_);
v___x_976_ = l_Lean_Name_getString_x21(v_v_975_);
lean_inc(v_a_969_);
v___x_977_ = l_Lean_Json_getObjVal_x3f(v_a_969_, v___x_976_);
lean_dec_ref(v___x_976_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v_a_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_985_; 
lean_dec_ref(v_bs_972_);
lean_dec(v_a_969_);
v_a_978_ = lean_ctor_get(v___x_977_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_985_ == 0)
{
v___x_980_ = v___x_977_;
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_a_978_);
lean_dec(v___x_977_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_983_; 
if (v_isShared_981_ == 0)
{
v___x_983_ = v___x_980_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_a_978_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
else
{
lean_object* v_a_986_; lean_object* v___x_987_; lean_object* v_bs_x27_988_; size_t v___x_989_; size_t v___x_990_; lean_object* v___x_991_; 
v_a_986_ = lean_ctor_get(v___x_977_, 0);
lean_inc(v_a_986_);
lean_dec_ref_known(v___x_977_, 1);
v___x_987_ = lean_unsigned_to_nat(0u);
v_bs_x27_988_ = lean_array_uset(v_bs_972_, v_i_971_, v___x_987_);
v___x_989_ = ((size_t)1ULL);
v___x_990_ = lean_usize_add(v_i_971_, v___x_989_);
v___x_991_ = lean_array_uset(v_bs_x27_988_, v_i_971_, v_a_986_);
v_i_971_ = v___x_990_;
v_bs_972_ = v___x_991_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_parseCtorFields_spec__0___boxed(lean_object* v_a_993_, lean_object* v_sz_994_, lean_object* v_i_995_, lean_object* v_bs_996_){
_start:
{
size_t v_sz_boxed_997_; size_t v_i_boxed_998_; lean_object* v_res_999_; 
v_sz_boxed_997_ = lean_unbox_usize(v_sz_994_);
lean_dec(v_sz_994_);
v_i_boxed_998_ = lean_unbox_usize(v_i_995_);
lean_dec(v_i_995_);
v_res_999_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_parseCtorFields_spec__0(v_a_993_, v_sz_boxed_997_, v_i_boxed_998_, v_bs_996_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_parseCtorFields(lean_object* v_json_1000_, lean_object* v_tag_1001_, lean_object* v_nFields_1002_, lean_object* v_fieldNames_x3f_1003_){
_start:
{
lean_object* v___x_1004_; 
v___x_1004_ = l_Lean_Json_getObjVal_x3f(v_json_1000_, v_tag_1001_);
if (lean_obj_tag(v___x_1004_) == 0)
{
lean_object* v_a_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1012_; 
lean_dec(v_fieldNames_x3f_1003_);
lean_dec(v_nFields_1002_);
v_a_1005_ = lean_ctor_get(v___x_1004_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_1007_ = v___x_1004_;
v_isShared_1008_ = v_isSharedCheck_1012_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_a_1005_);
lean_dec(v___x_1004_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1012_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v___x_1010_; 
if (v_isShared_1008_ == 0)
{
v___x_1010_ = v___x_1007_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v_a_1005_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
}
else
{
if (lean_obj_tag(v_fieldNames_x3f_1003_) == 0)
{
lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1043_; 
v_a_1013_ = lean_ctor_get(v___x_1004_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1015_ = v___x_1004_;
v_isShared_1016_ = v_isSharedCheck_1043_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v___x_1004_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1043_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1017_; uint8_t v___x_1018_; 
v___x_1017_ = lean_unsigned_to_nat(1u);
v___x_1018_ = lean_nat_dec_eq(v_nFields_1002_, v___x_1017_);
if (v___x_1018_ == 0)
{
lean_object* v___x_1019_; 
lean_del_object(v___x_1015_);
v___x_1019_ = l_Lean_Json_getArr_x3f(v_a_1013_);
if (lean_obj_tag(v___x_1019_) == 0)
{
lean_dec(v_nFields_1002_);
return v___x_1019_;
}
else
{
lean_object* v_a_1020_; lean_object* v___x_1021_; uint8_t v___x_1022_; 
v_a_1020_ = lean_ctor_get(v___x_1019_, 0);
lean_inc(v_a_1020_);
v___x_1021_ = lean_array_get_size(v_a_1020_);
lean_dec(v_a_1020_);
v___x_1022_ = lean_nat_dec_eq(v___x_1021_, v_nFields_1002_);
if (v___x_1022_ == 0)
{
lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1036_; 
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1036_ == 0)
{
lean_object* v_unused_1037_; 
v_unused_1037_ = lean_ctor_get(v___x_1019_, 0);
lean_dec(v_unused_1037_);
v___x_1024_ = v___x_1019_;
v_isShared_1025_ = v_isSharedCheck_1036_;
goto v_resetjp_1023_;
}
else
{
lean_dec(v___x_1019_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1036_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1034_; 
v___x_1026_ = ((lean_object*)(l_Lean_Json_parseTagged___closed__0));
v___x_1027_ = l_Nat_reprFast(v___x_1021_);
v___x_1028_ = lean_string_append(v___x_1026_, v___x_1027_);
lean_dec_ref(v___x_1027_);
v___x_1029_ = ((lean_object*)(l_Lean_Json_parseTagged___closed__1));
v___x_1030_ = lean_string_append(v___x_1028_, v___x_1029_);
v___x_1031_ = l_Nat_reprFast(v_nFields_1002_);
v___x_1032_ = lean_string_append(v___x_1030_, v___x_1031_);
lean_dec_ref(v___x_1031_);
if (v_isShared_1025_ == 0)
{
lean_ctor_set_tag(v___x_1024_, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1032_);
v___x_1034_ = v___x_1024_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v___x_1032_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
}
}
}
else
{
lean_dec(v_nFields_1002_);
return v___x_1019_;
}
}
}
else
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1041_; 
lean_dec(v_nFields_1002_);
v___x_1038_ = lean_mk_empty_array_with_capacity(v___x_1017_);
v___x_1039_ = lean_array_push(v___x_1038_, v_a_1013_);
if (v_isShared_1016_ == 0)
{
lean_ctor_set(v___x_1015_, 0, v___x_1039_);
v___x_1041_ = v___x_1015_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1039_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
}
else
{
lean_object* v_a_1044_; lean_object* v_val_1045_; size_t v_sz_1046_; size_t v___x_1047_; lean_object* v___x_1048_; 
lean_dec(v_nFields_1002_);
v_a_1044_ = lean_ctor_get(v___x_1004_, 0);
lean_inc(v_a_1044_);
lean_dec_ref_known(v___x_1004_, 1);
v_val_1045_ = lean_ctor_get(v_fieldNames_x3f_1003_, 0);
lean_inc(v_val_1045_);
lean_dec_ref_known(v_fieldNames_x3f_1003_, 1);
v_sz_1046_ = lean_array_size(v_val_1045_);
v___x_1047_ = ((size_t)0ULL);
v___x_1048_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_parseCtorFields_spec__0(v_a_1044_, v_sz_1046_, v___x_1047_, v_val_1045_);
return v___x_1048_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_parseCtorFields___boxed(lean_object* v_json_1049_, lean_object* v_tag_1050_, lean_object* v_nFields_1051_, lean_object* v_fieldNames_x3f_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_Lean_Json_parseCtorFields(v_json_1049_, v_tag_1050_, v_nFields_1051_, v_fieldNames_x3f_1052_);
lean_dec_ref(v_tag_1050_);
return v_res_1053_;
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
