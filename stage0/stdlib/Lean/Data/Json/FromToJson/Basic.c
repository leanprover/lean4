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
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Except_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_instMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_instMonad___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_pure(lean_object*, lean_object*, lean_object*);
lean_object* l_Except_instMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_String_toName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* l_String_toSlice(lean_object*);
lean_object* l_Lean_Json_getObjVal_x3f(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Json_getArr_x3f(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Name_getString_x21(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* l_Function_comp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_compare___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_decodeNatLitVal_x3f(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_Json_setObjVal_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getInt_x3f(lean_object*);
lean_object* l_Lean_Json_getBool_x3f___boxed(lean_object*);
lean_object* l_Lean_JsonNumber_fromFloat_x3f(double);
lean_object* l_Lean_JsonNumber_fromInt(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
extern lean_object* l_System_Platform_numBits;
lean_object* lean_nat_pow(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
double lean_float_div(double, double);
double lean_float_negate(double);
double l_Lean_JsonNumber_toFloat(lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
lean_object* l_Lean_Json_getNat_x3f(lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_Json_getNum_x3f(lean_object*);
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
static const lean_closure_object l_Lean_Array_fromJson_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_instMonad___redArg___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Array_fromJson_x3f___redArg___closed__0 = (const lean_object*)&l_Lean_Array_fromJson_x3f___redArg___closed__0_value;
static const lean_closure_object l_Lean_Array_fromJson_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_instMonad___redArg___lam__1, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Array_fromJson_x3f___redArg___closed__1 = (const lean_object*)&l_Lean_Array_fromJson_x3f___redArg___closed__1_value;
static const lean_closure_object l_Lean_Array_fromJson_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_instMonad___redArg___lam__2___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Array_fromJson_x3f___redArg___closed__2 = (const lean_object*)&l_Lean_Array_fromJson_x3f___redArg___closed__2_value;
static const lean_closure_object l_Lean_Array_fromJson_x3f___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_instMonad___redArg___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Array_fromJson_x3f___redArg___closed__3 = (const lean_object*)&l_Lean_Array_fromJson_x3f___redArg___closed__3_value;
static const lean_closure_object l_Lean_Array_fromJson_x3f___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_map, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Array_fromJson_x3f___redArg___closed__4 = (const lean_object*)&l_Lean_Array_fromJson_x3f___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Array_fromJson_x3f___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Array_fromJson_x3f___redArg___closed__4_value),((lean_object*)&l_Lean_Array_fromJson_x3f___redArg___closed__0_value)}};
static const lean_object* l_Lean_Array_fromJson_x3f___redArg___closed__5 = (const lean_object*)&l_Lean_Array_fromJson_x3f___redArg___closed__5_value;
static const lean_closure_object l_Lean_Array_fromJson_x3f___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_pure, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Array_fromJson_x3f___redArg___closed__6 = (const lean_object*)&l_Lean_Array_fromJson_x3f___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Array_fromJson_x3f___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Array_fromJson_x3f___redArg___closed__5_value),((lean_object*)&l_Lean_Array_fromJson_x3f___redArg___closed__6_value),((lean_object*)&l_Lean_Array_fromJson_x3f___redArg___closed__1_value),((lean_object*)&l_Lean_Array_fromJson_x3f___redArg___closed__2_value),((lean_object*)&l_Lean_Array_fromJson_x3f___redArg___closed__3_value)}};
static const lean_object* l_Lean_Array_fromJson_x3f___redArg___closed__7 = (const lean_object*)&l_Lean_Array_fromJson_x3f___redArg___closed__7_value;
static const lean_closure_object l_Lean_Array_fromJson_x3f___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_bind, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Array_fromJson_x3f___redArg___closed__8 = (const lean_object*)&l_Lean_Array_fromJson_x3f___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Array_fromJson_x3f___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Array_fromJson_x3f___redArg___closed__7_value),((lean_object*)&l_Lean_Array_fromJson_x3f___redArg___closed__8_value)}};
static const lean_object* l_Lean_Array_fromJson_x3f___redArg___closed__9 = (const lean_object*)&l_Lean_Array_fromJson_x3f___redArg___closed__9_value;
static const lean_string_object l_Lean_Array_fromJson_x3f___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Lean_Array_fromJson_x3f___redArg___closed__10 = (const lean_object*)&l_Lean_Array_fromJson_x3f___redArg___closed__10_value;
static const lean_string_object l_Lean_Array_fromJson_x3f___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_Array_fromJson_x3f___redArg___closed__11 = (const lean_object*)&l_Lean_Array_fromJson_x3f___redArg___closed__11_value;
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Array_toJson___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Array_toJson___redArg___closed__0 = (const lean_object*)&l_Lean_Array_toJson___redArg___closed__0_value;
static const lean_closure_object l_Lean_Array_toJson___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Array_toJson___redArg___closed__1 = (const lean_object*)&l_Lean_Array_toJson___redArg___closed__1_value;
static const lean_closure_object l_Lean_Array_toJson___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Array_toJson___redArg___closed__2 = (const lean_object*)&l_Lean_Array_toJson___redArg___closed__2_value;
static const lean_closure_object l_Lean_Array_toJson___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Array_toJson___redArg___closed__3 = (const lean_object*)&l_Lean_Array_toJson___redArg___closed__3_value;
static const lean_closure_object l_Lean_Array_toJson___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Array_toJson___redArg___closed__4 = (const lean_object*)&l_Lean_Array_toJson___redArg___closed__4_value;
static const lean_closure_object l_Lean_Array_toJson___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Array_toJson___redArg___closed__5 = (const lean_object*)&l_Lean_Array_toJson___redArg___closed__5_value;
static const lean_closure_object l_Lean_Array_toJson___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Array_toJson___redArg___closed__6 = (const lean_object*)&l_Lean_Array_toJson___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Array_toJson___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Array_toJson___redArg___closed__0_value),((lean_object*)&l_Lean_Array_toJson___redArg___closed__1_value)}};
static const lean_object* l_Lean_Array_toJson___redArg___closed__7 = (const lean_object*)&l_Lean_Array_toJson___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Array_toJson___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Array_toJson___redArg___closed__7_value),((lean_object*)&l_Lean_Array_toJson___redArg___closed__2_value),((lean_object*)&l_Lean_Array_toJson___redArg___closed__3_value),((lean_object*)&l_Lean_Array_toJson___redArg___closed__4_value),((lean_object*)&l_Lean_Array_toJson___redArg___closed__5_value)}};
static const lean_object* l_Lean_Array_toJson___redArg___closed__8 = (const lean_object*)&l_Lean_Array_toJson___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Array_toJson___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Array_toJson___redArg___closed__8_value),((lean_object*)&l_Lean_Array_toJson___redArg___closed__6_value)}};
static const lean_object* l_Lean_Array_toJson___redArg___closed__9 = (const lean_object*)&l_Lean_Array_toJson___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Array_toJson___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToJsonArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToJsonArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_List_fromJson_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_List_fromJson_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonList(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_List_toJson___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_List_toJson(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToJsonList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToJsonList(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___redArg___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonOption___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonOption(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_toJson___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_toJson(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToJsonOption___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToJsonOption(lean_object*, lean_object*);
static const lean_string_object l_Lean_Prod_fromJson_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "expected pair, got '"};
static const lean_object* l_Lean_Prod_fromJson_x3f___redArg___closed__0 = (const lean_object*)&l_Lean_Prod_fromJson_x3f___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Prod_fromJson_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Prod_fromJson_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonProd___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonProd(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Prod_toJson___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Prod_toJson(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_USize_fromJson_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_USize_fromJson_x3f___closed__0;
static const lean_string_object l_Lean_USize_fromJson_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "value '"};
static const lean_object* l_Lean_USize_fromJson_x3f___closed__1 = (const lean_object*)&l_Lean_USize_fromJson_x3f___closed__1_value;
static const lean_string_object l_Lean_USize_fromJson_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "' is too large for `USize`"};
static const lean_object* l_Lean_USize_fromJson_x3f___closed__2 = (const lean_object*)&l_Lean_USize_fromJson_x3f___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_USize_fromJson_x3f(lean_object*);
static const lean_closure_object l_Lean_instFromJsonUSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_USize_fromJson_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonUSize___closed__0 = (const lean_object*)&l_Lean_instFromJsonUSize___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instFromJsonUSize = (const lean_object*)&l_Lean_instFromJsonUSize___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instToJsonUSize___lam__0(size_t);
LEAN_EXPORT lean_object* l_Lean_instToJsonUSize___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_instToJsonUSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonUSize___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonUSize___closed__0 = (const lean_object*)&l_Lean_instToJsonUSize___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonUSize = (const lean_object*)&l_Lean_instToJsonUSize___closed__0_value;
static lean_once_cell_t l_Lean_UInt64_fromJson_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_UInt64_fromJson_x3f___closed__0;
static const lean_string_object l_Lean_UInt64_fromJson_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "' is too large for `UInt64`"};
static const lean_object* l_Lean_UInt64_fromJson_x3f___closed__1 = (const lean_object*)&l_Lean_UInt64_fromJson_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_UInt64_fromJson_x3f(lean_object*);
static const lean_closure_object l_Lean_instFromJsonUInt64___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_UInt64_fromJson_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonUInt64___closed__0 = (const lean_object*)&l_Lean_instFromJsonUInt64___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instFromJsonUInt64 = (const lean_object*)&l_Lean_instFromJsonUInt64___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instToJsonUInt64___lam__0(uint64_t);
LEAN_EXPORT lean_object* l_Lean_instToJsonUInt64___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_instToJsonUInt64___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonUInt64___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonUInt64___closed__0 = (const lean_object*)&l_Lean_instToJsonUInt64___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonUInt64 = (const lean_object*)&l_Lean_instToJsonUInt64___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Float_toJson(double);
LEAN_EXPORT lean_object* l_Lean_Float_toJson___boxed(lean_object*);
static const lean_closure_object l_Lean_instToJsonFloat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Float_toJson___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonFloat___closed__0 = (const lean_object*)&l_Lean_instToJsonFloat___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonFloat = (const lean_object*)&l_Lean_instToJsonFloat___closed__0_value;
static const lean_string_object l_Lean_Float_fromJson_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "Expected a number or a string 'Infinity', '-Infinity', 'NaN'."};
static const lean_object* l_Lean_Float_fromJson_x3f___closed__0 = (const lean_object*)&l_Lean_Float_fromJson_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Float_fromJson_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Float_fromJson_x3f___closed__0_value)}};
static const lean_object* l_Lean_Float_fromJson_x3f___closed__1 = (const lean_object*)&l_Lean_Float_fromJson_x3f___closed__1_value;
static const lean_string_object l_Lean_Float_fromJson_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Infinity"};
static const lean_object* l_Lean_Float_fromJson_x3f___closed__2 = (const lean_object*)&l_Lean_Float_fromJson_x3f___closed__2_value;
static const lean_string_object l_Lean_Float_fromJson_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "-Infinity"};
static const lean_object* l_Lean_Float_fromJson_x3f___closed__3 = (const lean_object*)&l_Lean_Float_fromJson_x3f___closed__3_value;
static const lean_string_object l_Lean_Float_fromJson_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "NaN"};
static const lean_object* l_Lean_Float_fromJson_x3f___closed__4 = (const lean_object*)&l_Lean_Float_fromJson_x3f___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Float_fromJson_x3f(lean_object*);
static const lean_closure_object l_Lean_instFromJsonFloat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Float_fromJson_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
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
lean_object* l_Lean_instToJsonEmpty___lam__0(uint8_t v_a_45_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT void l_Lean_instToJsonEmpty___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_45_ = stack[0].m_num;
lean_object* v_res_46_;
v_res_46_ = l_Lean_instToJsonEmpty___lam__0(v_a_45_);
stack->m_obj
 = v_res_46_;
}
LEAN_EXPORT lean_object* l_Lean_instToJsonEmpty___lam__0___boxed(lean_object* v_a_47_){
_start:
{
uint8_t v_a_6__boxed_48_; lean_object* v_res_49_; 
v_a_6__boxed_48_ = lean_unbox(v_a_47_);
v_res_49_ = l_Lean_instToJsonEmpty___lam__0(v_a_6__boxed_48_);
return v_res_49_;
}
}
lean_object* l_Lean_instToJsonBool___lam__0(uint8_t v_b_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_55_, 0, v_b_54_);
return v___x_55_;
}
}
LEAN_EXPORT void l_Lean_instToJsonBool___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_b_54_ = stack[0].m_num;
lean_object* v_res_56_;
v_res_56_ = l_Lean_instToJsonBool___lam__0(v_b_54_);
stack->m_obj
 = v_res_56_;
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBool___lam__0___boxed(lean_object* v_b_57_){
_start:
{
uint8_t v_b_boxed_58_; lean_object* v_res_59_; 
v_b_boxed_58_ = lean_unbox(v_b_57_);
v_res_59_ = l_Lean_instToJsonBool___lam__0(v_b_boxed_58_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonNat___lam__0(lean_object* v_n_64_){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_65_ = l_Lean_JsonNumber_fromNat(v_n_64_);
v___x_66_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_66_, 0, v___x_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonInt___lam__0(lean_object* v_n_71_){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_72_ = l_Lean_JsonNumber_fromInt(v_n_71_);
v___x_73_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonString___lam__0(lean_object* v_s_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_79_, 0, v_s_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonSlice___lam__0(lean_object* v_s_89_){
_start:
{
lean_object* v_str_90_; lean_object* v_startInclusive_91_; lean_object* v_endExclusive_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v_str_90_ = lean_ctor_get(v_s_89_, 0);
v_startInclusive_91_ = lean_ctor_get(v_s_89_, 1);
v_endExclusive_92_ = lean_ctor_get(v_s_89_, 2);
v___x_93_ = lean_string_utf8_extract_fast(v_str_90_, v_startInclusive_91_, v_endExclusive_92_);
v___x_94_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_94_, 0, v___x_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonSlice___lam__0___boxed(lean_object* v_s_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Lean_instToJsonSlice___lam__0(v_s_95_);
lean_dec_ref(v_s_95_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonFilePath___lam__0(lean_object* v_j_99_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = l_Lean_Json_getStr_x3f(v_j_99_);
if (lean_obj_tag(v___x_100_) == 0)
{
lean_object* v_a_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_108_; 
v_a_101_ = lean_ctor_get(v___x_100_, 0);
v_isSharedCheck_108_ = !lean_is_exclusive(v___x_100_);
if (v_isSharedCheck_108_ == 0)
{
v___x_103_ = v___x_100_;
v_isShared_104_ = v_isSharedCheck_108_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_a_101_);
lean_dec(v___x_100_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_108_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
lean_object* v___x_106_; 
if (v_isShared_104_ == 0)
{
v___x_106_ = v___x_103_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v_a_101_);
v___x_106_ = v_reuseFailAlloc_107_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
return v___x_106_;
}
}
}
else
{
lean_object* v_a_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_116_; 
v_a_109_ = lean_ctor_get(v___x_100_, 0);
v_isSharedCheck_116_ = !lean_is_exclusive(v___x_100_);
if (v_isSharedCheck_116_ == 0)
{
v___x_111_ = v___x_100_;
v_isShared_112_ = v_isSharedCheck_116_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_a_109_);
lean_dec(v___x_100_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_116_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_114_; 
if (v_isShared_112_ == 0)
{
v___x_114_ = v___x_111_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v_a_109_);
v___x_114_ = v_reuseFailAlloc_115_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
return v___x_114_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonFilePath___lam__0(lean_object* v_p_119_){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_120_, 0, v_p_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___redArg(lean_object* v_inst_144_, lean_object* v_x_145_){
_start:
{
lean_object* v___x_146_; 
v___x_146_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___redArg___closed__9));
if (lean_obj_tag(v_x_145_) == 4)
{
lean_object* v_elems_147_; size_t v_sz_148_; size_t v___x_149_; lean_object* v___x_150_; 
v_elems_147_ = lean_ctor_get(v_x_145_, 0);
lean_inc_ref(v_elems_147_);
lean_dec_ref_known(v_x_145_, 1);
v_sz_148_ = lean_array_size(v_elems_147_);
v___x_149_ = ((size_t)0ULL);
v___x_150_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_146_, v_inst_144_, v_sz_148_, v___x_149_, v_elems_147_);
return v___x_150_;
}
else
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
lean_dec_ref(v_inst_144_);
v___x_151_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___redArg___closed__10));
v___x_152_ = lean_unsigned_to_nat(80u);
v___x_153_ = l_Lean_Json_pretty(v_x_145_, v___x_152_);
v___x_154_ = lean_string_append(v___x_151_, v___x_153_);
lean_dec_ref(v___x_153_);
v___x_155_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___redArg___closed__11));
v___x_156_ = lean_string_append(v___x_154_, v___x_155_);
v___x_157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
return v___x_157_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f(lean_object* v_00_u03b1_158_, lean_object* v_inst_159_, lean_object* v_x_160_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l_Lean_Array_fromJson_x3f___redArg(v_inst_159_, v_x_160_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonArray___redArg(lean_object* v_inst_162_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = lean_alloc_closure((void*)(l_Lean_Array_fromJson_x3f), 3, 2);
lean_closure_set(v___x_163_, 0, lean_box(0));
lean_closure_set(v___x_163_, 1, v_inst_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonArray(lean_object* v_00_u03b1_164_, lean_object* v_inst_165_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = lean_alloc_closure((void*)(l_Lean_Array_fromJson_x3f), 3, 2);
lean_closure_set(v___x_166_, 0, lean_box(0));
lean_closure_set(v___x_166_, 1, v_inst_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___redArg___lam__0(lean_object* v_inst_167_, lean_object* v_x_168_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = lean_apply_1(v_inst_167_, v_x_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___redArg(lean_object* v_inst_189_, lean_object* v_a_190_){
_start:
{
lean_object* v___f_191_; lean_object* v___x_192_; size_t v_sz_193_; size_t v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v___f_191_ = lean_alloc_closure((void*)(l_Lean_Array_toJson___redArg___lam__0), 2, 1);
lean_closure_set(v___f_191_, 0, v_inst_189_);
v___x_192_ = ((lean_object*)(l_Lean_Array_toJson___redArg___closed__9));
v_sz_193_ = lean_array_size(v_a_190_);
v___x_194_ = ((size_t)0ULL);
v___x_195_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_192_, v___f_191_, v_sz_193_, v___x_194_, v_a_190_);
v___x_196_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson(lean_object* v_00_u03b1_197_, lean_object* v_inst_198_, lean_object* v_a_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l_Lean_Array_toJson___redArg(v_inst_198_, v_a_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonArray___redArg(lean_object* v_inst_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = lean_alloc_closure((void*)(l_Lean_Array_toJson), 3, 2);
lean_closure_set(v___x_202_, 0, lean_box(0));
lean_closure_set(v___x_202_, 1, v_inst_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonArray(lean_object* v_00_u03b1_203_, lean_object* v_inst_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = lean_alloc_closure((void*)(l_Lean_Array_toJson), 3, 2);
lean_closure_set(v___x_205_, 0, lean_box(0));
lean_closure_set(v___x_205_, 1, v_inst_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_fromJson_x3f___redArg(lean_object* v_inst_206_, lean_object* v_j_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l_Lean_Array_fromJson_x3f___redArg(v_inst_206_, v_j_207_);
if (lean_obj_tag(v___x_208_) == 0)
{
lean_object* v_a_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_216_; 
v_a_209_ = lean_ctor_get(v___x_208_, 0);
v_isSharedCheck_216_ = !lean_is_exclusive(v___x_208_);
if (v_isSharedCheck_216_ == 0)
{
v___x_211_ = v___x_208_;
v_isShared_212_ = v_isSharedCheck_216_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_a_209_);
lean_dec(v___x_208_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_216_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v___x_214_; 
if (v_isShared_212_ == 0)
{
v___x_214_ = v___x_211_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v_a_209_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
return v___x_214_;
}
}
}
else
{
lean_object* v_a_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_225_; 
v_a_217_ = lean_ctor_get(v___x_208_, 0);
v_isSharedCheck_225_ = !lean_is_exclusive(v___x_208_);
if (v_isSharedCheck_225_ == 0)
{
v___x_219_ = v___x_208_;
v_isShared_220_ = v_isSharedCheck_225_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_a_217_);
lean_dec(v___x_208_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_225_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v___x_221_; lean_object* v___x_223_; 
v___x_221_ = lean_array_to_list(v_a_217_);
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 0, v___x_221_);
v___x_223_ = v___x_219_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v___x_221_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
return v___x_223_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_List_fromJson_x3f(lean_object* v_00_u03b1_226_, lean_object* v_inst_227_, lean_object* v_j_228_){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = l_Lean_List_fromJson_x3f___redArg(v_inst_227_, v_j_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonList___redArg(lean_object* v_inst_230_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = lean_alloc_closure((void*)(l_Lean_List_fromJson_x3f), 3, 2);
lean_closure_set(v___x_231_, 0, lean_box(0));
lean_closure_set(v___x_231_, 1, v_inst_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonList(lean_object* v_00_u03b1_232_, lean_object* v_inst_233_){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = lean_alloc_closure((void*)(l_Lean_List_fromJson_x3f), 3, 2);
lean_closure_set(v___x_234_, 0, lean_box(0));
lean_closure_set(v___x_234_, 1, v_inst_233_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toJson___redArg(lean_object* v_inst_235_, lean_object* v_a_236_){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_237_ = lean_array_mk(v_a_236_);
v___x_238_ = l_Lean_Array_toJson___redArg(v_inst_235_, v___x_237_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toJson(lean_object* v_00_u03b1_239_, lean_object* v_inst_240_, lean_object* v_a_241_){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = l_Lean_List_toJson___redArg(v_inst_240_, v_a_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonList___redArg(lean_object* v_inst_243_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = lean_alloc_closure((void*)(l_Lean_List_toJson), 3, 2);
lean_closure_set(v___x_244_, 0, lean_box(0));
lean_closure_set(v___x_244_, 1, v_inst_243_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonList(lean_object* v_00_u03b1_245_, lean_object* v_inst_246_){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = lean_alloc_closure((void*)(l_Lean_List_toJson), 3, 2);
lean_closure_set(v___x_247_, 0, lean_box(0));
lean_closure_set(v___x_247_, 1, v_inst_246_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___redArg(lean_object* v_inst_250_, lean_object* v_x_251_){
_start:
{
if (lean_obj_tag(v_x_251_) == 0)
{
lean_object* v___x_252_; 
lean_dec_ref(v_inst_250_);
v___x_252_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___redArg___closed__0));
return v___x_252_;
}
else
{
lean_object* v___x_253_; 
v___x_253_ = lean_apply_1(v_inst_250_, v_x_251_);
if (lean_obj_tag(v___x_253_) == 0)
{
lean_object* v_a_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_261_; 
v_a_254_ = lean_ctor_get(v___x_253_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v___x_253_);
if (v_isSharedCheck_261_ == 0)
{
v___x_256_ = v___x_253_;
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_a_254_);
lean_dec(v___x_253_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___x_259_; 
if (v_isShared_257_ == 0)
{
v___x_259_ = v___x_256_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_a_254_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
}
else
{
lean_object* v_a_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_270_; 
v_a_262_ = lean_ctor_get(v___x_253_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_253_);
if (v_isSharedCheck_270_ == 0)
{
v___x_264_ = v___x_253_;
v_isShared_265_ = v_isSharedCheck_270_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_a_262_);
lean_dec(v___x_253_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_270_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_266_; lean_object* v___x_268_; 
v___x_266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_266_, 0, v_a_262_);
if (v_isShared_265_ == 0)
{
lean_ctor_set(v___x_264_, 0, v___x_266_);
v___x_268_ = v___x_264_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v___x_266_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f(lean_object* v_00_u03b1_271_, lean_object* v_inst_272_, lean_object* v_x_273_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = l_Lean_Option_fromJson_x3f___redArg(v_inst_272_, v_x_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonOption___redArg(lean_object* v_inst_275_){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = lean_alloc_closure((void*)(l_Lean_Option_fromJson_x3f), 3, 2);
lean_closure_set(v___x_276_, 0, lean_box(0));
lean_closure_set(v___x_276_, 1, v_inst_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonOption(lean_object* v_00_u03b1_277_, lean_object* v_inst_278_){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = lean_alloc_closure((void*)(l_Lean_Option_fromJson_x3f), 3, 2);
lean_closure_set(v___x_279_, 0, lean_box(0));
lean_closure_set(v___x_279_, 1, v_inst_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_toJson___redArg(lean_object* v_inst_280_, lean_object* v_x_281_){
_start:
{
if (lean_obj_tag(v_x_281_) == 0)
{
lean_object* v___x_282_; 
lean_dec_ref(v_inst_280_);
v___x_282_ = lean_box(0);
return v___x_282_;
}
else
{
lean_object* v_val_283_; lean_object* v___x_284_; 
v_val_283_ = lean_ctor_get(v_x_281_, 0);
lean_inc(v_val_283_);
lean_dec_ref_known(v_x_281_, 1);
v___x_284_ = lean_apply_1(v_inst_280_, v_val_283_);
return v___x_284_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_toJson(lean_object* v_00_u03b1_285_, lean_object* v_inst_286_, lean_object* v_x_287_){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = l_Lean_Option_toJson___redArg(v_inst_286_, v_x_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonOption___redArg(lean_object* v_inst_289_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = lean_alloc_closure((void*)(l_Lean_Option_toJson), 3, 2);
lean_closure_set(v___x_290_, 0, lean_box(0));
lean_closure_set(v___x_290_, 1, v_inst_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonOption(lean_object* v_00_u03b1_291_, lean_object* v_inst_292_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = lean_alloc_closure((void*)(l_Lean_Option_toJson), 3, 2);
lean_closure_set(v___x_293_, 0, lean_box(0));
lean_closure_set(v___x_293_, 1, v_inst_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Prod_fromJson_x3f___redArg(lean_object* v_inst_295_, lean_object* v_inst_296_, lean_object* v_x_297_){
_start:
{
lean_object* v_j_299_; 
if (lean_obj_tag(v_x_297_) == 4)
{
lean_object* v_elems_307_; lean_object* v___x_308_; lean_object* v___x_309_; uint8_t v___x_310_; 
v_elems_307_ = lean_ctor_get(v_x_297_, 0);
v___x_308_ = lean_array_get_size(v_elems_307_);
v___x_309_ = lean_unsigned_to_nat(2u);
v___x_310_ = lean_nat_dec_eq(v___x_308_, v___x_309_);
if (v___x_310_ == 0)
{
lean_dec_ref(v_inst_296_);
lean_dec_ref(v_inst_295_);
v_j_299_ = v_x_297_;
goto v___jp_298_;
}
else
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
lean_inc_ref(v_elems_307_);
lean_dec_ref_known(v_x_297_, 1);
v___x_311_ = lean_unsigned_to_nat(0u);
v___x_312_ = lean_array_fget_borrowed(v_elems_307_, v___x_311_);
lean_inc(v___x_312_);
v___x_313_ = lean_apply_1(v_inst_295_, v___x_312_);
if (lean_obj_tag(v___x_313_) == 0)
{
lean_object* v_a_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_321_; 
lean_dec_ref(v_elems_307_);
lean_dec_ref(v_inst_296_);
v_a_314_ = lean_ctor_get(v___x_313_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_313_);
if (v_isSharedCheck_321_ == 0)
{
v___x_316_ = v___x_313_;
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_a_314_);
lean_dec(v___x_313_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_319_; 
if (v_isShared_317_ == 0)
{
v___x_319_ = v___x_316_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_a_314_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
else
{
lean_object* v_a_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v_a_322_ = lean_ctor_get(v___x_313_, 0);
lean_inc(v_a_322_);
lean_dec_ref_known(v___x_313_, 1);
v___x_323_ = lean_unsigned_to_nat(1u);
v___x_324_ = lean_array_fget(v_elems_307_, v___x_323_);
lean_dec_ref(v_elems_307_);
v___x_325_ = lean_apply_1(v_inst_296_, v___x_324_);
if (lean_obj_tag(v___x_325_) == 0)
{
lean_object* v_a_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_333_; 
lean_dec(v_a_322_);
v_a_326_ = lean_ctor_get(v___x_325_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_333_ == 0)
{
v___x_328_ = v___x_325_;
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_a_326_);
lean_dec(v___x_325_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_331_; 
if (v_isShared_329_ == 0)
{
v___x_331_ = v___x_328_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_a_326_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
else
{
lean_object* v_a_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_342_; 
v_a_334_ = lean_ctor_get(v___x_325_, 0);
v_isSharedCheck_342_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_342_ == 0)
{
v___x_336_ = v___x_325_;
v_isShared_337_ = v_isSharedCheck_342_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_a_334_);
lean_dec(v___x_325_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_342_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_338_; lean_object* v___x_340_; 
v___x_338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_338_, 0, v_a_322_);
lean_ctor_set(v___x_338_, 1, v_a_334_);
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 0, v___x_338_);
v___x_340_ = v___x_336_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v___x_338_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_inst_296_);
lean_dec_ref(v_inst_295_);
v_j_299_ = v_x_297_;
goto v___jp_298_;
}
v___jp_298_:
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_300_ = ((lean_object*)(l_Lean_Prod_fromJson_x3f___redArg___closed__0));
v___x_301_ = lean_unsigned_to_nat(80u);
v___x_302_ = l_Lean_Json_pretty(v_j_299_, v___x_301_);
v___x_303_ = lean_string_append(v___x_300_, v___x_302_);
lean_dec_ref(v___x_302_);
v___x_304_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___redArg___closed__11));
v___x_305_ = lean_string_append(v___x_303_, v___x_304_);
v___x_306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
return v___x_306_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Prod_fromJson_x3f(lean_object* v_00_u03b1_343_, lean_object* v_00_u03b2_344_, lean_object* v_inst_345_, lean_object* v_inst_346_, lean_object* v_x_347_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = l_Lean_Prod_fromJson_x3f___redArg(v_inst_345_, v_inst_346_, v_x_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonProd___redArg(lean_object* v_inst_349_, lean_object* v_inst_350_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = lean_alloc_closure((void*)(l_Lean_Prod_fromJson_x3f), 5, 4);
lean_closure_set(v___x_351_, 0, lean_box(0));
lean_closure_set(v___x_351_, 1, lean_box(0));
lean_closure_set(v___x_351_, 2, v_inst_349_);
lean_closure_set(v___x_351_, 3, v_inst_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonProd(lean_object* v_00_u03b1_352_, lean_object* v_00_u03b2_353_, lean_object* v_inst_354_, lean_object* v_inst_355_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = lean_alloc_closure((void*)(l_Lean_Prod_fromJson_x3f), 5, 4);
lean_closure_set(v___x_356_, 0, lean_box(0));
lean_closure_set(v___x_356_, 1, lean_box(0));
lean_closure_set(v___x_356_, 2, v_inst_354_);
lean_closure_set(v___x_356_, 3, v_inst_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Prod_toJson___redArg(lean_object* v_inst_357_, lean_object* v_inst_358_, lean_object* v_x_359_){
_start:
{
lean_object* v_fst_360_; lean_object* v_snd_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v_fst_360_ = lean_ctor_get(v_x_359_, 0);
lean_inc(v_fst_360_);
v_snd_361_ = lean_ctor_get(v_x_359_, 1);
lean_inc(v_snd_361_);
lean_dec_ref(v_x_359_);
v___x_362_ = lean_apply_1(v_inst_357_, v_fst_360_);
v___x_363_ = lean_apply_1(v_inst_358_, v_snd_361_);
v___x_364_ = lean_unsigned_to_nat(2u);
v___x_365_ = lean_mk_empty_array_with_capacity(v___x_364_);
v___x_366_ = lean_array_push(v___x_365_, v___x_362_);
v___x_367_ = lean_array_push(v___x_366_, v___x_363_);
v___x_368_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_368_, 0, v___x_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Prod_toJson(lean_object* v_00_u03b1_369_, lean_object* v_00_u03b2_370_, lean_object* v_inst_371_, lean_object* v_inst_372_, lean_object* v_x_373_){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = l_Lean_Prod_toJson___redArg(v_inst_371_, v_inst_372_, v_x_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonProd___redArg(lean_object* v_inst_375_, lean_object* v_inst_376_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = lean_alloc_closure((void*)(l_Lean_Prod_toJson), 5, 4);
lean_closure_set(v___x_377_, 0, lean_box(0));
lean_closure_set(v___x_377_, 1, lean_box(0));
lean_closure_set(v___x_377_, 2, v_inst_375_);
lean_closure_set(v___x_377_, 3, v_inst_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonProd(lean_object* v_00_u03b1_378_, lean_object* v_00_u03b2_379_, lean_object* v_inst_380_, lean_object* v_inst_381_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = lean_alloc_closure((void*)(l_Lean_Prod_toJson), 5, 4);
lean_closure_set(v___x_382_, 0, lean_box(0));
lean_closure_set(v___x_382_, 1, lean_box(0));
lean_closure_set(v___x_382_, 2, v_inst_380_);
lean_closure_set(v___x_382_, 3, v_inst_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_fromJson_x3f(lean_object* v_j_387_){
_start:
{
lean_object* v___x_388_; 
lean_inc(v_j_387_);
v___x_388_ = l_Lean_Json_getStr_x3f(v_j_387_);
if (lean_obj_tag(v___x_388_) == 0)
{
lean_object* v_a_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_396_; 
lean_dec(v_j_387_);
v_a_389_ = lean_ctor_get(v___x_388_, 0);
v_isSharedCheck_396_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_396_ == 0)
{
v___x_391_ = v___x_388_;
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_a_389_);
lean_dec(v___x_388_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_394_; 
if (v_isShared_392_ == 0)
{
v___x_394_ = v___x_391_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_a_389_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
else
{
lean_object* v_a_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_418_; 
v_a_397_ = lean_ctor_get(v___x_388_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_418_ == 0)
{
v___x_399_ = v___x_388_;
v_isShared_400_ = v_isSharedCheck_418_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_a_397_);
lean_dec(v___x_388_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_418_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_401_; uint8_t v___x_402_; 
v___x_401_ = ((lean_object*)(l_Lean_Name_fromJson_x3f___closed__0));
v___x_402_ = lean_string_dec_eq(v_a_397_, v___x_401_);
if (v___x_402_ == 0)
{
lean_object* v___x_403_; uint8_t v___x_404_; 
v___x_403_ = l_String_toName(v_a_397_);
v___x_404_ = l_Lean_Name_isAnonymous(v___x_403_);
if (v___x_404_ == 0)
{
lean_object* v___x_406_; 
lean_dec(v_j_387_);
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 0, v___x_403_);
v___x_406_ = v___x_399_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_403_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
else
{
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_415_; 
lean_dec(v___x_403_);
v___x_408_ = ((lean_object*)(l_Lean_Name_fromJson_x3f___closed__1));
v___x_409_ = lean_unsigned_to_nat(80u);
v___x_410_ = l_Lean_Json_pretty(v_j_387_, v___x_409_);
v___x_411_ = lean_string_append(v___x_408_, v___x_410_);
lean_dec_ref(v___x_410_);
v___x_412_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___redArg___closed__11));
v___x_413_ = lean_string_append(v___x_411_, v___x_412_);
if (v_isShared_400_ == 0)
{
lean_ctor_set_tag(v___x_399_, 0);
lean_ctor_set(v___x_399_, 0, v___x_413_);
v___x_415_ = v___x_399_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v___x_413_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
else
{
lean_object* v___x_417_; 
lean_del_object(v___x_399_);
lean_dec(v_a_397_);
lean_dec(v_j_387_);
v___x_417_ = ((lean_object*)(l_Lean_Name_fromJson_x3f___closed__2));
return v___x_417_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonName___lam__0(lean_object* v_n_421_){
_start:
{
uint8_t v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_422_ = 1;
v___x_423_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_421_, v___x_422_);
v___x_424_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f___redArg___lam__0(lean_object* v_inst_427_, lean_object* v_m_428_, lean_object* v_k_429_, lean_object* v_v_430_){
_start:
{
lean_object* v___x_431_; uint8_t v___x_432_; 
v___x_431_ = ((lean_object*)(l_Lean_Name_fromJson_x3f___closed__0));
v___x_432_ = lean_string_dec_eq(v_k_429_, v___x_431_);
if (v___x_432_ == 0)
{
lean_object* v_n_433_; uint8_t v___x_434_; 
lean_inc_ref(v_k_429_);
v_n_433_ = l_String_toName(v_k_429_);
v___x_434_ = l_Lean_Name_isAnonymous(v_n_433_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; 
lean_dec_ref(v_k_429_);
v___x_435_ = lean_apply_1(v_inst_427_, v_v_430_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v_a_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_443_; 
lean_dec(v_n_433_);
lean_dec(v_m_428_);
v_a_436_ = lean_ctor_get(v___x_435_, 0);
v_isSharedCheck_443_ = !lean_is_exclusive(v___x_435_);
if (v_isSharedCheck_443_ == 0)
{
v___x_438_ = v___x_435_;
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_a_436_);
lean_dec(v___x_435_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_441_; 
if (v_isShared_439_ == 0)
{
v___x_441_ = v___x_438_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_a_436_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
}
else
{
lean_object* v_a_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_452_; 
v_a_444_ = lean_ctor_get(v___x_435_, 0);
v_isSharedCheck_452_ = !lean_is_exclusive(v___x_435_);
if (v_isSharedCheck_452_ == 0)
{
v___x_446_ = v___x_435_;
v_isShared_447_ = v_isSharedCheck_452_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_a_444_);
lean_dec(v___x_435_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_452_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v___x_448_; lean_object* v___x_450_; 
v___x_448_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_n_433_, v_a_444_, v_m_428_);
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 0, v___x_448_);
v___x_450_ = v___x_446_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v___x_448_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
}
}
else
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
lean_dec(v_n_433_);
lean_dec(v_v_430_);
lean_dec(v_m_428_);
lean_dec_ref(v_inst_427_);
v___x_453_ = ((lean_object*)(l_Lean_Name_fromJson_x3f___closed__1));
v___x_454_ = lean_string_append(v___x_453_, v_k_429_);
lean_dec_ref(v_k_429_);
v___x_455_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___redArg___closed__11));
v___x_456_ = lean_string_append(v___x_454_, v___x_455_);
v___x_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
return v___x_457_;
}
}
else
{
lean_object* v___x_458_; 
lean_dec_ref(v_k_429_);
v___x_458_ = lean_apply_1(v_inst_427_, v_v_430_);
if (lean_obj_tag(v___x_458_) == 0)
{
lean_object* v_a_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_466_; 
lean_dec(v_m_428_);
v_a_459_ = lean_ctor_get(v___x_458_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_466_ == 0)
{
v___x_461_ = v___x_458_;
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_a_459_);
lean_dec(v___x_458_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_464_; 
if (v_isShared_462_ == 0)
{
v___x_464_ = v___x_461_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_a_459_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
else
{
lean_object* v_a_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_476_; 
v_a_467_ = lean_ctor_get(v___x_458_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_476_ == 0)
{
v___x_469_ = v___x_458_;
v_isShared_470_ = v_isSharedCheck_476_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_a_467_);
lean_dec(v___x_458_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_476_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_474_; 
v___x_471_ = lean_box(0);
v___x_472_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_471_, v_a_467_, v_m_428_);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 0, v___x_472_);
v___x_474_ = v___x_469_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v___x_472_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f___redArg(lean_object* v_inst_478_, lean_object* v_x_479_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___redArg___closed__9));
if (lean_obj_tag(v_x_479_) == 5)
{
lean_object* v_kvPairs_481_; lean_object* v___f_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v_kvPairs_481_ = lean_ctor_get(v_x_479_, 0);
lean_inc(v_kvPairs_481_);
lean_dec_ref_known(v_x_479_, 1);
v___f_482_ = lean_alloc_closure((void*)(l_Lean_NameMap_fromJson_x3f___redArg___lam__0), 4, 1);
lean_closure_set(v___f_482_, 0, v_inst_478_);
v___x_483_ = lean_box(1);
v___x_484_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v___x_480_, v___f_482_, v___x_483_, v_kvPairs_481_);
return v___x_484_;
}
else
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
lean_dec_ref(v_inst_478_);
v___x_485_ = ((lean_object*)(l_Lean_NameMap_fromJson_x3f___redArg___closed__0));
v___x_486_ = lean_unsigned_to_nat(80u);
v___x_487_ = l_Lean_Json_pretty(v_x_479_, v___x_486_);
v___x_488_ = lean_string_append(v___x_485_, v___x_487_);
lean_dec_ref(v___x_487_);
v___x_489_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___redArg___closed__11));
v___x_490_ = lean_string_append(v___x_488_, v___x_489_);
v___x_491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_491_, 0, v___x_490_);
return v___x_491_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f(lean_object* v_00_u03b1_492_, lean_object* v_inst_493_, lean_object* v_x_494_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l_Lean_NameMap_fromJson_x3f___redArg(v_inst_493_, v_x_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonNameMap___redArg(lean_object* v_inst_496_){
_start:
{
lean_object* v___x_497_; 
v___x_497_ = lean_alloc_closure((void*)(l_Lean_NameMap_fromJson_x3f), 3, 2);
lean_closure_set(v___x_497_, 0, lean_box(0));
lean_closure_set(v___x_497_, 1, v_inst_496_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonNameMap(lean_object* v_00_u03b1_498_, lean_object* v_inst_499_){
_start:
{
lean_object* v___x_500_; 
v___x_500_ = lean_alloc_closure((void*)(l_Lean_NameMap_fromJson_x3f), 3, 2);
lean_closure_set(v___x_500_, 0, lean_box(0));
lean_closure_set(v___x_500_, 1, v_inst_499_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___redArg___lam__0(lean_object* v_inst_502_, lean_object* v_n_503_, lean_object* v_k_504_, lean_object* v_v_505_){
_start:
{
lean_object* v___x_506_; uint8_t v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_506_ = ((lean_object*)(l_Lean_NameMap_toJson___redArg___lam__0___closed__0));
v___x_507_ = 1;
v___x_508_ = l_Lean_Name_toString(v_k_504_, v___x_507_);
v___x_509_ = lean_apply_1(v_inst_502_, v_v_505_);
v___x_510_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v___x_506_, v___x_508_, v___x_509_, v_n_503_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___redArg(lean_object* v_inst_511_, lean_object* v_m_512_){
_start:
{
lean_object* v___f_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v___f_513_ = lean_alloc_closure((void*)(l_Lean_NameMap_toJson___redArg___lam__0), 4, 1);
lean_closure_set(v___f_513_, 0, v_inst_511_);
v___x_514_ = lean_box(1);
v___x_515_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_513_, v___x_514_, v_m_512_);
v___x_516_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_516_, 0, v___x_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson(lean_object* v_00_u03b1_517_, lean_object* v_inst_518_, lean_object* v_m_519_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = l_Lean_NameMap_toJson___redArg(v_inst_518_, v_m_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonNameMap___redArg(lean_object* v_inst_521_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = lean_alloc_closure((void*)(l_Lean_NameMap_toJson), 3, 2);
lean_closure_set(v___x_522_, 0, lean_box(0));
lean_closure_set(v___x_522_, 1, v_inst_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonNameMap(lean_object* v_00_u03b1_523_, lean_object* v_inst_524_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = lean_alloc_closure((void*)(l_Lean_NameMap_toJson), 3, 2);
lean_closure_set(v___x_525_, 0, lean_box(0));
lean_closure_set(v___x_525_, 1, v_inst_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_bignumFromJson_x3f(lean_object* v_j_527_){
_start:
{
lean_object* v___x_528_; 
lean_inc(v_j_527_);
v___x_528_ = l_Lean_Json_getStr_x3f(v_j_527_);
if (lean_obj_tag(v___x_528_) == 0)
{
lean_object* v_a_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_536_; 
lean_dec(v_j_527_);
v_a_529_ = lean_ctor_get(v___x_528_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_528_);
if (v_isSharedCheck_536_ == 0)
{
v___x_531_ = v___x_528_;
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_a_529_);
lean_dec(v___x_528_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_534_; 
if (v_isShared_532_ == 0)
{
v___x_534_ = v___x_531_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_a_529_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
else
{
lean_object* v_a_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_555_; 
v_a_537_ = lean_ctor_get(v___x_528_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_528_);
if (v_isSharedCheck_555_ == 0)
{
v___x_539_ = v___x_528_;
v_isShared_540_ = v_isSharedCheck_555_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_a_537_);
lean_dec(v___x_528_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_555_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_541_; 
v___x_541_ = l_Lean_Syntax_decodeNatLitVal_x3f(v_a_537_);
lean_dec(v_a_537_);
if (lean_obj_tag(v___x_541_) == 1)
{
lean_object* v_val_542_; lean_object* v___x_544_; 
lean_dec(v_j_527_);
v_val_542_ = lean_ctor_get(v___x_541_, 0);
lean_inc(v_val_542_);
lean_dec_ref_known(v___x_541_, 1);
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 0, v_val_542_);
v___x_544_ = v___x_539_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_val_542_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
else
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_553_; 
lean_dec(v___x_541_);
v___x_546_ = ((lean_object*)(l_Lean_bignumFromJson_x3f___closed__0));
v___x_547_ = lean_unsigned_to_nat(80u);
v___x_548_ = l_Lean_Json_pretty(v_j_527_, v___x_547_);
v___x_549_ = lean_string_append(v___x_546_, v___x_548_);
lean_dec_ref(v___x_548_);
v___x_550_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___redArg___closed__11));
v___x_551_ = lean_string_append(v___x_549_, v___x_550_);
if (v_isShared_540_ == 0)
{
lean_ctor_set_tag(v___x_539_, 0);
lean_ctor_set(v___x_539_, 0, v___x_551_);
v___x_553_ = v___x_539_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_551_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_bignumToJson(lean_object* v_n_556_){
_start:
{
lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_557_ = l_Nat_reprFast(v_n_556_);
v___x_558_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
return v___x_558_;
}
}
static lean_object* _init_l_Lean_USize_fromJson_x3f___closed__0(void){
_start:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_559_ = l_System_Platform_numBits;
v___x_560_ = lean_unsigned_to_nat(2u);
v___x_561_ = lean_nat_pow(v___x_560_, v___x_559_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_USize_fromJson_x3f(lean_object* v_j_564_){
_start:
{
lean_object* v___x_565_; 
lean_inc(v_j_564_);
v___x_565_ = l_Lean_bignumFromJson_x3f(v_j_564_);
if (lean_obj_tag(v___x_565_) == 0)
{
lean_object* v_a_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_573_; 
lean_dec(v_j_564_);
v_a_566_ = lean_ctor_get(v___x_565_, 0);
v_isSharedCheck_573_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_573_ == 0)
{
v___x_568_ = v___x_565_;
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_a_566_);
lean_dec(v___x_565_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_571_; 
if (v_isShared_569_ == 0)
{
v___x_571_ = v___x_568_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_a_566_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
else
{
lean_object* v_a_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_594_; 
v_a_574_ = lean_ctor_get(v___x_565_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_594_ == 0)
{
v___x_576_ = v___x_565_;
v_isShared_577_ = v_isSharedCheck_594_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_a_574_);
lean_dec(v___x_565_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_594_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_578_; uint8_t v___x_579_; 
v___x_578_ = lean_obj_once(&l_Lean_USize_fromJson_x3f___closed__0, &l_Lean_USize_fromJson_x3f___closed__0_once, _init_l_Lean_USize_fromJson_x3f___closed__0);
v___x_579_ = lean_nat_dec_le(v___x_578_, v_a_574_);
if (v___x_579_ == 0)
{
size_t v___x_580_; lean_object* v___x_581_; lean_object* v___x_583_; 
lean_dec(v_j_564_);
v___x_580_ = lean_usize_of_nat(v_a_574_);
lean_dec(v_a_574_);
v___x_581_ = lean_box_usize(v___x_580_);
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 0, v___x_581_);
v___x_583_ = v___x_576_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v___x_581_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
else
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_592_; 
lean_dec(v_a_574_);
v___x_585_ = ((lean_object*)(l_Lean_USize_fromJson_x3f___closed__1));
v___x_586_ = lean_unsigned_to_nat(80u);
v___x_587_ = l_Lean_Json_pretty(v_j_564_, v___x_586_);
v___x_588_ = lean_string_append(v___x_585_, v___x_587_);
lean_dec_ref(v___x_587_);
v___x_589_ = ((lean_object*)(l_Lean_USize_fromJson_x3f___closed__2));
v___x_590_ = lean_string_append(v___x_588_, v___x_589_);
if (v_isShared_577_ == 0)
{
lean_ctor_set_tag(v___x_576_, 0);
lean_ctor_set(v___x_576_, 0, v___x_590_);
v___x_592_ = v___x_576_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_590_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
}
}
}
lean_object* l_Lean_instToJsonUSize___lam__0(size_t v_v_597_){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_598_ = lean_usize_to_nat(v_v_597_);
v___x_599_ = l_Lean_bignumToJson(v___x_598_);
return v___x_599_;
}
}
LEAN_EXPORT void l_Lean_instToJsonUSize___lam__0_0interp(lean_interpreter_value* stack)
{
size_t v_v_597_ = stack[0].m_num;
lean_object* v_res_600_;
v_res_600_ = l_Lean_instToJsonUSize___lam__0(v_v_597_);
stack->m_obj
 = v_res_600_;
}
LEAN_EXPORT lean_object* l_Lean_instToJsonUSize___lam__0___boxed(lean_object* v_v_601_){
_start:
{
size_t v_v_boxed_602_; lean_object* v_res_603_; 
v_v_boxed_602_ = lean_unbox_usize(v_v_601_);
lean_dec(v_v_601_);
v_res_603_ = l_Lean_instToJsonUSize___lam__0(v_v_boxed_602_);
return v_res_603_;
}
}
static lean_object* _init_l_Lean_UInt64_fromJson_x3f___closed__0(void){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = lean_cstr_to_nat("18446744073709551616");
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_UInt64_fromJson_x3f(lean_object* v_j_608_){
_start:
{
lean_object* v___x_609_; 
lean_inc(v_j_608_);
v___x_609_ = l_Lean_bignumFromJson_x3f(v_j_608_);
if (lean_obj_tag(v___x_609_) == 0)
{
lean_object* v_a_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_617_; 
lean_dec(v_j_608_);
v_a_610_ = lean_ctor_get(v___x_609_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_617_ == 0)
{
v___x_612_ = v___x_609_;
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_a_610_);
lean_dec(v___x_609_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_615_; 
if (v_isShared_613_ == 0)
{
v___x_615_ = v___x_612_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_a_610_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
else
{
lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_638_; 
v_a_618_ = lean_ctor_get(v___x_609_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_638_ == 0)
{
v___x_620_ = v___x_609_;
v_isShared_621_ = v_isSharedCheck_638_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_dec(v___x_609_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_638_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_622_; uint8_t v___x_623_; 
v___x_622_ = lean_obj_once(&l_Lean_UInt64_fromJson_x3f___closed__0, &l_Lean_UInt64_fromJson_x3f___closed__0_once, _init_l_Lean_UInt64_fromJson_x3f___closed__0);
v___x_623_ = lean_nat_dec_le(v___x_622_, v_a_618_);
if (v___x_623_ == 0)
{
uint64_t v___x_624_; lean_object* v___x_625_; lean_object* v___x_627_; 
lean_dec(v_j_608_);
v___x_624_ = lean_uint64_of_nat(v_a_618_);
lean_dec(v_a_618_);
v___x_625_ = lean_box_uint64(v___x_624_);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 0, v___x_625_);
v___x_627_ = v___x_620_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v___x_625_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
else
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_636_; 
lean_dec(v_a_618_);
v___x_629_ = ((lean_object*)(l_Lean_USize_fromJson_x3f___closed__1));
v___x_630_ = lean_unsigned_to_nat(80u);
v___x_631_ = l_Lean_Json_pretty(v_j_608_, v___x_630_);
v___x_632_ = lean_string_append(v___x_629_, v___x_631_);
lean_dec_ref(v___x_631_);
v___x_633_ = ((lean_object*)(l_Lean_UInt64_fromJson_x3f___closed__1));
v___x_634_ = lean_string_append(v___x_632_, v___x_633_);
if (v_isShared_621_ == 0)
{
lean_ctor_set_tag(v___x_620_, 0);
lean_ctor_set(v___x_620_, 0, v___x_634_);
v___x_636_ = v___x_620_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___x_634_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
}
}
}
lean_object* l_Lean_instToJsonUInt64___lam__0(uint64_t v_v_641_){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = lean_uint64_to_nat(v_v_641_);
v___x_643_ = l_Lean_bignumToJson(v___x_642_);
return v___x_643_;
}
}
LEAN_EXPORT void l_Lean_instToJsonUInt64___lam__0_0interp(lean_interpreter_value* stack)
{
uint64_t v_v_641_ = stack[0].m_num;
lean_object* v_res_644_;
v_res_644_ = l_Lean_instToJsonUInt64___lam__0(v_v_641_);
stack->m_obj
 = v_res_644_;
}
LEAN_EXPORT lean_object* l_Lean_instToJsonUInt64___lam__0___boxed(lean_object* v_v_645_){
_start:
{
uint64_t v_v_boxed_646_; lean_object* v_res_647_; 
v_v_boxed_646_ = lean_unbox_uint64(v_v_645_);
lean_dec_ref(v_v_645_);
v_res_647_ = l_Lean_instToJsonUInt64___lam__0(v_v_boxed_646_);
return v_res_647_;
}
}
lean_object* l_Lean_Float_toJson(double v_x_650_){
_start:
{
lean_object* v___x_651_; 
v___x_651_ = l_Lean_JsonNumber_fromFloat_x3f(v_x_650_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v_val_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_659_; 
v_val_652_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_659_ == 0)
{
v___x_654_ = v___x_651_;
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_val_652_);
lean_dec(v___x_651_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_657_; 
if (v_isShared_655_ == 0)
{
lean_ctor_set_tag(v___x_654_, 3);
v___x_657_ = v___x_654_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_val_652_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
else
{
lean_object* v_val_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_667_; 
v_val_660_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_667_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_667_ == 0)
{
v___x_662_ = v___x_651_;
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_val_660_);
lean_dec(v___x_651_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_665_; 
if (v_isShared_663_ == 0)
{
lean_ctor_set_tag(v___x_662_, 2);
v___x_665_ = v___x_662_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_val_660_);
v___x_665_ = v_reuseFailAlloc_666_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
return v___x_665_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Float_toJson_0interp(lean_interpreter_value* stack)
{
double v_x_650_ = stack[0].m_float;
lean_object* v_res_668_;
v_res_668_ = l_Lean_Float_toJson(v_x_650_);
stack->m_obj
 = v_res_668_;
}
LEAN_EXPORT lean_object* l_Lean_Float_toJson___boxed(lean_object* v_x_669_){
_start:
{
double v_x_boxed_670_; lean_object* v_res_671_; 
v_x_boxed_670_ = lean_unbox_float(v_x_669_);
lean_dec_ref(v_x_669_);
v_res_671_ = l_Lean_Float_toJson(v_x_boxed_670_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Float_fromJson_x3f(lean_object* v_x_680_){
_start:
{
switch(lean_obj_tag(v_x_680_))
{
case 3:
{
lean_object* v_s_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_722_; 
v_s_683_ = lean_ctor_get(v_x_680_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v_x_680_);
if (v_isSharedCheck_722_ == 0)
{
v___x_685_ = v_x_680_;
v_isShared_686_ = v_isSharedCheck_722_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_s_683_);
lean_dec(v_x_680_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_722_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_687_; uint8_t v___x_688_; 
v___x_687_ = ((lean_object*)(l_Lean_Float_fromJson_x3f___closed__2));
v___x_688_ = lean_string_dec_eq(v_s_683_, v___x_687_);
if (v___x_688_ == 0)
{
lean_object* v___x_689_; uint8_t v___x_690_; 
v___x_689_ = ((lean_object*)(l_Lean_Float_fromJson_x3f___closed__3));
v___x_690_ = lean_string_dec_eq(v_s_683_, v___x_689_);
if (v___x_690_ == 0)
{
lean_object* v___x_691_; uint8_t v___x_692_; 
v___x_691_ = ((lean_object*)(l_Lean_Float_fromJson_x3f___closed__4));
v___x_692_ = lean_string_dec_eq(v_s_683_, v___x_691_);
lean_dec_ref(v_s_683_);
if (v___x_692_ == 0)
{
lean_del_object(v___x_685_);
goto v___jp_681_;
}
else
{
lean_object* v___x_693_; lean_object* v___x_694_; double v___x_695_; double v___x_696_; lean_object* v___x_697_; lean_object* v___x_699_; 
v___x_693_ = lean_unsigned_to_nat(0u);
v___x_694_ = lean_unsigned_to_nat(1u);
v___x_695_ = l_Float_ofScientific(v___x_693_, v___x_692_, v___x_694_);
v___x_696_ = lean_float_div(v___x_695_, v___x_695_);
v___x_697_ = lean_box_float(v___x_696_);
if (v_isShared_686_ == 0)
{
lean_ctor_set_tag(v___x_685_, 1);
lean_ctor_set(v___x_685_, 0, v___x_697_);
v___x_699_ = v___x_685_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v___x_697_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
else
{
lean_object* v___x_701_; lean_object* v___x_702_; double v___x_703_; double v___x_704_; lean_object* v___x_705_; double v___x_706_; double v___x_707_; lean_object* v___x_708_; lean_object* v___x_710_; 
lean_dec_ref(v_s_683_);
v___x_701_ = lean_unsigned_to_nat(10u);
v___x_702_ = lean_unsigned_to_nat(1u);
v___x_703_ = l_Float_ofScientific(v___x_701_, v___x_690_, v___x_702_);
v___x_704_ = lean_float_negate(v___x_703_);
v___x_705_ = lean_unsigned_to_nat(0u);
v___x_706_ = l_Float_ofScientific(v___x_705_, v___x_690_, v___x_702_);
v___x_707_ = lean_float_div(v___x_704_, v___x_706_);
v___x_708_ = lean_box_float(v___x_707_);
if (v_isShared_686_ == 0)
{
lean_ctor_set_tag(v___x_685_, 1);
lean_ctor_set(v___x_685_, 0, v___x_708_);
v___x_710_ = v___x_685_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v___x_708_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
}
else
{
lean_object* v___x_712_; lean_object* v___x_713_; double v___x_714_; lean_object* v___x_715_; double v___x_716_; double v___x_717_; lean_object* v___x_718_; lean_object* v___x_720_; 
lean_dec_ref(v_s_683_);
v___x_712_ = lean_unsigned_to_nat(10u);
v___x_713_ = lean_unsigned_to_nat(1u);
v___x_714_ = l_Float_ofScientific(v___x_712_, v___x_688_, v___x_713_);
v___x_715_ = lean_unsigned_to_nat(0u);
v___x_716_ = l_Float_ofScientific(v___x_715_, v___x_688_, v___x_713_);
v___x_717_ = lean_float_div(v___x_714_, v___x_716_);
v___x_718_ = lean_box_float(v___x_717_);
if (v_isShared_686_ == 0)
{
lean_ctor_set_tag(v___x_685_, 1);
lean_ctor_set(v___x_685_, 0, v___x_718_);
v___x_720_ = v___x_685_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v___x_718_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
}
}
case 2:
{
lean_object* v_n_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_732_; 
v_n_723_ = lean_ctor_get(v_x_680_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v_x_680_);
if (v_isSharedCheck_732_ == 0)
{
v___x_725_ = v_x_680_;
v_isShared_726_ = v_isSharedCheck_732_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_n_723_);
lean_dec(v_x_680_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_732_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
double v___x_727_; lean_object* v___x_728_; lean_object* v___x_730_; 
v___x_727_ = l_Lean_JsonNumber_toFloat(v_n_723_);
v___x_728_ = lean_box_float(v___x_727_);
if (v_isShared_726_ == 0)
{
lean_ctor_set_tag(v___x_725_, 1);
lean_ctor_set(v___x_725_, 0, v___x_728_);
v___x_730_ = v___x_725_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v___x_728_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
default: 
{
lean_dec(v_x_680_);
goto v___jp_681_;
}
}
v___jp_681_:
{
lean_object* v___x_682_; 
v___x_682_ = ((lean_object*)(l_Lean_Float_fromJson_x3f___closed__1));
return v___x_682_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_fromJson_x3f(lean_object* v_x_736_){
_start:
{
switch(lean_obj_tag(v_x_736_))
{
case 4:
{
lean_object* v_elems_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_745_; 
v_elems_737_ = lean_ctor_get(v_x_736_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v_x_736_);
if (v_isSharedCheck_745_ == 0)
{
v___x_739_ = v_x_736_;
v_isShared_740_ = v_isSharedCheck_745_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_elems_737_);
lean_dec(v_x_736_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_745_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_742_; 
if (v_isShared_740_ == 0)
{
lean_ctor_set_tag(v___x_739_, 0);
v___x_742_ = v___x_739_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_elems_737_);
v___x_742_ = v_reuseFailAlloc_744_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
lean_object* v___x_743_; 
v___x_743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_743_, 0, v___x_742_);
return v___x_743_;
}
}
}
case 5:
{
lean_object* v_kvPairs_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_754_; 
v_kvPairs_746_ = lean_ctor_get(v_x_736_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v_x_736_);
if (v_isSharedCheck_754_ == 0)
{
v___x_748_ = v_x_736_;
v_isShared_749_ = v_isSharedCheck_754_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_kvPairs_746_);
lean_dec(v_x_736_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_754_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_751_; 
if (v_isShared_749_ == 0)
{
lean_ctor_set_tag(v___x_748_, 1);
v___x_751_ = v___x_748_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_kvPairs_746_);
v___x_751_ = v_reuseFailAlloc_753_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
lean_object* v___x_752_; 
v___x_752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_752_, 0, v___x_751_);
return v___x_752_;
}
}
}
default: 
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_755_ = ((lean_object*)(l_Lean_Json_Structured_fromJson_x3f___closed__0));
v___x_756_ = lean_unsigned_to_nat(80u);
v___x_757_ = l_Lean_Json_pretty(v_x_736_, v___x_756_);
v___x_758_ = lean_string_append(v___x_755_, v___x_757_);
lean_dec_ref(v___x_757_);
v___x_759_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___redArg___closed__11));
v___x_760_ = lean_string_append(v___x_758_, v___x_759_);
v___x_761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_761_, 0, v___x_760_);
return v___x_761_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_toJson(lean_object* v_x_764_){
_start:
{
if (lean_obj_tag(v_x_764_) == 0)
{
lean_object* v_elems_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_772_; 
v_elems_765_ = lean_ctor_get(v_x_764_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v_x_764_);
if (v_isSharedCheck_772_ == 0)
{
v___x_767_ = v_x_764_;
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_elems_765_);
lean_dec(v_x_764_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_770_; 
if (v_isShared_768_ == 0)
{
lean_ctor_set_tag(v___x_767_, 4);
v___x_770_ = v___x_767_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_elems_765_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
else
{
lean_object* v_kvPairs_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_780_; 
v_kvPairs_773_ = lean_ctor_get(v_x_764_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v_x_764_);
if (v_isSharedCheck_780_ == 0)
{
v___x_775_ = v_x_764_;
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_kvPairs_773_);
lean_dec(v_x_764_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_778_; 
if (v_isShared_776_ == 0)
{
lean_ctor_set_tag(v___x_775_, 5);
v___x_778_ = v___x_775_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_kvPairs_773_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___redArg(lean_object* v_inst_783_, lean_object* v_v_784_){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_785_ = lean_apply_1(v_inst_783_, v_v_784_);
v___x_786_ = l_Lean_Json_Structured_fromJson_x3f(v___x_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f(lean_object* v_00_u03b1_787_, lean_object* v_inst_788_, lean_object* v_v_789_){
_start:
{
lean_object* v___x_790_; 
v___x_790_ = l_Lean_Json_toStructured_x3f___redArg(v_inst_788_, v_v_789_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___redArg(lean_object* v_j_791_, lean_object* v_inst_792_, lean_object* v_k_793_){
_start:
{
lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_794_ = l_Lean_Json_getObjValD(v_j_791_, v_k_793_);
v___x_795_ = lean_apply_1(v_inst_792_, v___x_794_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___redArg___boxed(lean_object* v_j_796_, lean_object* v_inst_797_, lean_object* v_k_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_796_, v_inst_797_, v_k_798_);
lean_dec_ref(v_k_798_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f(lean_object* v_j_800_, lean_object* v_00_u03b1_801_, lean_object* v_inst_802_, lean_object* v_k_803_){
_start:
{
lean_object* v___x_804_; 
v___x_804_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_800_, v_inst_802_, v_k_803_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___boxed(lean_object* v_j_805_, lean_object* v_00_u03b1_806_, lean_object* v_inst_807_, lean_object* v_k_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Lean_Json_getObjValAs_x3f(v_j_805_, v_00_u03b1_806_, v_inst_807_, v_k_808_);
lean_dec_ref(v_k_808_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_setObjValAs_x21___redArg(lean_object* v_j_810_, lean_object* v_inst_811_, lean_object* v_k_812_, lean_object* v_v_813_){
_start:
{
lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_814_ = lean_apply_1(v_inst_811_, v_v_813_);
v___x_815_ = l_Lean_Json_setObjVal_x21(v_j_810_, v_k_812_, v___x_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_setObjValAs_x21(lean_object* v_j_816_, lean_object* v_00_u03b1_817_, lean_object* v_inst_818_, lean_object* v_k_819_, lean_object* v_v_820_){
_start:
{
lean_object* v___x_821_; 
v___x_821_ = l_Lean_Json_setObjValAs_x21___redArg(v_j_816_, v_inst_818_, v_k_819_, v_v_820_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___redArg(lean_object* v_inst_822_, lean_object* v_k_823_, lean_object* v_x_824_){
_start:
{
if (lean_obj_tag(v_x_824_) == 0)
{
lean_object* v___x_825_; 
lean_dec_ref(v_k_823_);
lean_dec_ref(v_inst_822_);
v___x_825_ = lean_box(0);
return v___x_825_;
}
else
{
lean_object* v_val_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v_val_826_ = lean_ctor_get(v_x_824_, 0);
lean_inc(v_val_826_);
lean_dec_ref_known(v_x_824_, 1);
v___x_827_ = lean_apply_1(v_inst_822_, v_val_826_);
v___x_828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_828_, 0, v_k_823_);
lean_ctor_set(v___x_828_, 1, v___x_827_);
v___x_829_ = lean_box(0);
v___x_830_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_830_, 0, v___x_828_);
lean_ctor_set(v___x_830_, 1, v___x_829_);
return v___x_830_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt(lean_object* v_00_u03b1_831_, lean_object* v_inst_832_, lean_object* v_k_833_, lean_object* v_x_834_){
_start:
{
lean_object* v___x_835_; 
v___x_835_ = l_Lean_Json_opt___redArg(v_inst_832_, v_k_833_, v_x_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getTag_x3f(lean_object* v_x_836_){
_start:
{
switch(lean_obj_tag(v_x_836_))
{
case 3:
{
lean_object* v_s_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_844_; 
v_s_837_ = lean_ctor_get(v_x_836_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v_x_836_);
if (v_isSharedCheck_844_ == 0)
{
v___x_839_ = v_x_836_;
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_s_837_);
lean_dec(v_x_836_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_842_; 
if (v_isShared_840_ == 0)
{
lean_ctor_set_tag(v___x_839_, 1);
v___x_842_ = v___x_839_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_s_837_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
case 5:
{
lean_object* v_kvPairs_845_; lean_object* v___y_847_; 
v_kvPairs_845_ = lean_ctor_get(v_x_836_, 0);
lean_inc(v_kvPairs_845_);
lean_dec_ref_known(v_x_836_, 1);
if (lean_obj_tag(v_kvPairs_845_) == 0)
{
lean_object* v_size_852_; 
v_size_852_ = lean_ctor_get(v_kvPairs_845_, 0);
lean_inc(v_size_852_);
v___y_847_ = v_size_852_;
goto v___jp_846_;
}
else
{
lean_object* v___x_853_; 
v___x_853_ = lean_unsigned_to_nat(0u);
v___y_847_ = v___x_853_;
goto v___jp_846_;
}
v___jp_846_:
{
lean_object* v___x_848_; uint8_t v___x_849_; 
v___x_848_ = lean_unsigned_to_nat(1u);
v___x_849_ = lean_nat_dec_eq(v___y_847_, v___x_848_);
lean_dec(v___y_847_);
if (v___x_849_ == 0)
{
lean_object* v___x_850_; 
lean_dec(v_kvPairs_845_);
v___x_850_ = lean_box(0);
return v___x_850_;
}
else
{
lean_object* v___x_851_; 
v___x_851_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_kvPairs_845_);
lean_dec(v_kvPairs_845_);
return v___x_851_;
}
}
}
default: 
{
lean_object* v___x_854_; 
lean_dec(v_x_836_);
v___x_854_ = lean_box(0);
return v___x_854_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Json_parseTagged_spec__0(lean_object* v_a_855_, lean_object* v_as_856_, size_t v_sz_857_, size_t v_i_858_, lean_object* v_b_859_){
_start:
{
uint8_t v___x_860_; 
v___x_860_ = lean_usize_dec_lt(v_i_858_, v_sz_857_);
if (v___x_860_ == 0)
{
lean_object* v___x_861_; 
lean_dec(v_a_855_);
v___x_861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_861_, 0, v_b_859_);
return v___x_861_;
}
else
{
lean_object* v_a_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v_a_862_ = lean_array_uget_borrowed(v_as_856_, v_i_858_);
v___x_863_ = l_Lean_Name_getString_x21(v_a_862_);
lean_inc(v_a_855_);
v___x_864_ = l_Lean_Json_getObjVal_x3f(v_a_855_, v___x_863_);
lean_dec_ref(v___x_863_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_872_; 
lean_dec_ref(v_b_859_);
lean_dec(v_a_855_);
v_a_865_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_872_ == 0)
{
v___x_867_ = v___x_864_;
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_864_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_870_; 
if (v_isShared_868_ == 0)
{
v___x_870_ = v___x_867_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_a_865_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
else
{
lean_object* v_a_873_; lean_object* v___x_874_; size_t v___x_875_; size_t v___x_876_; 
v_a_873_ = lean_ctor_get(v___x_864_, 0);
lean_inc(v_a_873_);
lean_dec_ref_known(v___x_864_, 1);
v___x_874_ = lean_array_push(v_b_859_, v_a_873_);
v___x_875_ = ((size_t)1ULL);
v___x_876_ = lean_usize_add(v_i_858_, v___x_875_);
v_i_858_ = v___x_876_;
v_b_859_ = v___x_874_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Json_parseTagged_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_855_ = stack[0].m_obj;
lean_object* v_as_856_ = stack[1].m_obj;
size_t v_sz_857_ = stack[2].m_num;
size_t v_i_858_ = stack[3].m_num;
lean_object* v_b_859_ = stack[4].m_obj;
lean_object* v_res_878_;
v_res_878_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Json_parseTagged_spec__0(v_a_855_, v_as_856_, v_sz_857_, v_i_858_, v_b_859_);
stack->m_obj
 = v_res_878_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Json_parseTagged_spec__0___boxed(lean_object* v_a_879_, lean_object* v_as_880_, lean_object* v_sz_881_, lean_object* v_i_882_, lean_object* v_b_883_){
_start:
{
size_t v_sz_boxed_884_; size_t v_i_boxed_885_; lean_object* v_res_886_; 
v_sz_boxed_884_ = lean_unbox_usize(v_sz_881_);
lean_dec(v_sz_881_);
v_i_boxed_885_ = lean_unbox_usize(v_i_882_);
lean_dec(v_i_882_);
v_res_886_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Json_parseTagged_spec__0(v_a_879_, v_as_880_, v_sz_boxed_884_, v_i_boxed_885_, v_b_883_);
lean_dec_ref(v_as_880_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_parseTagged(lean_object* v_json_894_, lean_object* v_tag_895_, lean_object* v_nFields_896_, lean_object* v_fieldNames_x3f_897_){
_start:
{
lean_object* v___x_898_; uint8_t v___x_899_; 
v___x_898_ = lean_unsigned_to_nat(0u);
v___x_899_ = lean_nat_dec_eq(v_nFields_896_, v___x_898_);
if (v___x_899_ == 0)
{
lean_object* v___x_900_; 
v___x_900_ = l_Lean_Json_getObjVal_x3f(v_json_894_, v_tag_895_);
if (lean_obj_tag(v___x_900_) == 0)
{
lean_object* v_a_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_908_; 
lean_dec(v_nFields_896_);
v_a_901_ = lean_ctor_get(v___x_900_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_908_ == 0)
{
v___x_903_ = v___x_900_;
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_a_901_);
lean_dec(v___x_900_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_906_; 
if (v_isShared_904_ == 0)
{
v___x_906_ = v___x_903_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_a_901_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
}
else
{
if (lean_obj_tag(v_fieldNames_x3f_897_) == 0)
{
lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_939_; 
v_a_909_ = lean_ctor_get(v___x_900_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_939_ == 0)
{
v___x_911_ = v___x_900_;
v_isShared_912_ = v_isSharedCheck_939_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v___x_900_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_939_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_913_; uint8_t v___x_914_; 
v___x_913_ = lean_unsigned_to_nat(1u);
v___x_914_ = lean_nat_dec_eq(v_nFields_896_, v___x_913_);
if (v___x_914_ == 0)
{
lean_object* v___x_915_; 
lean_del_object(v___x_911_);
v___x_915_ = l_Lean_Json_getArr_x3f(v_a_909_);
if (lean_obj_tag(v___x_915_) == 0)
{
lean_dec(v_nFields_896_);
return v___x_915_;
}
else
{
lean_object* v_a_916_; lean_object* v___x_917_; uint8_t v___x_918_; 
v_a_916_ = lean_ctor_get(v___x_915_, 0);
v___x_917_ = lean_array_get_size(v_a_916_);
v___x_918_ = lean_nat_dec_eq(v___x_917_, v_nFields_896_);
if (v___x_918_ == 0)
{
lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_932_; 
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_932_ == 0)
{
lean_object* v_unused_933_; 
v_unused_933_ = lean_ctor_get(v___x_915_, 0);
lean_dec(v_unused_933_);
v___x_920_ = v___x_915_;
v_isShared_921_ = v_isSharedCheck_932_;
goto v_resetjp_919_;
}
else
{
lean_dec(v___x_915_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_932_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_930_; 
v___x_922_ = ((lean_object*)(l_Lean_Json_parseTagged___closed__0));
v___x_923_ = l_Nat_reprFast(v___x_917_);
v___x_924_ = lean_string_append(v___x_922_, v___x_923_);
lean_dec_ref(v___x_923_);
v___x_925_ = ((lean_object*)(l_Lean_Json_parseTagged___closed__1));
v___x_926_ = lean_string_append(v___x_924_, v___x_925_);
v___x_927_ = l_Nat_reprFast(v_nFields_896_);
v___x_928_ = lean_string_append(v___x_926_, v___x_927_);
lean_dec_ref(v___x_927_);
if (v_isShared_921_ == 0)
{
lean_ctor_set_tag(v___x_920_, 0);
lean_ctor_set(v___x_920_, 0, v___x_928_);
v___x_930_ = v___x_920_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v___x_928_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
else
{
lean_dec(v_nFields_896_);
return v___x_915_;
}
}
}
else
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_937_; 
lean_dec(v_nFields_896_);
v___x_934_ = lean_mk_empty_array_with_capacity(v___x_913_);
v___x_935_ = lean_array_push(v___x_934_, v_a_909_);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 0, v___x_935_);
v___x_937_ = v___x_911_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v___x_935_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
}
else
{
lean_object* v_a_940_; lean_object* v_val_941_; lean_object* v_fields_942_; size_t v_sz_943_; size_t v___x_944_; lean_object* v___x_945_; 
lean_dec(v_nFields_896_);
v_a_940_ = lean_ctor_get(v___x_900_, 0);
lean_inc(v_a_940_);
lean_dec_ref_known(v___x_900_, 1);
v_val_941_ = lean_ctor_get(v_fieldNames_x3f_897_, 0);
v_fields_942_ = ((lean_object*)(l_Lean_Json_parseTagged___closed__2));
v_sz_943_ = lean_array_size(v_val_941_);
v___x_944_ = ((size_t)0ULL);
v___x_945_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Json_parseTagged_spec__0(v_a_940_, v_val_941_, v_sz_943_, v___x_944_, v_fields_942_);
return v___x_945_;
}
}
}
else
{
lean_object* v___x_946_; 
lean_dec(v_nFields_896_);
v___x_946_ = l_Lean_Json_getStr_x3f(v_json_894_);
if (lean_obj_tag(v___x_946_) == 0)
{
lean_object* v_a_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_954_; 
v_a_947_ = lean_ctor_get(v___x_946_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v___x_946_);
if (v_isSharedCheck_954_ == 0)
{
v___x_949_ = v___x_946_;
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_a_947_);
lean_dec(v___x_946_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_952_; 
if (v_isShared_950_ == 0)
{
v___x_952_ = v___x_949_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v_a_947_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
}
else
{
lean_object* v_a_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_969_; 
v_a_955_ = lean_ctor_get(v___x_946_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_946_);
if (v_isSharedCheck_969_ == 0)
{
v___x_957_ = v___x_946_;
v_isShared_958_ = v_isSharedCheck_969_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_a_955_);
lean_dec(v___x_946_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_969_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
uint8_t v___x_959_; 
v___x_959_ = lean_string_dec_eq(v_a_955_, v_tag_895_);
if (v___x_959_ == 0)
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_966_; 
v___x_960_ = ((lean_object*)(l_Lean_Json_parseTagged___closed__3));
v___x_961_ = lean_string_append(v___x_960_, v_a_955_);
lean_dec(v_a_955_);
v___x_962_ = ((lean_object*)(l_Lean_Json_parseTagged___closed__1));
v___x_963_ = lean_string_append(v___x_961_, v___x_962_);
v___x_964_ = lean_string_append(v___x_963_, v_tag_895_);
if (v_isShared_958_ == 0)
{
lean_ctor_set_tag(v___x_957_, 0);
lean_ctor_set(v___x_957_, 0, v___x_964_);
v___x_966_ = v___x_957_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v___x_964_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
else
{
lean_object* v___x_968_; 
lean_del_object(v___x_957_);
lean_dec(v_a_955_);
v___x_968_ = ((lean_object*)(l_Lean_Json_parseTagged___closed__4));
return v___x_968_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_parseTagged___boxed(lean_object* v_json_970_, lean_object* v_tag_971_, lean_object* v_nFields_972_, lean_object* v_fieldNames_x3f_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_Lean_Json_parseTagged(v_json_970_, v_tag_971_, v_nFields_972_, v_fieldNames_x3f_973_);
lean_dec(v_fieldNames_x3f_973_);
lean_dec_ref(v_tag_971_);
return v_res_974_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_parseCtorFields_spec__0(lean_object* v_a_975_, size_t v_sz_976_, size_t v_i_977_, lean_object* v_bs_978_){
_start:
{
uint8_t v___x_979_; 
v___x_979_ = lean_usize_dec_lt(v_i_977_, v_sz_976_);
if (v___x_979_ == 0)
{
lean_object* v___x_980_; 
lean_dec(v_a_975_);
v___x_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_980_, 0, v_bs_978_);
return v___x_980_;
}
else
{
lean_object* v_v_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
v_v_981_ = lean_array_uget_borrowed(v_bs_978_, v_i_977_);
v___x_982_ = l_Lean_Name_getString_x21(v_v_981_);
lean_inc(v_a_975_);
v___x_983_ = l_Lean_Json_getObjVal_x3f(v_a_975_, v___x_982_);
lean_dec_ref(v___x_982_);
if (lean_obj_tag(v___x_983_) == 0)
{
lean_object* v_a_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_991_; 
lean_dec_ref(v_bs_978_);
lean_dec(v_a_975_);
v_a_984_ = lean_ctor_get(v___x_983_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_991_ == 0)
{
v___x_986_ = v___x_983_;
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_a_984_);
lean_dec(v___x_983_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_989_; 
if (v_isShared_987_ == 0)
{
v___x_989_ = v___x_986_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_a_984_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
}
else
{
lean_object* v_a_992_; lean_object* v___x_993_; lean_object* v_bs_x27_994_; size_t v___x_995_; size_t v___x_996_; lean_object* v___x_997_; 
v_a_992_ = lean_ctor_get(v___x_983_, 0);
lean_inc(v_a_992_);
lean_dec_ref_known(v___x_983_, 1);
v___x_993_ = lean_unsigned_to_nat(0u);
v_bs_x27_994_ = lean_array_uset(v_bs_978_, v_i_977_, v___x_993_);
v___x_995_ = ((size_t)1ULL);
v___x_996_ = lean_usize_add(v_i_977_, v___x_995_);
v___x_997_ = lean_array_uset(v_bs_x27_994_, v_i_977_, v_a_992_);
v_i_977_ = v___x_996_;
v_bs_978_ = v___x_997_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_parseCtorFields_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_975_ = stack[0].m_obj;
size_t v_sz_976_ = stack[1].m_num;
size_t v_i_977_ = stack[2].m_num;
lean_object* v_bs_978_ = stack[3].m_obj;
lean_object* v_res_999_;
v_res_999_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_parseCtorFields_spec__0(v_a_975_, v_sz_976_, v_i_977_, v_bs_978_);
stack->m_obj
 = v_res_999_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_parseCtorFields_spec__0___boxed(lean_object* v_a_1000_, lean_object* v_sz_1001_, lean_object* v_i_1002_, lean_object* v_bs_1003_){
_start:
{
size_t v_sz_boxed_1004_; size_t v_i_boxed_1005_; lean_object* v_res_1006_; 
v_sz_boxed_1004_ = lean_unbox_usize(v_sz_1001_);
lean_dec(v_sz_1001_);
v_i_boxed_1005_ = lean_unbox_usize(v_i_1002_);
lean_dec(v_i_1002_);
v_res_1006_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_parseCtorFields_spec__0(v_a_1000_, v_sz_boxed_1004_, v_i_boxed_1005_, v_bs_1003_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_parseCtorFields(lean_object* v_json_1007_, lean_object* v_tag_1008_, lean_object* v_nFields_1009_, lean_object* v_fieldNames_x3f_1010_){
_start:
{
lean_object* v___x_1011_; 
v___x_1011_ = l_Lean_Json_getObjVal_x3f(v_json_1007_, v_tag_1008_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_object* v_a_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1019_; 
lean_dec(v_fieldNames_x3f_1010_);
lean_dec(v_nFields_1009_);
v_a_1012_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1014_ = v___x_1011_;
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_a_1012_);
lean_dec(v___x_1011_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1017_; 
if (v_isShared_1015_ == 0)
{
v___x_1017_ = v___x_1014_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_a_1012_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
}
else
{
if (lean_obj_tag(v_fieldNames_x3f_1010_) == 0)
{
lean_object* v_a_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1050_; 
v_a_1020_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1022_ = v___x_1011_;
v_isShared_1023_ = v_isSharedCheck_1050_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_a_1020_);
lean_dec(v___x_1011_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1050_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1024_; uint8_t v___x_1025_; 
v___x_1024_ = lean_unsigned_to_nat(1u);
v___x_1025_ = lean_nat_dec_eq(v_nFields_1009_, v___x_1024_);
if (v___x_1025_ == 0)
{
lean_object* v___x_1026_; 
lean_del_object(v___x_1022_);
v___x_1026_ = l_Lean_Json_getArr_x3f(v_a_1020_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_dec(v_nFields_1009_);
return v___x_1026_;
}
else
{
lean_object* v_a_1027_; lean_object* v___x_1028_; uint8_t v___x_1029_; 
v_a_1027_ = lean_ctor_get(v___x_1026_, 0);
v___x_1028_ = lean_array_get_size(v_a_1027_);
v___x_1029_ = lean_nat_dec_eq(v___x_1028_, v_nFields_1009_);
if (v___x_1029_ == 0)
{
lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1043_; 
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1043_ == 0)
{
lean_object* v_unused_1044_; 
v_unused_1044_ = lean_ctor_get(v___x_1026_, 0);
lean_dec(v_unused_1044_);
v___x_1031_ = v___x_1026_;
v_isShared_1032_ = v_isSharedCheck_1043_;
goto v_resetjp_1030_;
}
else
{
lean_dec(v___x_1026_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1043_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1041_; 
v___x_1033_ = ((lean_object*)(l_Lean_Json_parseTagged___closed__0));
v___x_1034_ = l_Nat_reprFast(v___x_1028_);
v___x_1035_ = lean_string_append(v___x_1033_, v___x_1034_);
lean_dec_ref(v___x_1034_);
v___x_1036_ = ((lean_object*)(l_Lean_Json_parseTagged___closed__1));
v___x_1037_ = lean_string_append(v___x_1035_, v___x_1036_);
v___x_1038_ = l_Nat_reprFast(v_nFields_1009_);
v___x_1039_ = lean_string_append(v___x_1037_, v___x_1038_);
lean_dec_ref(v___x_1038_);
if (v_isShared_1032_ == 0)
{
lean_ctor_set_tag(v___x_1031_, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1039_);
v___x_1041_ = v___x_1031_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_dec(v_nFields_1009_);
return v___x_1026_;
}
}
}
else
{
lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1048_; 
lean_dec(v_nFields_1009_);
v___x_1045_ = lean_mk_empty_array_with_capacity(v___x_1024_);
v___x_1046_ = lean_array_push(v___x_1045_, v_a_1020_);
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 0, v___x_1046_);
v___x_1048_ = v___x_1022_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1046_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
}
else
{
lean_object* v_a_1051_; lean_object* v_val_1052_; size_t v_sz_1053_; size_t v___x_1054_; lean_object* v___x_1055_; 
lean_dec(v_nFields_1009_);
v_a_1051_ = lean_ctor_get(v___x_1011_, 0);
lean_inc(v_a_1051_);
lean_dec_ref_known(v___x_1011_, 1);
v_val_1052_ = lean_ctor_get(v_fieldNames_x3f_1010_, 0);
lean_inc(v_val_1052_);
lean_dec_ref_known(v_fieldNames_x3f_1010_, 1);
v_sz_1053_ = lean_array_size(v_val_1052_);
v___x_1054_ = ((size_t)0ULL);
v___x_1055_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_parseCtorFields_spec__0(v_a_1051_, v_sz_1053_, v___x_1054_, v_val_1052_);
return v___x_1055_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_parseCtorFields___boxed(lean_object* v_json_1056_, lean_object* v_tag_1057_, lean_object* v_nFields_1058_, lean_object* v_fieldNames_x3f_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_Lean_Json_parseCtorFields(v_json_1056_, v_tag_1057_, v_nFields_1058_, v_fieldNames_x3f_1059_);
lean_dec_ref(v_tag_1057_);
return v_res_1060_;
}
}
lean_object* runtime_initialize_Lean_Data_Json_Printer(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_GetLit(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Json_FromToJson_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
