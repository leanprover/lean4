// Lean compiler output
// Module: Lake.Toml.Decode
// Imports: public import Init.System.FilePath public import Lake.Toml.Data import Init.Data.ToString.Macro
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
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lake_Toml_ppKey(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_push___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_mapFinIdxM_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
lean_object* l_Lake_Toml_RBDict_findEntry_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_String_toName(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_decodeToml___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_decodeToml(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_ensureDecode___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_ensureDecode(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_tryDecodeD___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_tryDecodeD(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_tryDecode_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_tryDecode_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_tryDecode___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_tryDecode(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_optDecodeD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_optDecodeD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_optDecode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_optDecode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_optDecode_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_optDecode_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_mergeErrors___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_mergeErrors(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_throwDecodeErrorAt___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_throwDecodeErrorAt(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_Toml_decodeArray___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_push___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lake_Toml_decodeArray___redArg___lam__0___closed__0 = (const lean_object*)&l_Lake_Toml_decodeArray___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_Toml_decodeArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Toml_decodeArray___redArg___closed__0 = (const lean_object*)&l_Lake_Toml_decodeArray___redArg___closed__0_value;
static const lean_closure_object l_Lake_Toml_decodeArray___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Toml_decodeArray___redArg___closed__1 = (const lean_object*)&l_Lake_Toml_decodeArray___redArg___closed__1_value;
static const lean_closure_object l_Lake_Toml_decodeArray___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Toml_decodeArray___redArg___closed__2 = (const lean_object*)&l_Lake_Toml_decodeArray___redArg___closed__2_value;
static const lean_closure_object l_Lake_Toml_decodeArray___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Toml_decodeArray___redArg___closed__3 = (const lean_object*)&l_Lake_Toml_decodeArray___redArg___closed__3_value;
static const lean_closure_object l_Lake_Toml_decodeArray___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Toml_decodeArray___redArg___closed__4 = (const lean_object*)&l_Lake_Toml_decodeArray___redArg___closed__4_value;
static const lean_closure_object l_Lake_Toml_decodeArray___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Toml_decodeArray___redArg___closed__5 = (const lean_object*)&l_Lake_Toml_decodeArray___redArg___closed__5_value;
static const lean_closure_object l_Lake_Toml_decodeArray___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Toml_decodeArray___redArg___closed__6 = (const lean_object*)&l_Lake_Toml_decodeArray___redArg___closed__6_value;
static const lean_ctor_object l_Lake_Toml_decodeArray___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Toml_decodeArray___redArg___closed__0_value),((lean_object*)&l_Lake_Toml_decodeArray___redArg___closed__1_value)}};
static const lean_object* l_Lake_Toml_decodeArray___redArg___closed__7 = (const lean_object*)&l_Lake_Toml_decodeArray___redArg___closed__7_value;
static const lean_ctor_object l_Lake_Toml_decodeArray___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Toml_decodeArray___redArg___closed__7_value),((lean_object*)&l_Lake_Toml_decodeArray___redArg___closed__2_value),((lean_object*)&l_Lake_Toml_decodeArray___redArg___closed__3_value),((lean_object*)&l_Lake_Toml_decodeArray___redArg___closed__4_value),((lean_object*)&l_Lake_Toml_decodeArray___redArg___closed__5_value)}};
static const lean_object* l_Lake_Toml_decodeArray___redArg___closed__8 = (const lean_object*)&l_Lake_Toml_decodeArray___redArg___closed__8_value;
static const lean_ctor_object l_Lake_Toml_decodeArray___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Toml_decodeArray___redArg___closed__8_value),((lean_object*)&l_Lake_Toml_decodeArray___redArg___closed__6_value)}};
static const lean_object* l_Lake_Toml_decodeArray___redArg___closed__9 = (const lean_object*)&l_Lake_Toml_decodeArray___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_Toml_Decode_0__Lake_Toml_instDecodeTomlValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_pure, .m_arity = 5, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lake_Toml_Decode_0__Lake_Toml_instDecodeTomlValue___closed__0 = (const lean_object*)&l___private_Lake_Toml_Decode_0__Lake_Toml_instDecodeTomlValue___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_Toml_Decode_0__Lake_Toml_instDecodeTomlValue = (const lean_object*)&l___private_Lake_Toml_Decode_0__Lake_Toml_instDecodeTomlValue___closed__0_value;
static const lean_string_object l_Lake_Toml_Value_decodeString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "expected string"};
static const lean_object* l_Lake_Toml_Value_decodeString___closed__0 = (const lean_object*)&l_Lake_Toml_Value_decodeString___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Toml_Value_decodeString(lean_object*, lean_object*);
static const lean_closure_object l_Lake_Toml_Value_instDecodeTomlString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Toml_Value_decodeString, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Toml_Value_instDecodeTomlString___closed__0 = (const lean_object*)&l_Lake_Toml_Value_instDecodeTomlString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Toml_Value_instDecodeTomlString = (const lean_object*)&l_Lake_Toml_Value_instDecodeTomlString___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Toml_Value_instDecodeTomlFilePath___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lake_Toml_Value_instDecodeTomlFilePath___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Toml_Value_instDecodeTomlFilePath___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Toml_Value_instDecodeTomlFilePath___closed__0 = (const lean_object*)&l_Lake_Toml_Value_instDecodeTomlFilePath___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Toml_Value_instDecodeTomlFilePath = (const lean_object*)&l_Lake_Toml_Value_instDecodeTomlFilePath___closed__0_value;
static const lean_string_object l_Lake_Toml_Value_decodeName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected name"};
static const lean_object* l_Lake_Toml_Value_decodeName___closed__0 = (const lean_object*)&l_Lake_Toml_Value_decodeName___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Toml_Value_decodeName(lean_object*, lean_object*);
static const lean_closure_object l_Lake_Toml_Value_instDecodeTomlName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Toml_Value_decodeName, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Toml_Value_instDecodeTomlName___closed__0 = (const lean_object*)&l_Lake_Toml_Value_instDecodeTomlName___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Toml_Value_instDecodeTomlName = (const lean_object*)&l_Lake_Toml_Value_instDecodeTomlName___closed__0_value;
static const lean_string_object l_Lake_Toml_Value_decodeInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "expected integer"};
static const lean_object* l_Lake_Toml_Value_decodeInt___closed__0 = (const lean_object*)&l_Lake_Toml_Value_decodeInt___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Toml_Value_decodeInt(lean_object*, lean_object*);
static const lean_closure_object l_Lake_Toml_Value_instDecodeTomlInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Toml_Value_decodeInt, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Toml_Value_instDecodeTomlInt___closed__0 = (const lean_object*)&l_Lake_Toml_Value_instDecodeTomlInt___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Toml_Value_instDecodeTomlInt = (const lean_object*)&l_Lake_Toml_Value_instDecodeTomlInt___closed__0_value;
static const lean_string_object l_Lake_Toml_Value_decodeNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "expected nonnegative integer"};
static const lean_object* l_Lake_Toml_Value_decodeNat___closed__0 = (const lean_object*)&l_Lake_Toml_Value_decodeNat___closed__0_value;
static lean_once_cell_t l_Lake_Toml_Value_decodeNat___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_Value_decodeNat___closed__1;
LEAN_EXPORT lean_object* l_Lake_Toml_Value_decodeNat(lean_object*, lean_object*);
static const lean_closure_object l_Lake_Toml_Value_instDecodeTomlNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Toml_Value_decodeNat, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Toml_Value_instDecodeTomlNat___closed__0 = (const lean_object*)&l_Lake_Toml_Value_instDecodeTomlNat___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Toml_Value_instDecodeTomlNat = (const lean_object*)&l_Lake_Toml_Value_instDecodeTomlNat___closed__0_value;
static const lean_string_object l_Lake_Toml_Value_decodeFloat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "expected float"};
static const lean_object* l_Lake_Toml_Value_decodeFloat___closed__0 = (const lean_object*)&l_Lake_Toml_Value_decodeFloat___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Toml_Value_decodeFloat(lean_object*, lean_object*);
static const lean_closure_object l_Lake_Toml_Value_instDecodeTomlFloat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Toml_Value_decodeFloat, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Toml_Value_instDecodeTomlFloat___closed__0 = (const lean_object*)&l_Lake_Toml_Value_instDecodeTomlFloat___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Toml_Value_instDecodeTomlFloat = (const lean_object*)&l_Lake_Toml_Value_instDecodeTomlFloat___closed__0_value;
static const lean_string_object l_Lake_Toml_Value_decodeBool___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "expected boolean"};
static const lean_object* l_Lake_Toml_Value_decodeBool___closed__0 = (const lean_object*)&l_Lake_Toml_Value_decodeBool___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Toml_Value_decodeBool(lean_object*, lean_object*);
static const lean_closure_object l_Lake_Toml_Value_instDecodeTomlBool___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Toml_Value_decodeBool, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Toml_Value_instDecodeTomlBool___closed__0 = (const lean_object*)&l_Lake_Toml_Value_instDecodeTomlBool___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Toml_Value_instDecodeTomlBool = (const lean_object*)&l_Lake_Toml_Value_instDecodeTomlBool___closed__0_value;
static const lean_string_object l_Lake_Toml_Value_decodeDateTime___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "expected date-time"};
static const lean_object* l_Lake_Toml_Value_decodeDateTime___closed__0 = (const lean_object*)&l_Lake_Toml_Value_decodeDateTime___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Toml_Value_decodeDateTime(lean_object*, lean_object*);
static const lean_closure_object l_Lake_Toml_Value_instDecodeTomlDateTime___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Toml_Value_decodeDateTime, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Toml_Value_instDecodeTomlDateTime___closed__0 = (const lean_object*)&l_Lake_Toml_Value_instDecodeTomlDateTime___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Toml_Value_instDecodeTomlDateTime = (const lean_object*)&l_Lake_Toml_Value_instDecodeTomlDateTime___closed__0_value;
static const lean_string_object l_Lake_Toml_Value_decodeValueArray___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "expected array"};
static const lean_object* l_Lake_Toml_Value_decodeValueArray___closed__0 = (const lean_object*)&l_Lake_Toml_Value_decodeValueArray___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Toml_Value_decodeValueArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Value_decodeArray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Value_decodeArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Value_instDecodeTomlArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Value_instDecodeTomlArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Value_decodeArrayOrSingleton___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Value_decodeArrayOrSingleton(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Toml_Value_decodeTable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "expected table"};
static const lean_object* l_Lake_Toml_Value_decodeTable___closed__0 = (const lean_object*)&l_Lake_Toml_Value_decodeTable___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Toml_Value_decodeTable(lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_Toml_Decode_0__Lake_Toml_Value_instDecodeTomlTable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Toml_Value_decodeTable, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Toml_Decode_0__Lake_Toml_Value_instDecodeTomlTable___closed__0 = (const lean_object*)&l___private_Lake_Toml_Decode_0__Lake_Toml_Value_instDecodeTomlTable___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_Toml_Decode_0__Lake_Toml_Value_instDecodeTomlTable = (const lean_object*)&l___private_Lake_Toml_Decode_0__Lake_Toml_Value_instDecodeTomlTable___closed__0_value;
static const lean_string_object l_Lake_Toml_decodeKeyval___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "key "};
static const lean_object* l_Lake_Toml_decodeKeyval___redArg___lam__0___closed__0 = (const lean_object*)&l_Lake_Toml_decodeKeyval___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lake_Toml_decodeKeyval___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lake_Toml_decodeKeyval___redArg___lam__0___closed__1 = (const lean_object*)&l_Lake_Toml_decodeKeyval___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Toml_decodeKeyval___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_decodeKeyval___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_decodeKeyval___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_decodeKeyval___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_decodeKeyval(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_Toml_Table_decodeValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Toml_Table_decodeValue___closed__0 = (const lean_object*)&l_Lake_Toml_Table_decodeValue___closed__0_value;
static const lean_string_object l_Lake_Toml_Table_decodeValue___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "missing required key: "};
static const lean_object* l_Lake_Toml_Table_decodeValue___closed__1 = (const lean_object*)&l_Lake_Toml_Table_decodeValue___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decodeValue(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decode___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decode_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decode_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decodeNameMap___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decodeNameMap___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_Toml_Table_decodeNameMap___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_pure, .m_arity = 5, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lake_Toml_Table_decodeNameMap___redArg___closed__0 = (const lean_object*)&l_Lake_Toml_Table_decodeNameMap___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decodeNameMap___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decodeNameMap(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Table_instDecodeTomlNameMap___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Table_instDecodeTomlNameMap___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Table_instDecodeTomlNameMap(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Table_tryDecode___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Table_tryDecode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Table_tryDecode_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Table_tryDecode_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Table_tryDecodeD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Table_tryDecodeD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_decodeToml___redArg(lean_object* v_inst_1_, lean_object* v_v_2_, lean_object* v_a_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_apply_2(v_inst_1_, v_v_2_, v_a_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Lake_decodeToml(lean_object* v_00_u03b1_5_, lean_object* v_inst_6_, lean_object* v_v_7_, lean_object* v_a_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_apply_2(v_inst_6_, v_v_7_, v_a_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ensureDecode___redArg(lean_object* v_x_10_, lean_object* v_es_11_){
_start:
{
lean_object* v___x_12_; lean_object* v_a_13_; lean_object* v_a_14_; lean_object* v___x_16_; uint8_t v_isShared_17_; uint8_t v_isSharedCheck_28_; 
v___x_12_ = lean_apply_1(v_x_10_, v_es_11_);
v_a_13_ = lean_ctor_get(v___x_12_, 0);
v_a_14_ = lean_ctor_get(v___x_12_, 1);
v_isSharedCheck_28_ = !lean_is_exclusive(v___x_12_);
if (v_isSharedCheck_28_ == 0)
{
v___x_16_ = v___x_12_;
v_isShared_17_ = v_isSharedCheck_28_;
goto v_resetjp_15_;
}
else
{
lean_inc(v_a_14_);
lean_inc(v_a_13_);
lean_dec(v___x_12_);
v___x_16_ = lean_box(0);
v_isShared_17_ = v_isSharedCheck_28_;
goto v_resetjp_15_;
}
v_resetjp_15_:
{
lean_object* v___x_18_; lean_object* v___x_19_; uint8_t v___x_20_; 
v___x_18_ = lean_array_get_size(v_a_14_);
v___x_19_ = lean_unsigned_to_nat(0u);
v___x_20_ = lean_nat_dec_eq(v___x_18_, v___x_19_);
if (v___x_20_ == 0)
{
lean_object* v___x_21_; lean_object* v___x_23_; 
lean_dec(v_a_13_);
v___x_21_ = lean_box(0);
if (v_isShared_17_ == 0)
{
lean_ctor_set_tag(v___x_16_, 1);
lean_ctor_set(v___x_16_, 0, v___x_21_);
v___x_23_ = v___x_16_;
goto v_reusejp_22_;
}
else
{
lean_object* v_reuseFailAlloc_24_; 
v_reuseFailAlloc_24_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_24_, 0, v___x_21_);
lean_ctor_set(v_reuseFailAlloc_24_, 1, v_a_14_);
v___x_23_ = v_reuseFailAlloc_24_;
goto v_reusejp_22_;
}
v_reusejp_22_:
{
return v___x_23_;
}
}
else
{
lean_object* v___x_26_; 
if (v_isShared_17_ == 0)
{
v___x_26_ = v___x_16_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_a_13_);
lean_ctor_set(v_reuseFailAlloc_27_, 1, v_a_14_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ensureDecode(lean_object* v_00_u03b1_29_, lean_object* v_x_30_, lean_object* v_es_31_){
_start:
{
lean_object* v___x_32_; lean_object* v_a_33_; lean_object* v_a_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_48_; 
v___x_32_ = lean_apply_1(v_x_30_, v_es_31_);
v_a_33_ = lean_ctor_get(v___x_32_, 0);
v_a_34_ = lean_ctor_get(v___x_32_, 1);
v_isSharedCheck_48_ = !lean_is_exclusive(v___x_32_);
if (v_isSharedCheck_48_ == 0)
{
v___x_36_ = v___x_32_;
v_isShared_37_ = v_isSharedCheck_48_;
goto v_resetjp_35_;
}
else
{
lean_inc(v_a_34_);
lean_inc(v_a_33_);
lean_dec(v___x_32_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_48_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
lean_object* v___x_38_; lean_object* v___x_39_; uint8_t v___x_40_; 
v___x_38_ = lean_array_get_size(v_a_34_);
v___x_39_ = lean_unsigned_to_nat(0u);
v___x_40_ = lean_nat_dec_eq(v___x_38_, v___x_39_);
if (v___x_40_ == 0)
{
lean_object* v___x_41_; lean_object* v___x_43_; 
lean_dec(v_a_33_);
v___x_41_ = lean_box(0);
if (v_isShared_37_ == 0)
{
lean_ctor_set_tag(v___x_36_, 1);
lean_ctor_set(v___x_36_, 0, v___x_41_);
v___x_43_ = v___x_36_;
goto v_reusejp_42_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v___x_41_);
lean_ctor_set(v_reuseFailAlloc_44_, 1, v_a_34_);
v___x_43_ = v_reuseFailAlloc_44_;
goto v_reusejp_42_;
}
v_reusejp_42_:
{
return v___x_43_;
}
}
else
{
lean_object* v___x_46_; 
if (v_isShared_37_ == 0)
{
v___x_46_ = v___x_36_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_47_; 
v_reuseFailAlloc_47_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_47_, 0, v_a_33_);
lean_ctor_set(v_reuseFailAlloc_47_, 1, v_a_34_);
v___x_46_ = v_reuseFailAlloc_47_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
return v___x_46_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_tryDecodeD___redArg(lean_object* v_default_49_, lean_object* v_x_50_, lean_object* v_es_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = lean_apply_1(v_x_50_, v_es_51_);
if (lean_obj_tag(v___x_52_) == 0)
{
lean_object* v_a_53_; lean_object* v_a_54_; lean_object* v___x_56_; uint8_t v_isShared_57_; uint8_t v_isSharedCheck_61_; 
lean_dec(v_default_49_);
v_a_53_ = lean_ctor_get(v___x_52_, 0);
v_a_54_ = lean_ctor_get(v___x_52_, 1);
v_isSharedCheck_61_ = !lean_is_exclusive(v___x_52_);
if (v_isSharedCheck_61_ == 0)
{
v___x_56_ = v___x_52_;
v_isShared_57_ = v_isSharedCheck_61_;
goto v_resetjp_55_;
}
else
{
lean_inc(v_a_54_);
lean_inc(v_a_53_);
lean_dec(v___x_52_);
v___x_56_ = lean_box(0);
v_isShared_57_ = v_isSharedCheck_61_;
goto v_resetjp_55_;
}
v_resetjp_55_:
{
lean_object* v___x_59_; 
if (v_isShared_57_ == 0)
{
v___x_59_ = v___x_56_;
goto v_reusejp_58_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v_a_53_);
lean_ctor_set(v_reuseFailAlloc_60_, 1, v_a_54_);
v___x_59_ = v_reuseFailAlloc_60_;
goto v_reusejp_58_;
}
v_reusejp_58_:
{
return v___x_59_;
}
}
}
else
{
lean_object* v_a_62_; lean_object* v___x_64_; uint8_t v_isShared_65_; uint8_t v_isSharedCheck_69_; 
v_a_62_ = lean_ctor_get(v___x_52_, 1);
v_isSharedCheck_69_ = !lean_is_exclusive(v___x_52_);
if (v_isSharedCheck_69_ == 0)
{
lean_object* v_unused_70_; 
v_unused_70_ = lean_ctor_get(v___x_52_, 0);
lean_dec(v_unused_70_);
v___x_64_ = v___x_52_;
v_isShared_65_ = v_isSharedCheck_69_;
goto v_resetjp_63_;
}
else
{
lean_inc(v_a_62_);
lean_dec(v___x_52_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_69_;
goto v_resetjp_63_;
}
v_resetjp_63_:
{
lean_object* v___x_67_; 
if (v_isShared_65_ == 0)
{
lean_ctor_set_tag(v___x_64_, 0);
lean_ctor_set(v___x_64_, 0, v_default_49_);
v___x_67_ = v___x_64_;
goto v_reusejp_66_;
}
else
{
lean_object* v_reuseFailAlloc_68_; 
v_reuseFailAlloc_68_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_68_, 0, v_default_49_);
lean_ctor_set(v_reuseFailAlloc_68_, 1, v_a_62_);
v___x_67_ = v_reuseFailAlloc_68_;
goto v_reusejp_66_;
}
v_reusejp_66_:
{
return v___x_67_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_tryDecodeD(lean_object* v_00_u03b1_71_, lean_object* v_default_72_, lean_object* v_x_73_, lean_object* v_es_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = lean_apply_1(v_x_73_, v_es_74_);
if (lean_obj_tag(v___x_75_) == 0)
{
lean_object* v_a_76_; lean_object* v_a_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_84_; 
lean_dec(v_default_72_);
v_a_76_ = lean_ctor_get(v___x_75_, 0);
v_a_77_ = lean_ctor_get(v___x_75_, 1);
v_isSharedCheck_84_ = !lean_is_exclusive(v___x_75_);
if (v_isSharedCheck_84_ == 0)
{
v___x_79_ = v___x_75_;
v_isShared_80_ = v_isSharedCheck_84_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_a_77_);
lean_inc(v_a_76_);
lean_dec(v___x_75_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_84_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v___x_82_; 
if (v_isShared_80_ == 0)
{
v___x_82_ = v___x_79_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v_a_76_);
lean_ctor_set(v_reuseFailAlloc_83_, 1, v_a_77_);
v___x_82_ = v_reuseFailAlloc_83_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
return v___x_82_;
}
}
}
else
{
lean_object* v_a_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_92_; 
v_a_85_ = lean_ctor_get(v___x_75_, 1);
v_isSharedCheck_92_ = !lean_is_exclusive(v___x_75_);
if (v_isSharedCheck_92_ == 0)
{
lean_object* v_unused_93_; 
v_unused_93_ = lean_ctor_get(v___x_75_, 0);
lean_dec(v_unused_93_);
v___x_87_ = v___x_75_;
v_isShared_88_ = v_isSharedCheck_92_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_a_85_);
lean_dec(v___x_75_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_92_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
lean_object* v___x_90_; 
if (v_isShared_88_ == 0)
{
lean_ctor_set_tag(v___x_87_, 0);
lean_ctor_set(v___x_87_, 0, v_default_72_);
v___x_90_ = v___x_87_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v_default_72_);
lean_ctor_set(v_reuseFailAlloc_91_, 1, v_a_85_);
v___x_90_ = v_reuseFailAlloc_91_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
return v___x_90_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_tryDecode_x3f___redArg(lean_object* v_x_94_, lean_object* v_es_95_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = lean_apply_1(v_x_94_, v_es_95_);
if (lean_obj_tag(v___x_96_) == 0)
{
lean_object* v_a_97_; lean_object* v_a_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_106_; 
v_a_97_ = lean_ctor_get(v___x_96_, 0);
v_a_98_ = lean_ctor_get(v___x_96_, 1);
v_isSharedCheck_106_ = !lean_is_exclusive(v___x_96_);
if (v_isSharedCheck_106_ == 0)
{
v___x_100_ = v___x_96_;
v_isShared_101_ = v_isSharedCheck_106_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_a_98_);
lean_inc(v_a_97_);
lean_dec(v___x_96_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_106_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v___x_102_; lean_object* v___x_104_; 
v___x_102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_102_, 0, v_a_97_);
if (v_isShared_101_ == 0)
{
lean_ctor_set(v___x_100_, 0, v___x_102_);
v___x_104_ = v___x_100_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v___x_102_);
lean_ctor_set(v_reuseFailAlloc_105_, 1, v_a_98_);
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
lean_object* v_a_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_115_; 
v_a_107_ = lean_ctor_get(v___x_96_, 1);
v_isSharedCheck_115_ = !lean_is_exclusive(v___x_96_);
if (v_isSharedCheck_115_ == 0)
{
lean_object* v_unused_116_; 
v_unused_116_ = lean_ctor_get(v___x_96_, 0);
lean_dec(v_unused_116_);
v___x_109_ = v___x_96_;
v_isShared_110_ = v_isSharedCheck_115_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_a_107_);
lean_dec(v___x_96_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_115_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_111_; lean_object* v___x_113_; 
v___x_111_ = lean_box(0);
if (v_isShared_110_ == 0)
{
lean_ctor_set_tag(v___x_109_, 0);
lean_ctor_set(v___x_109_, 0, v___x_111_);
v___x_113_ = v___x_109_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v___x_111_);
lean_ctor_set(v_reuseFailAlloc_114_, 1, v_a_107_);
v___x_113_ = v_reuseFailAlloc_114_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
return v___x_113_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_tryDecode_x3f(lean_object* v_00_u03b1_117_, lean_object* v_x_118_, lean_object* v_es_119_){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = lean_apply_1(v_x_118_, v_es_119_);
if (lean_obj_tag(v___x_120_) == 0)
{
lean_object* v_a_121_; lean_object* v_a_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_130_; 
v_a_121_ = lean_ctor_get(v___x_120_, 0);
v_a_122_ = lean_ctor_get(v___x_120_, 1);
v_isSharedCheck_130_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_130_ == 0)
{
v___x_124_ = v___x_120_;
v_isShared_125_ = v_isSharedCheck_130_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_a_122_);
lean_inc(v_a_121_);
lean_dec(v___x_120_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_130_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_126_; lean_object* v___x_128_; 
v___x_126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_126_, 0, v_a_121_);
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 0, v___x_126_);
v___x_128_ = v___x_124_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v___x_126_);
lean_ctor_set(v_reuseFailAlloc_129_, 1, v_a_122_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
}
else
{
lean_object* v_a_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_139_; 
v_a_131_ = lean_ctor_get(v___x_120_, 1);
v_isSharedCheck_139_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_139_ == 0)
{
lean_object* v_unused_140_; 
v_unused_140_ = lean_ctor_get(v___x_120_, 0);
lean_dec(v_unused_140_);
v___x_133_ = v___x_120_;
v_isShared_134_ = v_isSharedCheck_139_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_a_131_);
lean_dec(v___x_120_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_139_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v___x_135_; lean_object* v___x_137_; 
v___x_135_ = lean_box(0);
if (v_isShared_134_ == 0)
{
lean_ctor_set_tag(v___x_133_, 0);
lean_ctor_set(v___x_133_, 0, v___x_135_);
v___x_137_ = v___x_133_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v___x_135_);
lean_ctor_set(v_reuseFailAlloc_138_, 1, v_a_131_);
v___x_137_ = v_reuseFailAlloc_138_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
return v___x_137_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_tryDecode___redArg(lean_object* v_inst_141_, lean_object* v_x_142_, lean_object* v_a_143_){
_start:
{
lean_object* v___x_144_; 
v___x_144_ = lean_apply_1(v_x_142_, v_a_143_);
if (lean_obj_tag(v___x_144_) == 0)
{
lean_object* v_a_145_; lean_object* v_a_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_153_; 
lean_dec(v_inst_141_);
v_a_145_ = lean_ctor_get(v___x_144_, 0);
v_a_146_ = lean_ctor_get(v___x_144_, 1);
v_isSharedCheck_153_ = !lean_is_exclusive(v___x_144_);
if (v_isSharedCheck_153_ == 0)
{
v___x_148_ = v___x_144_;
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_a_146_);
lean_inc(v_a_145_);
lean_dec(v___x_144_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_151_; 
if (v_isShared_149_ == 0)
{
v___x_151_ = v___x_148_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_a_145_);
lean_ctor_set(v_reuseFailAlloc_152_, 1, v_a_146_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
return v___x_151_;
}
}
}
else
{
lean_object* v_a_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_161_; 
v_a_154_ = lean_ctor_get(v___x_144_, 1);
v_isSharedCheck_161_ = !lean_is_exclusive(v___x_144_);
if (v_isSharedCheck_161_ == 0)
{
lean_object* v_unused_162_; 
v_unused_162_ = lean_ctor_get(v___x_144_, 0);
lean_dec(v_unused_162_);
v___x_156_ = v___x_144_;
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_a_154_);
lean_dec(v___x_144_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_159_; 
if (v_isShared_157_ == 0)
{
lean_ctor_set_tag(v___x_156_, 0);
lean_ctor_set(v___x_156_, 0, v_inst_141_);
v___x_159_ = v___x_156_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_inst_141_);
lean_ctor_set(v_reuseFailAlloc_160_, 1, v_a_154_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_tryDecode(lean_object* v_00_u03b1_163_, lean_object* v_inst_164_, lean_object* v_x_165_, lean_object* v_a_166_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = lean_apply_1(v_x_165_, v_a_166_);
if (lean_obj_tag(v___x_167_) == 0)
{
lean_object* v_a_168_; lean_object* v_a_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_176_; 
lean_dec(v_inst_164_);
v_a_168_ = lean_ctor_get(v___x_167_, 0);
v_a_169_ = lean_ctor_get(v___x_167_, 1);
v_isSharedCheck_176_ = !lean_is_exclusive(v___x_167_);
if (v_isSharedCheck_176_ == 0)
{
v___x_171_ = v___x_167_;
v_isShared_172_ = v_isSharedCheck_176_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_a_169_);
lean_inc(v_a_168_);
lean_dec(v___x_167_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_176_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v___x_174_; 
if (v_isShared_172_ == 0)
{
v___x_174_ = v___x_171_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v_a_168_);
lean_ctor_set(v_reuseFailAlloc_175_, 1, v_a_169_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
}
else
{
lean_object* v_a_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_184_; 
v_a_177_ = lean_ctor_get(v___x_167_, 1);
v_isSharedCheck_184_ = !lean_is_exclusive(v___x_167_);
if (v_isSharedCheck_184_ == 0)
{
lean_object* v_unused_185_; 
v_unused_185_ = lean_ctor_get(v___x_167_, 0);
lean_dec(v_unused_185_);
v___x_179_ = v___x_167_;
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_a_177_);
lean_dec(v___x_167_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___x_182_; 
if (v_isShared_180_ == 0)
{
lean_ctor_set_tag(v___x_179_, 0);
lean_ctor_set(v___x_179_, 0, v_inst_164_);
v___x_182_ = v___x_179_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_inst_164_);
lean_ctor_set(v_reuseFailAlloc_183_, 1, v_a_177_);
v___x_182_ = v_reuseFailAlloc_183_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
return v___x_182_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_optDecodeD___redArg(lean_object* v_default_186_, lean_object* v_a_x3f_187_, lean_object* v_f_188_, lean_object* v_a_189_){
_start:
{
if (lean_obj_tag(v_a_x3f_187_) == 0)
{
lean_object* v___x_190_; 
lean_dec_ref(v_f_188_);
v___x_190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_190_, 0, v_default_186_);
lean_ctor_set(v___x_190_, 1, v_a_189_);
return v___x_190_;
}
else
{
lean_object* v_val_191_; lean_object* v___x_192_; 
v_val_191_ = lean_ctor_get(v_a_x3f_187_, 0);
lean_inc(v_val_191_);
lean_dec_ref(v_a_x3f_187_);
v___x_192_ = lean_apply_2(v_f_188_, v_val_191_, v_a_189_);
if (lean_obj_tag(v___x_192_) == 0)
{
lean_object* v_a_193_; lean_object* v_a_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_201_; 
lean_dec(v_default_186_);
v_a_193_ = lean_ctor_get(v___x_192_, 0);
v_a_194_ = lean_ctor_get(v___x_192_, 1);
v_isSharedCheck_201_ = !lean_is_exclusive(v___x_192_);
if (v_isSharedCheck_201_ == 0)
{
v___x_196_ = v___x_192_;
v_isShared_197_ = v_isSharedCheck_201_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_a_194_);
lean_inc(v_a_193_);
lean_dec(v___x_192_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_201_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_199_; 
if (v_isShared_197_ == 0)
{
v___x_199_ = v___x_196_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v_a_193_);
lean_ctor_set(v_reuseFailAlloc_200_, 1, v_a_194_);
v___x_199_ = v_reuseFailAlloc_200_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
return v___x_199_;
}
}
}
else
{
lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_209_; 
v_a_202_ = lean_ctor_get(v___x_192_, 1);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_192_);
if (v_isSharedCheck_209_ == 0)
{
lean_object* v_unused_210_; 
v_unused_210_ = lean_ctor_get(v___x_192_, 0);
lean_dec(v_unused_210_);
v___x_204_ = v___x_192_;
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_dec(v___x_192_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_207_; 
if (v_isShared_205_ == 0)
{
lean_ctor_set_tag(v___x_204_, 0);
lean_ctor_set(v___x_204_, 0, v_default_186_);
v___x_207_ = v___x_204_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_default_186_);
lean_ctor_set(v_reuseFailAlloc_208_, 1, v_a_202_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_optDecodeD(lean_object* v_00_u03b2_211_, lean_object* v_00_u03b1_212_, lean_object* v_default_213_, lean_object* v_a_x3f_214_, lean_object* v_f_215_, lean_object* v_a_216_){
_start:
{
if (lean_obj_tag(v_a_x3f_214_) == 0)
{
lean_object* v___x_217_; 
lean_dec_ref(v_f_215_);
v___x_217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_217_, 0, v_default_213_);
lean_ctor_set(v___x_217_, 1, v_a_216_);
return v___x_217_;
}
else
{
lean_object* v_val_218_; lean_object* v___x_219_; 
v_val_218_ = lean_ctor_get(v_a_x3f_214_, 0);
lean_inc(v_val_218_);
lean_dec_ref(v_a_x3f_214_);
v___x_219_ = lean_apply_2(v_f_215_, v_val_218_, v_a_216_);
if (lean_obj_tag(v___x_219_) == 0)
{
lean_object* v_a_220_; lean_object* v_a_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_228_; 
lean_dec(v_default_213_);
v_a_220_ = lean_ctor_get(v___x_219_, 0);
v_a_221_ = lean_ctor_get(v___x_219_, 1);
v_isSharedCheck_228_ = !lean_is_exclusive(v___x_219_);
if (v_isSharedCheck_228_ == 0)
{
v___x_223_ = v___x_219_;
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_a_221_);
lean_inc(v_a_220_);
lean_dec(v___x_219_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_226_; 
if (v_isShared_224_ == 0)
{
v___x_226_ = v___x_223_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v_a_220_);
lean_ctor_set(v_reuseFailAlloc_227_, 1, v_a_221_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
}
else
{
lean_object* v_a_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_236_; 
v_a_229_ = lean_ctor_get(v___x_219_, 1);
v_isSharedCheck_236_ = !lean_is_exclusive(v___x_219_);
if (v_isSharedCheck_236_ == 0)
{
lean_object* v_unused_237_; 
v_unused_237_ = lean_ctor_get(v___x_219_, 0);
lean_dec(v_unused_237_);
v___x_231_ = v___x_219_;
v_isShared_232_ = v_isSharedCheck_236_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_a_229_);
lean_dec(v___x_219_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_236_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___x_234_; 
if (v_isShared_232_ == 0)
{
lean_ctor_set_tag(v___x_231_, 0);
lean_ctor_set(v___x_231_, 0, v_default_213_);
v___x_234_ = v___x_231_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v_default_213_);
lean_ctor_set(v_reuseFailAlloc_235_, 1, v_a_229_);
v___x_234_ = v_reuseFailAlloc_235_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
return v___x_234_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_optDecode___redArg(lean_object* v_inst_238_, lean_object* v_a_x3f_239_, lean_object* v_f_240_, lean_object* v_a_241_){
_start:
{
if (lean_obj_tag(v_a_x3f_239_) == 0)
{
lean_object* v___x_242_; 
lean_dec_ref(v_f_240_);
v___x_242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_242_, 0, v_inst_238_);
lean_ctor_set(v___x_242_, 1, v_a_241_);
return v___x_242_;
}
else
{
lean_object* v_val_243_; lean_object* v___x_244_; 
v_val_243_ = lean_ctor_get(v_a_x3f_239_, 0);
lean_inc(v_val_243_);
lean_dec_ref(v_a_x3f_239_);
v___x_244_ = lean_apply_2(v_f_240_, v_val_243_, v_a_241_);
if (lean_obj_tag(v___x_244_) == 0)
{
lean_object* v_a_245_; lean_object* v_a_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_253_; 
lean_dec(v_inst_238_);
v_a_245_ = lean_ctor_get(v___x_244_, 0);
v_a_246_ = lean_ctor_get(v___x_244_, 1);
v_isSharedCheck_253_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_253_ == 0)
{
v___x_248_ = v___x_244_;
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_a_246_);
lean_inc(v_a_245_);
lean_dec(v___x_244_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_251_; 
if (v_isShared_249_ == 0)
{
v___x_251_ = v___x_248_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_a_245_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v_a_246_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
return v___x_251_;
}
}
}
else
{
lean_object* v_a_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_261_; 
v_a_254_ = lean_ctor_get(v___x_244_, 1);
v_isSharedCheck_261_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_261_ == 0)
{
lean_object* v_unused_262_; 
v_unused_262_ = lean_ctor_get(v___x_244_, 0);
lean_dec(v_unused_262_);
v___x_256_ = v___x_244_;
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_a_254_);
lean_dec(v___x_244_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___x_259_; 
if (v_isShared_257_ == 0)
{
lean_ctor_set_tag(v___x_256_, 0);
lean_ctor_set(v___x_256_, 0, v_inst_238_);
v___x_259_ = v___x_256_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_inst_238_);
lean_ctor_set(v_reuseFailAlloc_260_, 1, v_a_254_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_optDecode(lean_object* v_00_u03b2_263_, lean_object* v_00_u03b1_264_, lean_object* v_inst_265_, lean_object* v_a_x3f_266_, lean_object* v_f_267_, lean_object* v_a_268_){
_start:
{
if (lean_obj_tag(v_a_x3f_266_) == 0)
{
lean_object* v___x_269_; 
lean_dec_ref(v_f_267_);
v___x_269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_269_, 0, v_inst_265_);
lean_ctor_set(v___x_269_, 1, v_a_268_);
return v___x_269_;
}
else
{
lean_object* v_val_270_; lean_object* v___x_271_; 
v_val_270_ = lean_ctor_get(v_a_x3f_266_, 0);
lean_inc(v_val_270_);
lean_dec_ref(v_a_x3f_266_);
v___x_271_ = lean_apply_2(v_f_267_, v_val_270_, v_a_268_);
if (lean_obj_tag(v___x_271_) == 0)
{
lean_object* v_a_272_; lean_object* v_a_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_280_; 
lean_dec(v_inst_265_);
v_a_272_ = lean_ctor_get(v___x_271_, 0);
v_a_273_ = lean_ctor_get(v___x_271_, 1);
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_280_ == 0)
{
v___x_275_ = v___x_271_;
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_a_273_);
lean_inc(v_a_272_);
lean_dec(v___x_271_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_278_; 
if (v_isShared_276_ == 0)
{
v___x_278_ = v___x_275_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_a_272_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v_a_273_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
}
else
{
lean_object* v_a_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_288_; 
v_a_281_ = lean_ctor_get(v___x_271_, 1);
v_isSharedCheck_288_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_288_ == 0)
{
lean_object* v_unused_289_; 
v_unused_289_ = lean_ctor_get(v___x_271_, 0);
lean_dec(v_unused_289_);
v___x_283_ = v___x_271_;
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_a_281_);
lean_dec(v___x_271_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_286_; 
if (v_isShared_284_ == 0)
{
lean_ctor_set_tag(v___x_283_, 0);
lean_ctor_set(v___x_283_, 0, v_inst_265_);
v___x_286_ = v___x_283_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v_inst_265_);
lean_ctor_set(v_reuseFailAlloc_287_, 1, v_a_281_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_optDecode_x3f___redArg(lean_object* v_a_x3f_290_, lean_object* v_f_291_, lean_object* v_a_292_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = lean_box(0);
if (lean_obj_tag(v_a_x3f_290_) == 0)
{
lean_object* v___x_294_; 
lean_dec_ref(v_f_291_);
v___x_294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
lean_ctor_set(v___x_294_, 1, v_a_292_);
return v___x_294_;
}
else
{
lean_object* v_val_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_321_; 
v_val_295_ = lean_ctor_get(v_a_x3f_290_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v_a_x3f_290_);
if (v_isSharedCheck_321_ == 0)
{
v___x_297_ = v_a_x3f_290_;
v_isShared_298_ = v_isSharedCheck_321_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_val_295_);
lean_dec(v_a_x3f_290_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_321_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_299_; 
v___x_299_ = lean_apply_2(v_f_291_, v_val_295_, v_a_292_);
if (lean_obj_tag(v___x_299_) == 0)
{
lean_object* v_a_300_; lean_object* v_a_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_311_; 
v_a_300_ = lean_ctor_get(v___x_299_, 0);
v_a_301_ = lean_ctor_get(v___x_299_, 1);
v_isSharedCheck_311_ = !lean_is_exclusive(v___x_299_);
if (v_isSharedCheck_311_ == 0)
{
v___x_303_ = v___x_299_;
v_isShared_304_ = v_isSharedCheck_311_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_a_301_);
lean_inc(v_a_300_);
lean_dec(v___x_299_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_311_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_306_; 
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 0, v_a_300_);
v___x_306_ = v___x_297_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v_a_300_);
v___x_306_ = v_reuseFailAlloc_310_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
lean_object* v___x_308_; 
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 0, v___x_306_);
v___x_308_ = v___x_303_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v___x_306_);
lean_ctor_set(v_reuseFailAlloc_309_, 1, v_a_301_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
}
}
else
{
lean_object* v_a_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_319_; 
lean_del_object(v___x_297_);
v_a_312_ = lean_ctor_get(v___x_299_, 1);
v_isSharedCheck_319_ = !lean_is_exclusive(v___x_299_);
if (v_isSharedCheck_319_ == 0)
{
lean_object* v_unused_320_; 
v_unused_320_ = lean_ctor_get(v___x_299_, 0);
lean_dec(v_unused_320_);
v___x_314_ = v___x_299_;
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_a_312_);
lean_dec(v___x_299_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_317_; 
if (v_isShared_315_ == 0)
{
lean_ctor_set_tag(v___x_314_, 0);
lean_ctor_set(v___x_314_, 0, v___x_293_);
v___x_317_ = v___x_314_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v___x_293_);
lean_ctor_set(v_reuseFailAlloc_318_, 1, v_a_312_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_optDecode_x3f(lean_object* v_00_u03b1_322_, lean_object* v_00_u03b2_323_, lean_object* v_a_x3f_324_, lean_object* v_f_325_, lean_object* v_a_326_){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = lean_box(0);
if (lean_obj_tag(v_a_x3f_324_) == 0)
{
lean_object* v___x_328_; 
lean_dec_ref(v_f_325_);
v___x_328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_328_, 0, v___x_327_);
lean_ctor_set(v___x_328_, 1, v_a_326_);
return v___x_328_;
}
else
{
lean_object* v_val_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_355_; 
v_val_329_ = lean_ctor_get(v_a_x3f_324_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v_a_x3f_324_);
if (v_isSharedCheck_355_ == 0)
{
v___x_331_ = v_a_x3f_324_;
v_isShared_332_ = v_isSharedCheck_355_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_val_329_);
lean_dec(v_a_x3f_324_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_355_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_333_; 
v___x_333_ = lean_apply_2(v_f_325_, v_val_329_, v_a_326_);
if (lean_obj_tag(v___x_333_) == 0)
{
lean_object* v_a_334_; lean_object* v_a_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_345_; 
v_a_334_ = lean_ctor_get(v___x_333_, 0);
v_a_335_ = lean_ctor_get(v___x_333_, 1);
v_isSharedCheck_345_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_345_ == 0)
{
v___x_337_ = v___x_333_;
v_isShared_338_ = v_isSharedCheck_345_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_a_335_);
lean_inc(v_a_334_);
lean_dec(v___x_333_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_345_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_340_; 
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 0, v_a_334_);
v___x_340_ = v___x_331_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v_a_334_);
v___x_340_ = v_reuseFailAlloc_344_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
lean_object* v___x_342_; 
if (v_isShared_338_ == 0)
{
lean_ctor_set(v___x_337_, 0, v___x_340_);
v___x_342_ = v___x_337_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v___x_340_);
lean_ctor_set(v_reuseFailAlloc_343_, 1, v_a_335_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
}
else
{
lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_353_; 
lean_del_object(v___x_331_);
v_a_346_ = lean_ctor_get(v___x_333_, 1);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_353_ == 0)
{
lean_object* v_unused_354_; 
v_unused_354_ = lean_ctor_get(v___x_333_, 0);
lean_dec(v_unused_354_);
v___x_348_ = v___x_333_;
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_a_346_);
lean_dec(v___x_333_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_351_; 
if (v_isShared_349_ == 0)
{
lean_ctor_set_tag(v___x_348_, 0);
lean_ctor_set(v___x_348_, 0, v___x_327_);
v___x_351_ = v___x_348_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v___x_327_);
lean_ctor_set(v_reuseFailAlloc_352_, 1, v_a_346_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_mergeErrors___redArg(lean_object* v_x_u2081_356_, lean_object* v_x_u2082_357_, lean_object* v_f_358_, lean_object* v_es_359_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = lean_apply_1(v_x_u2081_356_, v_es_359_);
if (lean_obj_tag(v___x_360_) == 0)
{
lean_object* v_a_361_; lean_object* v_a_362_; lean_object* v___x_363_; 
v_a_361_ = lean_ctor_get(v___x_360_, 0);
lean_inc(v_a_361_);
v_a_362_ = lean_ctor_get(v___x_360_, 1);
lean_inc(v_a_362_);
lean_dec_ref(v___x_360_);
v___x_363_ = lean_apply_1(v_x_u2082_357_, v_a_362_);
if (lean_obj_tag(v___x_363_) == 0)
{
lean_object* v_a_364_; lean_object* v_a_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_373_; 
v_a_364_ = lean_ctor_get(v___x_363_, 0);
v_a_365_ = lean_ctor_get(v___x_363_, 1);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_373_ == 0)
{
v___x_367_ = v___x_363_;
v_isShared_368_ = v_isSharedCheck_373_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_a_365_);
lean_inc(v_a_364_);
lean_dec(v___x_363_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_373_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_369_; lean_object* v___x_371_; 
v___x_369_ = lean_apply_2(v_f_358_, v_a_361_, v_a_364_);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 0, v___x_369_);
v___x_371_ = v___x_367_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_369_);
lean_ctor_set(v_reuseFailAlloc_372_, 1, v_a_365_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
else
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_382_; 
lean_dec(v_a_361_);
lean_dec(v_f_358_);
v_a_374_ = lean_ctor_get(v___x_363_, 1);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_382_ == 0)
{
lean_object* v_unused_383_; 
v_unused_383_ = lean_ctor_get(v___x_363_, 0);
lean_dec(v_unused_383_);
v___x_376_ = v___x_363_;
v_isShared_377_ = v_isSharedCheck_382_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_363_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_382_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_378_; lean_object* v___x_380_; 
v___x_378_ = lean_box(0);
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 0, v___x_378_);
v___x_380_ = v___x_376_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v___x_378_);
lean_ctor_set(v_reuseFailAlloc_381_, 1, v_a_374_);
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
else
{
lean_object* v_a_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_392_; 
lean_dec(v_f_358_);
lean_dec_ref(v_x_u2082_357_);
v_a_384_ = lean_ctor_get(v___x_360_, 1);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_392_ == 0)
{
lean_object* v_unused_393_; 
v_unused_393_ = lean_ctor_get(v___x_360_, 0);
lean_dec(v_unused_393_);
v___x_386_ = v___x_360_;
v_isShared_387_ = v_isSharedCheck_392_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_a_384_);
lean_dec(v___x_360_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_392_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_388_; lean_object* v___x_390_; 
v___x_388_ = lean_box(0);
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 0, v___x_388_);
v___x_390_ = v___x_386_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v___x_388_);
lean_ctor_set(v_reuseFailAlloc_391_, 1, v_a_384_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_mergeErrors(lean_object* v_00_u03b1_394_, lean_object* v_00_u03b2_395_, lean_object* v_00_u03b3_396_, lean_object* v_x_u2081_397_, lean_object* v_x_u2082_398_, lean_object* v_f_399_, lean_object* v_es_400_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = l_Lake_Toml_mergeErrors___redArg(v_x_u2081_397_, v_x_u2082_398_, v_f_399_, v_es_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_throwDecodeErrorAt___redArg(lean_object* v_ref_402_, lean_object* v_msg_403_, lean_object* v_es_404_){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_405_ = lean_box(0);
v___x_406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_406_, 0, v_ref_402_);
lean_ctor_set(v___x_406_, 1, v_msg_403_);
v___x_407_ = lean_array_push(v_es_404_, v___x_406_);
v___x_408_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_408_, 0, v___x_405_);
lean_ctor_set(v___x_408_, 1, v___x_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_throwDecodeErrorAt(lean_object* v_00_u03b1_409_, lean_object* v_ref_410_, lean_object* v_msg_411_, lean_object* v_es_412_){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_413_ = lean_box(0);
v___x_414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_414_, 0, v_ref_410_);
lean_ctor_set(v___x_414_, 1, v_msg_411_);
v___x_415_ = lean_array_push(v_es_412_, v___x_414_);
v___x_416_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_416_, 0, v___x_413_);
lean_ctor_set(v___x_416_, 1, v___x_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___redArg___lam__0(lean_object* v_dec_418_, lean_object* v_x1_419_, lean_object* v_x2_420_, lean_object* v___y_421_){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_422_ = lean_apply_1(v_dec_418_, v_x2_420_);
v___x_423_ = ((lean_object*)(l_Lake_Toml_decodeArray___redArg___lam__0___closed__0));
v___x_424_ = l_Lake_Toml_mergeErrors___redArg(v_x1_419_, v___x_422_, v___x_423_, v___y_421_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___redArg(lean_object* v_dec_444_, lean_object* v_vs_445_, lean_object* v_a_446_){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; uint8_t v___x_451_; 
v___x_447_ = lean_array_get_size(v_vs_445_);
v___x_448_ = lean_mk_empty_array_with_capacity(v___x_447_);
v___x_449_ = lean_unsigned_to_nat(0u);
v___x_450_ = ((lean_object*)(l_Lake_Toml_decodeArray___redArg___closed__9));
v___x_451_ = lean_nat_dec_lt(v___x_449_, v___x_447_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; 
lean_dec_ref(v_vs_445_);
lean_dec_ref(v_dec_444_);
v___x_452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_452_, 0, v___x_448_);
lean_ctor_set(v___x_452_, 1, v_a_446_);
return v___x_452_;
}
else
{
lean_object* v___f_453_; lean_object* v___x_454_; uint8_t v___x_455_; 
v___f_453_ = lean_alloc_closure((void*)(l_Lake_Toml_decodeArray___redArg___lam__0), 4, 1);
lean_closure_set(v___f_453_, 0, v_dec_444_);
lean_inc_ref(v___x_448_);
v___x_454_ = lean_alloc_closure((void*)(l_EStateM_pure), 5, 4);
lean_closure_set(v___x_454_, 0, lean_box(0));
lean_closure_set(v___x_454_, 1, lean_box(0));
lean_closure_set(v___x_454_, 2, lean_box(0));
lean_closure_set(v___x_454_, 3, v___x_448_);
v___x_455_ = lean_nat_dec_le(v___x_447_, v___x_447_);
if (v___x_455_ == 0)
{
if (v___x_451_ == 0)
{
lean_object* v___x_456_; 
lean_dec_ref(v___x_454_);
lean_dec_ref(v___f_453_);
lean_dec_ref(v_vs_445_);
v___x_456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_456_, 0, v___x_448_);
lean_ctor_set(v___x_456_, 1, v_a_446_);
return v___x_456_;
}
else
{
size_t v___x_457_; size_t v___x_458_; lean_object* v___x_133__overap_459_; lean_object* v___x_460_; 
lean_dec_ref(v___x_448_);
v___x_457_ = ((size_t)0ULL);
v___x_458_ = lean_usize_of_nat(v___x_447_);
v___x_133__overap_459_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_450_, v___f_453_, v_vs_445_, v___x_457_, v___x_458_, v___x_454_);
v___x_460_ = lean_apply_1(v___x_133__overap_459_, v_a_446_);
return v___x_460_;
}
}
else
{
size_t v___x_461_; size_t v___x_462_; lean_object* v___x_138__overap_463_; lean_object* v___x_464_; 
lean_dec_ref(v___x_448_);
v___x_461_ = ((size_t)0ULL);
v___x_462_ = lean_usize_of_nat(v___x_447_);
v___x_138__overap_463_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_450_, v___f_453_, v_vs_445_, v___x_461_, v___x_462_, v___x_454_);
v___x_464_ = lean_apply_1(v___x_138__overap_463_, v_a_446_);
return v___x_464_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray(lean_object* v_00_u03b1_465_, lean_object* v_dec_466_, lean_object* v_vs_467_, lean_object* v_a_468_){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = l_Lake_Toml_decodeArray___redArg(v_dec_466_, v_vs_467_, v_a_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_decodeString(lean_object* v_v_473_, lean_object* v_a_474_){
_start:
{
lean_object* v___y_476_; 
if (lean_obj_tag(v_v_473_) == 0)
{
lean_object* v_s_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_489_; 
v_s_482_ = lean_ctor_get(v_v_473_, 1);
v_isSharedCheck_489_ = !lean_is_exclusive(v_v_473_);
if (v_isSharedCheck_489_ == 0)
{
lean_object* v_unused_490_; 
v_unused_490_ = lean_ctor_get(v_v_473_, 0);
lean_dec(v_unused_490_);
v___x_484_ = v_v_473_;
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_s_482_);
lean_dec(v_v_473_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_487_; 
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 1, v_a_474_);
lean_ctor_set(v___x_484_, 0, v_s_482_);
v___x_487_ = v___x_484_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_s_482_);
lean_ctor_set(v_reuseFailAlloc_488_, 1, v_a_474_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
}
else
{
lean_object* v_ref_491_; 
v_ref_491_ = lean_ctor_get(v_v_473_, 0);
lean_inc(v_ref_491_);
lean_dec_ref(v_v_473_);
v___y_476_ = v_ref_491_;
goto v___jp_475_;
}
v___jp_475_:
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_477_ = ((lean_object*)(l_Lake_Toml_Value_decodeString___closed__0));
v___x_478_ = lean_box(0);
v___x_479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_479_, 0, v___y_476_);
lean_ctor_set(v___x_479_, 1, v___x_477_);
v___x_480_ = lean_array_push(v_a_474_, v___x_479_);
v___x_481_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_481_, 0, v___x_478_);
lean_ctor_set(v___x_481_, 1, v___x_480_);
return v___x_481_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_instDecodeTomlFilePath___lam__0(lean_object* v_x_494_, lean_object* v___y_495_){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = l_Lake_Toml_Value_decodeString(v_x_494_, v___y_495_);
if (lean_obj_tag(v___x_496_) == 0)
{
lean_object* v_a_497_; lean_object* v_a_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_505_; 
v_a_497_ = lean_ctor_get(v___x_496_, 0);
v_a_498_ = lean_ctor_get(v___x_496_, 1);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_505_ == 0)
{
v___x_500_ = v___x_496_;
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_a_498_);
lean_inc(v_a_497_);
lean_dec(v___x_496_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_503_; 
if (v_isShared_501_ == 0)
{
v___x_503_ = v___x_500_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_a_497_);
lean_ctor_set(v_reuseFailAlloc_504_, 1, v_a_498_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
else
{
lean_object* v_a_506_; lean_object* v_a_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_514_; 
v_a_506_ = lean_ctor_get(v___x_496_, 0);
v_a_507_ = lean_ctor_get(v___x_496_, 1);
v_isSharedCheck_514_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_514_ == 0)
{
v___x_509_ = v___x_496_;
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_a_507_);
lean_inc(v_a_506_);
lean_dec(v___x_496_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_512_; 
if (v_isShared_510_ == 0)
{
v___x_512_ = v___x_509_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_a_506_);
lean_ctor_set(v_reuseFailAlloc_513_, 1, v_a_507_);
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
LEAN_EXPORT lean_object* l_Lake_Toml_Value_decodeName(lean_object* v_v_518_, lean_object* v_a_519_){
_start:
{
lean_object* v___x_520_; 
lean_inc_ref(v_v_518_);
v___x_520_ = l_Lake_Toml_Value_decodeString(v_v_518_, v_a_519_);
if (lean_obj_tag(v___x_520_) == 0)
{
lean_object* v_a_521_; lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_538_; 
v_a_521_ = lean_ctor_get(v___x_520_, 0);
v_a_522_ = lean_ctor_get(v___x_520_, 1);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_538_ == 0)
{
v___x_524_ = v___x_520_;
v_isShared_525_ = v_isSharedCheck_538_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_inc(v_a_521_);
lean_dec(v___x_520_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_538_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___y_527_; lean_object* v___x_535_; 
v___x_535_ = l_String_toName(v_a_521_);
if (lean_obj_tag(v___x_535_) == 0)
{
lean_object* v_ref_536_; 
v_ref_536_ = lean_ctor_get(v_v_518_, 0);
lean_inc(v_ref_536_);
lean_dec_ref(v_v_518_);
v___y_527_ = v_ref_536_;
goto v___jp_526_;
}
else
{
lean_object* v___x_537_; 
lean_del_object(v___x_524_);
lean_dec_ref(v_v_518_);
v___x_537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_535_);
lean_ctor_set(v___x_537_, 1, v_a_522_);
return v___x_537_;
}
v___jp_526_:
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_533_; 
v___x_528_ = ((lean_object*)(l_Lake_Toml_Value_decodeName___closed__0));
v___x_529_ = lean_box(0);
v___x_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_530_, 0, v___y_527_);
lean_ctor_set(v___x_530_, 1, v___x_528_);
v___x_531_ = lean_array_push(v_a_522_, v___x_530_);
if (v_isShared_525_ == 0)
{
lean_ctor_set_tag(v___x_524_, 1);
lean_ctor_set(v___x_524_, 1, v___x_531_);
lean_ctor_set(v___x_524_, 0, v___x_529_);
v___x_533_ = v___x_524_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v___x_529_);
lean_ctor_set(v_reuseFailAlloc_534_, 1, v___x_531_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
return v___x_533_;
}
}
}
}
else
{
lean_object* v_a_539_; lean_object* v_a_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_547_; 
lean_dec_ref(v_v_518_);
v_a_539_ = lean_ctor_get(v___x_520_, 0);
v_a_540_ = lean_ctor_get(v___x_520_, 1);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_547_ == 0)
{
v___x_542_ = v___x_520_;
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_inc(v_a_539_);
lean_dec(v___x_520_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_545_; 
if (v_isShared_543_ == 0)
{
v___x_545_ = v___x_542_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_a_539_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v_a_540_);
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
LEAN_EXPORT lean_object* l_Lake_Toml_Value_decodeInt(lean_object* v_v_551_, lean_object* v_a_552_){
_start:
{
lean_object* v___y_554_; 
if (lean_obj_tag(v_v_551_) == 1)
{
lean_object* v_n_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_567_; 
v_n_560_ = lean_ctor_get(v_v_551_, 1);
v_isSharedCheck_567_ = !lean_is_exclusive(v_v_551_);
if (v_isSharedCheck_567_ == 0)
{
lean_object* v_unused_568_; 
v_unused_568_ = lean_ctor_get(v_v_551_, 0);
lean_dec(v_unused_568_);
v___x_562_ = v_v_551_;
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_n_560_);
lean_dec(v_v_551_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_565_; 
if (v_isShared_563_ == 0)
{
lean_ctor_set_tag(v___x_562_, 0);
lean_ctor_set(v___x_562_, 1, v_a_552_);
lean_ctor_set(v___x_562_, 0, v_n_560_);
v___x_565_ = v___x_562_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_n_560_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v_a_552_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
else
{
lean_object* v_ref_569_; 
v_ref_569_ = lean_ctor_get(v_v_551_, 0);
lean_inc(v_ref_569_);
lean_dec_ref(v_v_551_);
v___y_554_ = v_ref_569_;
goto v___jp_553_;
}
v___jp_553_:
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_555_ = ((lean_object*)(l_Lake_Toml_Value_decodeInt___closed__0));
v___x_556_ = lean_box(0);
v___x_557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_557_, 0, v___y_554_);
lean_ctor_set(v___x_557_, 1, v___x_555_);
v___x_558_ = lean_array_push(v_a_552_, v___x_557_);
v___x_559_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_559_, 0, v___x_556_);
lean_ctor_set(v___x_559_, 1, v___x_558_);
return v___x_559_;
}
}
}
static lean_object* _init_l_Lake_Toml_Value_decodeNat___closed__1(void){
_start:
{
lean_object* v_natZero_573_; lean_object* v_intZero_574_; 
v_natZero_573_ = lean_unsigned_to_nat(0u);
v_intZero_574_ = lean_nat_to_int(v_natZero_573_);
return v_intZero_574_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_decodeNat(lean_object* v_x_575_, lean_object* v_a_576_){
_start:
{
lean_object* v___y_578_; lean_object* v___y_579_; 
if (lean_obj_tag(v_x_575_) == 1)
{
lean_object* v_ref_585_; lean_object* v_n_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_596_; 
v_ref_585_ = lean_ctor_get(v_x_575_, 0);
v_n_586_ = lean_ctor_get(v_x_575_, 1);
v_isSharedCheck_596_ = !lean_is_exclusive(v_x_575_);
if (v_isSharedCheck_596_ == 0)
{
v___x_588_ = v_x_575_;
v_isShared_589_ = v_isSharedCheck_596_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_n_586_);
lean_inc(v_ref_585_);
lean_dec(v_x_575_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_596_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v_intZero_590_; uint8_t v_isNeg_591_; 
v_intZero_590_ = lean_obj_once(&l_Lake_Toml_Value_decodeNat___closed__1, &l_Lake_Toml_Value_decodeNat___closed__1_once, _init_l_Lake_Toml_Value_decodeNat___closed__1);
v_isNeg_591_ = lean_int_dec_lt(v_n_586_, v_intZero_590_);
if (v_isNeg_591_ == 0)
{
lean_object* v_a_592_; lean_object* v___x_594_; 
lean_dec(v_ref_585_);
v_a_592_ = lean_nat_abs(v_n_586_);
lean_dec(v_n_586_);
if (v_isShared_589_ == 0)
{
lean_ctor_set_tag(v___x_588_, 0);
lean_ctor_set(v___x_588_, 1, v_a_576_);
lean_ctor_set(v___x_588_, 0, v_a_592_);
v___x_594_ = v___x_588_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_a_592_);
lean_ctor_set(v_reuseFailAlloc_595_, 1, v_a_576_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
else
{
lean_del_object(v___x_588_);
lean_dec(v_n_586_);
v___y_578_ = v_a_576_;
v___y_579_ = v_ref_585_;
goto v___jp_577_;
}
}
}
else
{
lean_object* v_ref_597_; 
v_ref_597_ = lean_ctor_get(v_x_575_, 0);
lean_inc(v_ref_597_);
lean_dec_ref(v_x_575_);
v___y_578_ = v_a_576_;
v___y_579_ = v_ref_597_;
goto v___jp_577_;
}
v___jp_577_:
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_580_ = ((lean_object*)(l_Lake_Toml_Value_decodeNat___closed__0));
v___x_581_ = lean_box(0);
v___x_582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_582_, 0, v___y_579_);
lean_ctor_set(v___x_582_, 1, v___x_580_);
v___x_583_ = lean_array_push(v___y_578_, v___x_582_);
v___x_584_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_584_, 0, v___x_581_);
lean_ctor_set(v___x_584_, 1, v___x_583_);
return v___x_584_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_decodeFloat(lean_object* v_v_601_, lean_object* v_a_602_){
_start:
{
lean_object* v___y_604_; 
if (lean_obj_tag(v_v_601_) == 2)
{
double v_n_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v_n_610_ = lean_ctor_get_float(v_v_601_, sizeof(void*)*1);
lean_dec_ref(v_v_601_);
v___x_611_ = lean_box_float(v_n_610_);
v___x_612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_612_, 0, v___x_611_);
lean_ctor_set(v___x_612_, 1, v_a_602_);
return v___x_612_;
}
else
{
lean_object* v_ref_613_; 
v_ref_613_ = lean_ctor_get(v_v_601_, 0);
lean_inc(v_ref_613_);
lean_dec_ref(v_v_601_);
v___y_604_ = v_ref_613_;
goto v___jp_603_;
}
v___jp_603_:
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_605_ = ((lean_object*)(l_Lake_Toml_Value_decodeFloat___closed__0));
v___x_606_ = lean_box(0);
v___x_607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_607_, 0, v___y_604_);
lean_ctor_set(v___x_607_, 1, v___x_605_);
v___x_608_ = lean_array_push(v_a_602_, v___x_607_);
v___x_609_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_609_, 0, v___x_606_);
lean_ctor_set(v___x_609_, 1, v___x_608_);
return v___x_609_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_decodeBool(lean_object* v_v_617_, lean_object* v_a_618_){
_start:
{
lean_object* v___y_620_; 
if (lean_obj_tag(v_v_617_) == 3)
{
uint8_t v_b_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v_b_626_ = lean_ctor_get_uint8(v_v_617_, sizeof(void*)*1);
lean_dec_ref(v_v_617_);
v___x_627_ = lean_box(v_b_626_);
v___x_628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
lean_ctor_set(v___x_628_, 1, v_a_618_);
return v___x_628_;
}
else
{
lean_object* v_ref_629_; 
v_ref_629_ = lean_ctor_get(v_v_617_, 0);
lean_inc(v_ref_629_);
lean_dec_ref(v_v_617_);
v___y_620_ = v_ref_629_;
goto v___jp_619_;
}
v___jp_619_:
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_621_ = ((lean_object*)(l_Lake_Toml_Value_decodeBool___closed__0));
v___x_622_ = lean_box(0);
v___x_623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_623_, 0, v___y_620_);
lean_ctor_set(v___x_623_, 1, v___x_621_);
v___x_624_ = lean_array_push(v_a_618_, v___x_623_);
v___x_625_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_625_, 0, v___x_622_);
lean_ctor_set(v___x_625_, 1, v___x_624_);
return v___x_625_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_decodeDateTime(lean_object* v_v_633_, lean_object* v_a_634_){
_start:
{
lean_object* v___y_636_; 
if (lean_obj_tag(v_v_633_) == 4)
{
lean_object* v_dt_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_649_; 
v_dt_642_ = lean_ctor_get(v_v_633_, 1);
v_isSharedCheck_649_ = !lean_is_exclusive(v_v_633_);
if (v_isSharedCheck_649_ == 0)
{
lean_object* v_unused_650_; 
v_unused_650_ = lean_ctor_get(v_v_633_, 0);
lean_dec(v_unused_650_);
v___x_644_ = v_v_633_;
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_dt_642_);
lean_dec(v_v_633_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_647_; 
if (v_isShared_645_ == 0)
{
lean_ctor_set_tag(v___x_644_, 0);
lean_ctor_set(v___x_644_, 1, v_a_634_);
lean_ctor_set(v___x_644_, 0, v_dt_642_);
v___x_647_ = v___x_644_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_dt_642_);
lean_ctor_set(v_reuseFailAlloc_648_, 1, v_a_634_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
else
{
lean_object* v_ref_651_; 
v_ref_651_ = lean_ctor_get(v_v_633_, 0);
lean_inc(v_ref_651_);
lean_dec_ref(v_v_633_);
v___y_636_ = v_ref_651_;
goto v___jp_635_;
}
v___jp_635_:
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_637_ = ((lean_object*)(l_Lake_Toml_Value_decodeDateTime___closed__0));
v___x_638_ = lean_box(0);
v___x_639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_639_, 0, v___y_636_);
lean_ctor_set(v___x_639_, 1, v___x_637_);
v___x_640_ = lean_array_push(v_a_634_, v___x_639_);
v___x_641_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_641_, 0, v___x_638_);
lean_ctor_set(v___x_641_, 1, v___x_640_);
return v___x_641_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_decodeValueArray(lean_object* v_v_655_, lean_object* v_a_656_){
_start:
{
lean_object* v___y_658_; 
if (lean_obj_tag(v_v_655_) == 5)
{
lean_object* v_xs_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_671_; 
v_xs_664_ = lean_ctor_get(v_v_655_, 1);
v_isSharedCheck_671_ = !lean_is_exclusive(v_v_655_);
if (v_isSharedCheck_671_ == 0)
{
lean_object* v_unused_672_; 
v_unused_672_ = lean_ctor_get(v_v_655_, 0);
lean_dec(v_unused_672_);
v___x_666_ = v_v_655_;
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_xs_664_);
lean_dec(v_v_655_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_669_; 
if (v_isShared_667_ == 0)
{
lean_ctor_set_tag(v___x_666_, 0);
lean_ctor_set(v___x_666_, 1, v_a_656_);
lean_ctor_set(v___x_666_, 0, v_xs_664_);
v___x_669_ = v___x_666_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_xs_664_);
lean_ctor_set(v_reuseFailAlloc_670_, 1, v_a_656_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
else
{
lean_object* v_ref_673_; 
v_ref_673_ = lean_ctor_get(v_v_655_, 0);
lean_inc(v_ref_673_);
lean_dec_ref(v_v_655_);
v___y_658_ = v_ref_673_;
goto v___jp_657_;
}
v___jp_657_:
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_659_ = ((lean_object*)(l_Lake_Toml_Value_decodeValueArray___closed__0));
v___x_660_ = lean_box(0);
v___x_661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_661_, 0, v___y_658_);
lean_ctor_set(v___x_661_, 1, v___x_659_);
v___x_662_ = lean_array_push(v_a_656_, v___x_661_);
v___x_663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_663_, 0, v___x_660_);
lean_ctor_set(v___x_663_, 1, v___x_662_);
return v___x_663_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_decodeArray___redArg(lean_object* v_dec_674_, lean_object* v_v_675_, lean_object* v_a_676_){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = l_Lake_Toml_Value_decodeValueArray(v_v_675_, v_a_676_);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_object* v_a_678_; lean_object* v_a_679_; lean_object* v___x_680_; 
v_a_678_ = lean_ctor_get(v___x_677_, 0);
lean_inc(v_a_678_);
v_a_679_ = lean_ctor_get(v___x_677_, 1);
lean_inc(v_a_679_);
lean_dec_ref(v___x_677_);
v___x_680_ = l_Lake_Toml_decodeArray___redArg(v_dec_674_, v_a_678_, v_a_679_);
return v___x_680_;
}
else
{
lean_object* v_a_681_; lean_object* v_a_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_689_; 
lean_dec_ref(v_dec_674_);
v_a_681_ = lean_ctor_get(v___x_677_, 0);
v_a_682_ = lean_ctor_get(v___x_677_, 1);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_689_ == 0)
{
v___x_684_ = v___x_677_;
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_a_682_);
lean_inc(v_a_681_);
lean_dec(v___x_677_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_687_; 
if (v_isShared_685_ == 0)
{
v___x_687_ = v___x_684_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_a_681_);
lean_ctor_set(v_reuseFailAlloc_688_, 1, v_a_682_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_decodeArray(lean_object* v_00_u03b1_690_, lean_object* v_dec_691_, lean_object* v_v_692_, lean_object* v_a_693_){
_start:
{
lean_object* v___x_694_; 
v___x_694_ = l_Lake_Toml_Value_decodeValueArray(v_v_692_, v_a_693_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v_a_695_; lean_object* v_a_696_; lean_object* v___x_697_; 
v_a_695_ = lean_ctor_get(v___x_694_, 0);
lean_inc(v_a_695_);
v_a_696_ = lean_ctor_get(v___x_694_, 1);
lean_inc(v_a_696_);
lean_dec_ref(v___x_694_);
v___x_697_ = l_Lake_Toml_decodeArray___redArg(v_dec_691_, v_a_695_, v_a_696_);
return v___x_697_;
}
else
{
lean_object* v_a_698_; lean_object* v_a_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_706_; 
lean_dec_ref(v_dec_691_);
v_a_698_ = lean_ctor_get(v___x_694_, 0);
v_a_699_ = lean_ctor_get(v___x_694_, 1);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_706_ == 0)
{
v___x_701_ = v___x_694_;
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_a_699_);
lean_inc(v_a_698_);
lean_dec(v___x_694_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_704_; 
if (v_isShared_702_ == 0)
{
v___x_704_ = v___x_701_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_a_698_);
lean_ctor_set(v_reuseFailAlloc_705_, 1, v_a_699_);
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
LEAN_EXPORT lean_object* l_Lake_Toml_Value_instDecodeTomlArray___redArg(lean_object* v_inst_707_){
_start:
{
lean_object* v___x_708_; 
v___x_708_ = lean_alloc_closure((void*)(l_Lake_Toml_Value_decodeArray), 4, 2);
lean_closure_set(v___x_708_, 0, lean_box(0));
lean_closure_set(v___x_708_, 1, v_inst_707_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_instDecodeTomlArray(lean_object* v_00_u03b1_709_, lean_object* v_inst_710_){
_start:
{
lean_object* v___x_711_; 
v___x_711_ = lean_alloc_closure((void*)(l_Lake_Toml_Value_decodeArray), 4, 2);
lean_closure_set(v___x_711_, 0, lean_box(0));
lean_closure_set(v___x_711_, 1, v_inst_710_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_decodeArrayOrSingleton___redArg(lean_object* v_dec_712_, lean_object* v_v_713_, lean_object* v_a_714_){
_start:
{
if (lean_obj_tag(v_v_713_) == 5)
{
lean_object* v_xs_715_; lean_object* v___x_716_; 
v_xs_715_ = lean_ctor_get(v_v_713_, 1);
lean_inc_ref(v_xs_715_);
lean_dec_ref(v_v_713_);
v___x_716_ = l_Lake_Toml_decodeArray___redArg(v_dec_712_, v_xs_715_, v_a_714_);
return v___x_716_;
}
else
{
lean_object* v___x_717_; 
v___x_717_ = lean_apply_2(v_dec_712_, v_v_713_, v_a_714_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v_a_718_; lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_729_; 
v_a_718_ = lean_ctor_get(v___x_717_, 0);
v_a_719_ = lean_ctor_get(v___x_717_, 1);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_729_ == 0)
{
v___x_721_ = v___x_717_;
v_isShared_722_ = v_isSharedCheck_729_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_inc(v_a_718_);
lean_dec(v___x_717_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_729_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_727_; 
v___x_723_ = lean_unsigned_to_nat(1u);
v___x_724_ = lean_mk_empty_array_with_capacity(v___x_723_);
v___x_725_ = lean_array_push(v___x_724_, v_a_718_);
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 0, v___x_725_);
v___x_727_ = v___x_721_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v___x_725_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v_a_719_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
else
{
lean_object* v_a_730_; lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_738_; 
v_a_730_ = lean_ctor_get(v___x_717_, 0);
v_a_731_ = lean_ctor_get(v___x_717_, 1);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_738_ == 0)
{
v___x_733_ = v___x_717_;
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_inc(v_a_730_);
lean_dec(v___x_717_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_736_; 
if (v_isShared_734_ == 0)
{
v___x_736_ = v___x_733_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_a_730_);
lean_ctor_set(v_reuseFailAlloc_737_, 1, v_a_731_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_decodeArrayOrSingleton(lean_object* v_00_u03b1_739_, lean_object* v_dec_740_, lean_object* v_v_741_, lean_object* v_a_742_){
_start:
{
if (lean_obj_tag(v_v_741_) == 5)
{
lean_object* v_xs_743_; lean_object* v___x_744_; 
v_xs_743_ = lean_ctor_get(v_v_741_, 1);
lean_inc_ref(v_xs_743_);
lean_dec_ref(v_v_741_);
v___x_744_ = l_Lake_Toml_decodeArray___redArg(v_dec_740_, v_xs_743_, v_a_742_);
return v___x_744_;
}
else
{
lean_object* v___x_745_; 
v___x_745_ = lean_apply_2(v_dec_740_, v_v_741_, v_a_742_);
if (lean_obj_tag(v___x_745_) == 0)
{
lean_object* v_a_746_; lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_757_; 
v_a_746_ = lean_ctor_get(v___x_745_, 0);
v_a_747_ = lean_ctor_get(v___x_745_, 1);
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_745_);
if (v_isSharedCheck_757_ == 0)
{
v___x_749_ = v___x_745_;
v_isShared_750_ = v_isSharedCheck_757_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_inc(v_a_746_);
lean_dec(v___x_745_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_757_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_755_; 
v___x_751_ = lean_unsigned_to_nat(1u);
v___x_752_ = lean_mk_empty_array_with_capacity(v___x_751_);
v___x_753_ = lean_array_push(v___x_752_, v_a_746_);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 0, v___x_753_);
v___x_755_ = v___x_749_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_753_);
lean_ctor_set(v_reuseFailAlloc_756_, 1, v_a_747_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
else
{
lean_object* v_a_758_; lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_766_; 
v_a_758_ = lean_ctor_get(v___x_745_, 0);
v_a_759_ = lean_ctor_get(v___x_745_, 1);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_745_);
if (v_isSharedCheck_766_ == 0)
{
v___x_761_ = v___x_745_;
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_inc(v_a_758_);
lean_dec(v___x_745_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_764_; 
if (v_isShared_762_ == 0)
{
v___x_764_ = v___x_761_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_a_758_);
lean_ctor_set(v_reuseFailAlloc_765_, 1, v_a_759_);
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
LEAN_EXPORT lean_object* l_Lake_Toml_Value_decodeTable(lean_object* v_v_768_, lean_object* v_a_769_){
_start:
{
lean_object* v___y_771_; 
if (lean_obj_tag(v_v_768_) == 6)
{
lean_object* v_xs_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_784_; 
v_xs_777_ = lean_ctor_get(v_v_768_, 1);
v_isSharedCheck_784_ = !lean_is_exclusive(v_v_768_);
if (v_isSharedCheck_784_ == 0)
{
lean_object* v_unused_785_; 
v_unused_785_ = lean_ctor_get(v_v_768_, 0);
lean_dec(v_unused_785_);
v___x_779_ = v_v_768_;
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_xs_777_);
lean_dec(v_v_768_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_782_; 
if (v_isShared_780_ == 0)
{
lean_ctor_set_tag(v___x_779_, 0);
lean_ctor_set(v___x_779_, 1, v_a_769_);
lean_ctor_set(v___x_779_, 0, v_xs_777_);
v___x_782_ = v___x_779_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_xs_777_);
lean_ctor_set(v_reuseFailAlloc_783_, 1, v_a_769_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
}
else
{
lean_object* v_ref_786_; 
v_ref_786_ = lean_ctor_get(v_v_768_, 0);
lean_inc(v_ref_786_);
lean_dec_ref(v_v_768_);
v___y_771_ = v_ref_786_;
goto v___jp_770_;
}
v___jp_770_:
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_772_ = ((lean_object*)(l_Lake_Toml_Value_decodeTable___closed__0));
v___x_773_ = lean_box(0);
v___x_774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_774_, 0, v___y_771_);
lean_ctor_set(v___x_774_, 1, v___x_772_);
v___x_775_ = lean_array_push(v_a_769_, v___x_774_);
v___x_776_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_776_, 0, v___x_773_);
lean_ctor_set(v___x_776_, 1, v___x_775_);
return v___x_776_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_decodeKeyval___redArg___lam__0(lean_object* v_iniPos_791_, lean_object* v_k_792_, lean_object* v_i_793_, lean_object* v_a_794_, lean_object* v_x_795_){
_start:
{
uint8_t v___x_796_; 
v___x_796_ = lean_nat_dec_le(v_iniPos_791_, v_i_793_);
if (v___x_796_ == 0)
{
lean_dec(v_k_792_);
return v_a_794_;
}
else
{
lean_object* v_ref_797_; lean_object* v_msg_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_811_; 
v_ref_797_ = lean_ctor_get(v_a_794_, 0);
v_msg_798_ = lean_ctor_get(v_a_794_, 1);
v_isSharedCheck_811_ = !lean_is_exclusive(v_a_794_);
if (v_isSharedCheck_811_ == 0)
{
v___x_800_ = v_a_794_;
v_isShared_801_ = v_isSharedCheck_811_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_msg_798_);
lean_inc(v_ref_797_);
lean_dec(v_a_794_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_811_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_809_; 
v___x_802_ = ((lean_object*)(l_Lake_Toml_decodeKeyval___redArg___lam__0___closed__0));
v___x_803_ = l_Lake_Toml_ppKey(v_k_792_);
v___x_804_ = lean_string_append(v___x_802_, v___x_803_);
lean_dec_ref(v___x_803_);
v___x_805_ = ((lean_object*)(l_Lake_Toml_decodeKeyval___redArg___lam__0___closed__1));
v___x_806_ = lean_string_append(v___x_804_, v___x_805_);
v___x_807_ = lean_string_append(v___x_806_, v_msg_798_);
lean_dec_ref(v_msg_798_);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 1, v___x_807_);
v___x_809_ = v___x_800_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_ref_797_);
lean_ctor_set(v_reuseFailAlloc_810_, 1, v___x_807_);
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
LEAN_EXPORT lean_object* l_Lake_Toml_decodeKeyval___redArg___lam__0___boxed(lean_object* v_iniPos_812_, lean_object* v_k_813_, lean_object* v_i_814_, lean_object* v_a_815_, lean_object* v_x_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_Lake_Toml_decodeKeyval___redArg___lam__0(v_iniPos_812_, v_k_813_, v_i_814_, v_a_815_, v_x_816_);
lean_dec(v_i_814_);
lean_dec(v_iniPos_812_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_decodeKeyval___redArg___lam__1(lean_object* v___f_818_, lean_object* v_es_819_){
_start:
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_820_ = ((lean_object*)(l_Lake_Toml_decodeArray___redArg___closed__9));
v___x_821_ = lean_array_get_size(v_es_819_);
v___x_822_ = lean_unsigned_to_nat(0u);
v___x_823_ = lean_mk_empty_array_with_capacity(v___x_821_);
v___x_824_ = l_Array_mapFinIdxM_map___redArg(v___x_820_, v_es_819_, v___f_818_, v___x_821_, v___x_822_, v___x_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_decodeKeyval___redArg(lean_object* v_dec_825_, lean_object* v_k_826_, lean_object* v_v_827_, lean_object* v_es_828_){
_start:
{
lean_object* v_iniPos_829_; lean_object* v___f_830_; lean_object* v___x_831_; 
v_iniPos_829_ = lean_array_get_size(v_es_828_);
v___f_830_ = lean_alloc_closure((void*)(l_Lake_Toml_decodeKeyval___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_830_, 0, v_iniPos_829_);
lean_closure_set(v___f_830_, 1, v_k_826_);
v___x_831_ = lean_apply_2(v_dec_825_, v_v_827_, v_es_828_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_object* v_a_832_; lean_object* v_a_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_841_; 
v_a_832_ = lean_ctor_get(v___x_831_, 0);
v_a_833_ = lean_ctor_get(v___x_831_, 1);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_841_ == 0)
{
v___x_835_ = v___x_831_;
v_isShared_836_ = v_isSharedCheck_841_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_a_833_);
lean_inc(v_a_832_);
lean_dec(v___x_831_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_841_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_837_; lean_object* v___x_839_; 
v___x_837_ = l_Lake_Toml_decodeKeyval___redArg___lam__1(v___f_830_, v_a_833_);
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 1, v___x_837_);
v___x_839_ = v___x_835_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_a_832_);
lean_ctor_set(v_reuseFailAlloc_840_, 1, v___x_837_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
else
{
lean_object* v_a_842_; lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_851_; 
v_a_842_ = lean_ctor_get(v___x_831_, 0);
v_a_843_ = lean_ctor_get(v___x_831_, 1);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_851_ == 0)
{
v___x_845_ = v___x_831_;
v_isShared_846_ = v_isSharedCheck_851_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_inc(v_a_842_);
lean_dec(v___x_831_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_851_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_847_; lean_object* v___x_849_; 
v___x_847_ = l_Lake_Toml_decodeKeyval___redArg___lam__1(v___f_830_, v_a_843_);
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 1, v___x_847_);
v___x_849_ = v___x_845_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_a_842_);
lean_ctor_set(v_reuseFailAlloc_850_, 1, v___x_847_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_decodeKeyval(lean_object* v_00_u03b1_852_, lean_object* v_dec_853_, lean_object* v_k_854_, lean_object* v_v_855_, lean_object* v_es_856_){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = l_Lake_Toml_decodeKeyval___redArg(v_dec_853_, v_k_854_, v_v_855_, v_es_856_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decodeValue(lean_object* v_t_860_, lean_object* v_k_861_, lean_object* v_ref_862_, lean_object* v_a_863_){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_864_ = ((lean_object*)(l_Lake_Toml_Table_decodeValue___closed__0));
lean_inc(v_k_861_);
v___x_865_ = l_Lake_Toml_RBDict_findEntry_x3f___redArg(v___x_864_, v_k_861_, v_t_860_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_866_ = ((lean_object*)(l_Lake_Toml_Table_decodeValue___closed__1));
v___x_867_ = l_Lake_Toml_ppKey(v_k_861_);
v___x_868_ = lean_string_append(v___x_866_, v___x_867_);
lean_dec_ref(v___x_867_);
v___x_869_ = lean_box(0);
v___x_870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_870_, 0, v_ref_862_);
lean_ctor_set(v___x_870_, 1, v___x_868_);
v___x_871_ = lean_array_push(v_a_863_, v___x_870_);
v___x_872_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_872_, 0, v___x_869_);
lean_ctor_set(v___x_872_, 1, v___x_871_);
return v___x_872_;
}
else
{
lean_object* v_val_873_; lean_object* v_snd_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_881_; 
lean_dec(v_ref_862_);
lean_dec(v_k_861_);
v_val_873_ = lean_ctor_get(v___x_865_, 0);
lean_inc(v_val_873_);
lean_dec_ref(v___x_865_);
v_snd_874_ = lean_ctor_get(v_val_873_, 1);
v_isSharedCheck_881_ = !lean_is_exclusive(v_val_873_);
if (v_isSharedCheck_881_ == 0)
{
lean_object* v_unused_882_; 
v_unused_882_ = lean_ctor_get(v_val_873_, 0);
lean_dec(v_unused_882_);
v___x_876_ = v_val_873_;
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_snd_874_);
lean_dec(v_val_873_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_879_; 
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 1, v_a_863_);
lean_ctor_set(v___x_876_, 0, v_snd_874_);
v___x_879_ = v___x_876_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_snd_874_);
lean_ctor_set(v_reuseFailAlloc_880_, 1, v_a_863_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decode___redArg(lean_object* v_dec_883_, lean_object* v_t_884_, lean_object* v_k_885_, lean_object* v_ref_886_, lean_object* v_a_887_){
_start:
{
lean_object* v___x_888_; 
lean_inc(v_k_885_);
v___x_888_ = l_Lake_Toml_Table_decodeValue(v_t_884_, v_k_885_, v_ref_886_, v_a_887_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v_a_889_; lean_object* v_a_890_; lean_object* v___x_891_; 
v_a_889_ = lean_ctor_get(v___x_888_, 0);
lean_inc(v_a_889_);
v_a_890_ = lean_ctor_get(v___x_888_, 1);
lean_inc(v_a_890_);
lean_dec_ref(v___x_888_);
v___x_891_ = l_Lake_Toml_decodeKeyval___redArg(v_dec_883_, v_k_885_, v_a_889_, v_a_890_);
return v___x_891_;
}
else
{
lean_object* v_a_892_; lean_object* v_a_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_900_; 
lean_dec(v_k_885_);
lean_dec_ref(v_dec_883_);
v_a_892_ = lean_ctor_get(v___x_888_, 0);
v_a_893_ = lean_ctor_get(v___x_888_, 1);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_900_ == 0)
{
v___x_895_ = v___x_888_;
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_a_893_);
lean_inc(v_a_892_);
lean_dec(v___x_888_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_898_; 
if (v_isShared_896_ == 0)
{
v___x_898_ = v___x_895_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_a_892_);
lean_ctor_set(v_reuseFailAlloc_899_, 1, v_a_893_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decode(lean_object* v_00_u03b1_901_, lean_object* v_dec_902_, lean_object* v_t_903_, lean_object* v_k_904_, lean_object* v_ref_905_, lean_object* v_a_906_){
_start:
{
lean_object* v___x_907_; 
lean_inc(v_k_904_);
v___x_907_ = l_Lake_Toml_Table_decodeValue(v_t_903_, v_k_904_, v_ref_905_, v_a_906_);
if (lean_obj_tag(v___x_907_) == 0)
{
lean_object* v_a_908_; lean_object* v_a_909_; lean_object* v___x_910_; 
v_a_908_ = lean_ctor_get(v___x_907_, 0);
lean_inc(v_a_908_);
v_a_909_ = lean_ctor_get(v___x_907_, 1);
lean_inc(v_a_909_);
lean_dec_ref(v___x_907_);
v___x_910_ = l_Lake_Toml_decodeKeyval___redArg(v_dec_902_, v_k_904_, v_a_908_, v_a_909_);
return v___x_910_;
}
else
{
lean_object* v_a_911_; lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_919_; 
lean_dec(v_k_904_);
lean_dec_ref(v_dec_902_);
v_a_911_ = lean_ctor_get(v___x_907_, 0);
v_a_912_ = lean_ctor_get(v___x_907_, 1);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_919_ == 0)
{
v___x_914_ = v___x_907_;
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_inc(v_a_911_);
lean_dec(v___x_907_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_917_; 
if (v_isShared_915_ == 0)
{
v___x_917_ = v___x_914_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_a_911_);
lean_ctor_set(v_reuseFailAlloc_918_, 1, v_a_912_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decode_x3f___redArg(lean_object* v_dec_920_, lean_object* v_t_921_, lean_object* v_k_922_, lean_object* v_a_923_){
_start:
{
lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_924_ = ((lean_object*)(l_Lake_Toml_Table_decodeValue___closed__0));
lean_inc(v_k_922_);
v___x_925_ = l_Lake_Toml_RBDict_findEntry_x3f___redArg(v___x_924_, v_k_922_, v_t_921_);
if (lean_obj_tag(v___x_925_) == 0)
{
lean_object* v___x_926_; lean_object* v___x_927_; 
lean_dec(v_k_922_);
lean_dec_ref(v_dec_920_);
v___x_926_ = lean_box(0);
v___x_927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
lean_ctor_set(v___x_927_, 1, v_a_923_);
return v___x_927_;
}
else
{
lean_object* v_val_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_955_; 
v_val_928_ = lean_ctor_get(v___x_925_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_925_);
if (v_isSharedCheck_955_ == 0)
{
v___x_930_ = v___x_925_;
v_isShared_931_ = v_isSharedCheck_955_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_val_928_);
lean_dec(v___x_925_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_955_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v_snd_932_; lean_object* v___x_933_; 
v_snd_932_ = lean_ctor_get(v_val_928_, 1);
lean_inc(v_snd_932_);
lean_dec(v_val_928_);
v___x_933_ = l_Lake_Toml_decodeKeyval___redArg(v_dec_920_, v_k_922_, v_snd_932_, v_a_923_);
if (lean_obj_tag(v___x_933_) == 0)
{
lean_object* v_a_934_; lean_object* v_a_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_945_; 
v_a_934_ = lean_ctor_get(v___x_933_, 0);
v_a_935_ = lean_ctor_get(v___x_933_, 1);
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_945_ == 0)
{
v___x_937_ = v___x_933_;
v_isShared_938_ = v_isSharedCheck_945_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_a_935_);
lean_inc(v_a_934_);
lean_dec(v___x_933_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_945_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_940_; 
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 0, v_a_934_);
v___x_940_ = v___x_930_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v_a_934_);
v___x_940_ = v_reuseFailAlloc_944_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
lean_object* v___x_942_; 
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 0, v___x_940_);
v___x_942_ = v___x_937_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v___x_940_);
lean_ctor_set(v_reuseFailAlloc_943_, 1, v_a_935_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
}
else
{
lean_object* v_a_946_; lean_object* v_a_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_954_; 
lean_del_object(v___x_930_);
v_a_946_ = lean_ctor_get(v___x_933_, 0);
v_a_947_ = lean_ctor_get(v___x_933_, 1);
v_isSharedCheck_954_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_954_ == 0)
{
v___x_949_ = v___x_933_;
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_a_947_);
lean_inc(v_a_946_);
lean_dec(v___x_933_);
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
v_reuseFailAlloc_953_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v_a_946_);
lean_ctor_set(v_reuseFailAlloc_953_, 1, v_a_947_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decode_x3f(lean_object* v_00_u03b1_956_, lean_object* v_dec_957_, lean_object* v_t_958_, lean_object* v_k_959_, lean_object* v_a_960_){
_start:
{
lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_961_ = ((lean_object*)(l_Lake_Toml_Table_decodeValue___closed__0));
lean_inc(v_k_959_);
v___x_962_ = l_Lake_Toml_RBDict_findEntry_x3f___redArg(v___x_961_, v_k_959_, v_t_958_);
if (lean_obj_tag(v___x_962_) == 0)
{
lean_object* v___x_963_; lean_object* v___x_964_; 
lean_dec(v_k_959_);
lean_dec_ref(v_dec_957_);
v___x_963_ = lean_box(0);
v___x_964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
lean_ctor_set(v___x_964_, 1, v_a_960_);
return v___x_964_;
}
else
{
lean_object* v_val_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_992_; 
v_val_965_ = lean_ctor_get(v___x_962_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_992_ == 0)
{
v___x_967_ = v___x_962_;
v_isShared_968_ = v_isSharedCheck_992_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_val_965_);
lean_dec(v___x_962_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_992_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v_snd_969_; lean_object* v___x_970_; 
v_snd_969_ = lean_ctor_get(v_val_965_, 1);
lean_inc(v_snd_969_);
lean_dec(v_val_965_);
v___x_970_ = l_Lake_Toml_decodeKeyval___redArg(v_dec_957_, v_k_959_, v_snd_969_, v_a_960_);
if (lean_obj_tag(v___x_970_) == 0)
{
lean_object* v_a_971_; lean_object* v_a_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_982_; 
v_a_971_ = lean_ctor_get(v___x_970_, 0);
v_a_972_ = lean_ctor_get(v___x_970_, 1);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_982_ == 0)
{
v___x_974_ = v___x_970_;
v_isShared_975_ = v_isSharedCheck_982_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_a_972_);
lean_inc(v_a_971_);
lean_dec(v___x_970_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_982_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v___x_977_; 
if (v_isShared_968_ == 0)
{
lean_ctor_set(v___x_967_, 0, v_a_971_);
v___x_977_ = v___x_967_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_a_971_);
v___x_977_ = v_reuseFailAlloc_981_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
lean_object* v___x_979_; 
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 0, v___x_977_);
v___x_979_ = v___x_974_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v___x_977_);
lean_ctor_set(v_reuseFailAlloc_980_, 1, v_a_972_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
}
else
{
lean_object* v_a_983_; lean_object* v_a_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_991_; 
lean_del_object(v___x_967_);
v_a_983_ = lean_ctor_get(v___x_970_, 0);
v_a_984_ = lean_ctor_get(v___x_970_, 1);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_991_ == 0)
{
v___x_986_ = v___x_970_;
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_a_984_);
lean_inc(v_a_983_);
lean_dec(v___x_970_);
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
v_reuseFailAlloc_990_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_a_983_);
lean_ctor_set(v_reuseFailAlloc_990_, 1, v_a_984_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decodeNameMap___redArg___lam__0(lean_object* v_fst_993_, lean_object* v_m_994_, lean_object* v_v_995_){
_start:
{
lean_object* v___x_996_; 
v___x_996_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_993_, v_v_995_, v_m_994_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decodeNameMap___redArg___lam__1(lean_object* v_dec_997_, lean_object* v_x1_998_, lean_object* v_x2_999_, lean_object* v___y_1000_){
_start:
{
lean_object* v_fst_1001_; lean_object* v_snd_1002_; lean_object* v___f_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
v_fst_1001_ = lean_ctor_get(v_x2_999_, 0);
lean_inc(v_fst_1001_);
v_snd_1002_ = lean_ctor_get(v_x2_999_, 1);
lean_inc(v_snd_1002_);
lean_dec_ref(v_x2_999_);
v___f_1003_ = lean_alloc_closure((void*)(l_Lake_Toml_Table_decodeNameMap___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1003_, 0, v_fst_1001_);
v___x_1004_ = lean_apply_1(v_dec_997_, v_snd_1002_);
v___x_1005_ = l_Lake_Toml_mergeErrors___redArg(v_x1_998_, v___x_1004_, v___f_1003_, v___y_1000_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decodeNameMap___redArg(lean_object* v_dec_1008_, lean_object* v_t_1009_, lean_object* v_a_1010_){
_start:
{
lean_object* v_items_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1037_; 
v_items_1011_ = lean_ctor_get(v_t_1009_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v_t_1009_);
if (v_isSharedCheck_1037_ == 0)
{
lean_object* v_unused_1038_; 
v_unused_1038_ = lean_ctor_get(v_t_1009_, 1);
lean_dec(v_unused_1038_);
v___x_1013_ = v_t_1009_;
v_isShared_1014_ = v_isSharedCheck_1037_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_items_1011_);
lean_dec(v_t_1009_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1037_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; uint8_t v___x_1019_; 
v___x_1015_ = lean_box(1);
v___x_1016_ = lean_unsigned_to_nat(0u);
v___x_1017_ = lean_array_get_size(v_items_1011_);
v___x_1018_ = ((lean_object*)(l_Lake_Toml_decodeArray___redArg___closed__9));
v___x_1019_ = lean_nat_dec_lt(v___x_1016_, v___x_1017_);
if (v___x_1019_ == 0)
{
lean_object* v___x_1021_; 
lean_dec_ref(v_items_1011_);
lean_dec_ref(v_dec_1008_);
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 1, v_a_1010_);
lean_ctor_set(v___x_1013_, 0, v___x_1015_);
v___x_1021_ = v___x_1013_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v___x_1015_);
lean_ctor_set(v_reuseFailAlloc_1022_, 1, v_a_1010_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
else
{
lean_object* v___f_1023_; lean_object* v___x_1024_; uint8_t v___x_1025_; 
v___f_1023_ = lean_alloc_closure((void*)(l_Lake_Toml_Table_decodeNameMap___redArg___lam__1), 4, 1);
lean_closure_set(v___f_1023_, 0, v_dec_1008_);
v___x_1024_ = ((lean_object*)(l_Lake_Toml_Table_decodeNameMap___redArg___closed__0));
v___x_1025_ = lean_nat_dec_le(v___x_1017_, v___x_1017_);
if (v___x_1025_ == 0)
{
if (v___x_1019_ == 0)
{
lean_object* v___x_1027_; 
lean_dec_ref(v___f_1023_);
lean_dec_ref(v_items_1011_);
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 1, v_a_1010_);
lean_ctor_set(v___x_1013_, 0, v___x_1015_);
v___x_1027_ = v___x_1013_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v___x_1015_);
lean_ctor_set(v_reuseFailAlloc_1028_, 1, v_a_1010_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
else
{
size_t v___x_1029_; size_t v___x_1030_; lean_object* v___x_150__overap_1031_; lean_object* v___x_1032_; 
lean_del_object(v___x_1013_);
v___x_1029_ = ((size_t)0ULL);
v___x_1030_ = lean_usize_of_nat(v___x_1017_);
v___x_150__overap_1031_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1018_, v___f_1023_, v_items_1011_, v___x_1029_, v___x_1030_, v___x_1024_);
v___x_1032_ = lean_apply_1(v___x_150__overap_1031_, v_a_1010_);
return v___x_1032_;
}
}
else
{
size_t v___x_1033_; size_t v___x_1034_; lean_object* v___x_155__overap_1035_; lean_object* v___x_1036_; 
lean_del_object(v___x_1013_);
v___x_1033_ = ((size_t)0ULL);
v___x_1034_ = lean_usize_of_nat(v___x_1017_);
v___x_155__overap_1035_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1018_, v___f_1023_, v_items_1011_, v___x_1033_, v___x_1034_, v___x_1024_);
v___x_1036_ = lean_apply_1(v___x_155__overap_1035_, v_a_1010_);
return v___x_1036_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decodeNameMap(lean_object* v_00_u03b1_1039_, lean_object* v_dec_1040_, lean_object* v_t_1041_, lean_object* v_a_1042_){
_start:
{
lean_object* v___x_1043_; 
v___x_1043_ = l_Lake_Toml_Table_decodeNameMap___redArg(v_dec_1040_, v_t_1041_, v_a_1042_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_instDecodeTomlNameMap___redArg___lam__0(lean_object* v_inst_1044_, lean_object* v_x_1045_, lean_object* v___y_1046_){
_start:
{
lean_object* v___x_1047_; 
v___x_1047_ = l_Lake_Toml_Value_decodeTable(v_x_1045_, v___y_1046_);
if (lean_obj_tag(v___x_1047_) == 0)
{
lean_object* v_a_1048_; lean_object* v_a_1049_; lean_object* v___x_1050_; 
v_a_1048_ = lean_ctor_get(v___x_1047_, 0);
lean_inc(v_a_1048_);
v_a_1049_ = lean_ctor_get(v___x_1047_, 1);
lean_inc(v_a_1049_);
lean_dec_ref(v___x_1047_);
v___x_1050_ = l_Lake_Toml_Table_decodeNameMap___redArg(v_inst_1044_, v_a_1048_, v_a_1049_);
return v___x_1050_;
}
else
{
lean_object* v_a_1051_; lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1059_; 
lean_dec_ref(v_inst_1044_);
v_a_1051_ = lean_ctor_get(v___x_1047_, 0);
v_a_1052_ = lean_ctor_get(v___x_1047_, 1);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1054_ = v___x_1047_;
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_inc(v_a_1051_);
lean_dec(v___x_1047_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1057_; 
if (v_isShared_1055_ == 0)
{
v___x_1057_ = v___x_1054_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_a_1051_);
lean_ctor_set(v_reuseFailAlloc_1058_, 1, v_a_1052_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_instDecodeTomlNameMap___redArg(lean_object* v_inst_1060_){
_start:
{
lean_object* v___f_1061_; 
v___f_1061_ = lean_alloc_closure((void*)(l_Lake_Toml_Table_instDecodeTomlNameMap___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1061_, 0, v_inst_1060_);
return v___f_1061_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_instDecodeTomlNameMap(lean_object* v_00_u03b1_1062_, lean_object* v_inst_1063_){
_start:
{
lean_object* v___f_1064_; 
v___f_1064_ = lean_alloc_closure((void*)(l_Lake_Toml_Table_instDecodeTomlNameMap___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1064_, 0, v_inst_1063_);
return v___f_1064_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_tryDecode___redArg(lean_object* v_inst_1065_, lean_object* v_dec_1066_, lean_object* v_t_1067_, lean_object* v_k_1068_, lean_object* v_ref_1069_, lean_object* v_a_1070_){
_start:
{
lean_object* v___x_1071_; 
lean_inc(v_k_1068_);
v___x_1071_ = l_Lake_Toml_Table_decodeValue(v_t_1067_, v_k_1068_, v_ref_1069_, v_a_1070_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v_a_1072_; lean_object* v_a_1073_; lean_object* v___x_1074_; 
v_a_1072_ = lean_ctor_get(v___x_1071_, 0);
lean_inc(v_a_1072_);
v_a_1073_ = lean_ctor_get(v___x_1071_, 1);
lean_inc(v_a_1073_);
lean_dec_ref(v___x_1071_);
v___x_1074_ = l_Lake_Toml_decodeKeyval___redArg(v_dec_1066_, v_k_1068_, v_a_1072_, v_a_1073_);
if (lean_obj_tag(v___x_1074_) == 0)
{
lean_object* v_a_1075_; lean_object* v_a_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1083_; 
lean_dec(v_inst_1065_);
v_a_1075_ = lean_ctor_get(v___x_1074_, 0);
v_a_1076_ = lean_ctor_get(v___x_1074_, 1);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1078_ = v___x_1074_;
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_a_1076_);
lean_inc(v_a_1075_);
lean_dec(v___x_1074_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1081_; 
if (v_isShared_1079_ == 0)
{
v___x_1081_ = v___x_1078_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_a_1075_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v_a_1076_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
else
{
lean_object* v_a_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1091_; 
v_a_1084_ = lean_ctor_get(v___x_1074_, 1);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1091_ == 0)
{
lean_object* v_unused_1092_; 
v_unused_1092_ = lean_ctor_get(v___x_1074_, 0);
lean_dec(v_unused_1092_);
v___x_1086_ = v___x_1074_;
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_a_1084_);
lean_dec(v___x_1074_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1089_; 
if (v_isShared_1087_ == 0)
{
lean_ctor_set_tag(v___x_1086_, 0);
lean_ctor_set(v___x_1086_, 0, v_inst_1065_);
v___x_1089_ = v___x_1086_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_inst_1065_);
lean_ctor_set(v_reuseFailAlloc_1090_, 1, v_a_1084_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
}
else
{
lean_object* v_a_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1100_; 
lean_dec(v_k_1068_);
lean_dec_ref(v_dec_1066_);
v_a_1093_ = lean_ctor_get(v___x_1071_, 1);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1100_ == 0)
{
lean_object* v_unused_1101_; 
v_unused_1101_ = lean_ctor_get(v___x_1071_, 0);
lean_dec(v_unused_1101_);
v___x_1095_ = v___x_1071_;
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_a_1093_);
lean_dec(v___x_1071_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1098_; 
if (v_isShared_1096_ == 0)
{
lean_ctor_set_tag(v___x_1095_, 0);
lean_ctor_set(v___x_1095_, 0, v_inst_1065_);
v___x_1098_ = v___x_1095_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_inst_1065_);
lean_ctor_set(v_reuseFailAlloc_1099_, 1, v_a_1093_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_tryDecode(lean_object* v_00_u03b1_1102_, lean_object* v_inst_1103_, lean_object* v_dec_1104_, lean_object* v_t_1105_, lean_object* v_k_1106_, lean_object* v_ref_1107_, lean_object* v_a_1108_){
_start:
{
lean_object* v___x_1109_; 
lean_inc(v_k_1106_);
v___x_1109_ = l_Lake_Toml_Table_decodeValue(v_t_1105_, v_k_1106_, v_ref_1107_, v_a_1108_);
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_object* v_a_1110_; lean_object* v_a_1111_; lean_object* v___x_1112_; 
v_a_1110_ = lean_ctor_get(v___x_1109_, 0);
lean_inc(v_a_1110_);
v_a_1111_ = lean_ctor_get(v___x_1109_, 1);
lean_inc(v_a_1111_);
lean_dec_ref(v___x_1109_);
v___x_1112_ = l_Lake_Toml_decodeKeyval___redArg(v_dec_1104_, v_k_1106_, v_a_1110_, v_a_1111_);
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_object* v_a_1113_; lean_object* v_a_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1121_; 
lean_dec(v_inst_1103_);
v_a_1113_ = lean_ctor_get(v___x_1112_, 0);
v_a_1114_ = lean_ctor_get(v___x_1112_, 1);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1116_ = v___x_1112_;
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_a_1114_);
lean_inc(v_a_1113_);
lean_dec(v___x_1112_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1119_; 
if (v_isShared_1117_ == 0)
{
v___x_1119_ = v___x_1116_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_a_1113_);
lean_ctor_set(v_reuseFailAlloc_1120_, 1, v_a_1114_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
else
{
lean_object* v_a_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1129_; 
v_a_1122_ = lean_ctor_get(v___x_1112_, 1);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1129_ == 0)
{
lean_object* v_unused_1130_; 
v_unused_1130_ = lean_ctor_get(v___x_1112_, 0);
lean_dec(v_unused_1130_);
v___x_1124_ = v___x_1112_;
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_a_1122_);
lean_dec(v___x_1112_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1127_; 
if (v_isShared_1125_ == 0)
{
lean_ctor_set_tag(v___x_1124_, 0);
lean_ctor_set(v___x_1124_, 0, v_inst_1103_);
v___x_1127_ = v___x_1124_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_inst_1103_);
lean_ctor_set(v_reuseFailAlloc_1128_, 1, v_a_1122_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
}
}
else
{
lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1138_; 
lean_dec(v_k_1106_);
lean_dec_ref(v_dec_1104_);
v_a_1131_ = lean_ctor_get(v___x_1109_, 1);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1138_ == 0)
{
lean_object* v_unused_1139_; 
v_unused_1139_ = lean_ctor_get(v___x_1109_, 0);
lean_dec(v_unused_1139_);
v___x_1133_ = v___x_1109_;
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_dec(v___x_1109_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1136_; 
if (v_isShared_1134_ == 0)
{
lean_ctor_set_tag(v___x_1133_, 0);
lean_ctor_set(v___x_1133_, 0, v_inst_1103_);
v___x_1136_ = v___x_1133_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_inst_1103_);
lean_ctor_set(v_reuseFailAlloc_1137_, 1, v_a_1131_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_tryDecode_x3f___redArg(lean_object* v_dec_1140_, lean_object* v_t_1141_, lean_object* v_k_1142_, lean_object* v_a_1143_){
_start:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1144_ = ((lean_object*)(l_Lake_Toml_Table_decodeValue___closed__0));
v___x_1145_ = l_Lake_Toml_RBDict_findEntry_x3f___redArg(v___x_1144_, v_k_1142_, v_t_1141_);
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v___x_1146_; lean_object* v___x_1147_; 
lean_dec_ref(v_dec_1140_);
v___x_1146_ = lean_box(0);
v___x_1147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1146_);
lean_ctor_set(v___x_1147_, 1, v_a_1143_);
return v___x_1147_;
}
else
{
lean_object* v_val_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1176_; 
v_val_1148_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1176_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1150_ = v___x_1145_;
v_isShared_1151_ = v_isSharedCheck_1176_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_val_1148_);
lean_dec(v___x_1145_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1176_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v_snd_1152_; lean_object* v___x_1153_; 
v_snd_1152_ = lean_ctor_get(v_val_1148_, 1);
lean_inc(v_snd_1152_);
lean_dec(v_val_1148_);
v___x_1153_ = lean_apply_2(v_dec_1140_, v_snd_1152_, v_a_1143_);
if (lean_obj_tag(v___x_1153_) == 0)
{
lean_object* v_a_1154_; lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1165_; 
v_a_1154_ = lean_ctor_get(v___x_1153_, 0);
v_a_1155_ = lean_ctor_get(v___x_1153_, 1);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1153_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1157_ = v___x_1153_;
v_isShared_1158_ = v_isSharedCheck_1165_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_inc(v_a_1154_);
lean_dec(v___x_1153_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1165_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1160_; 
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 0, v_a_1154_);
v___x_1160_ = v___x_1150_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_a_1154_);
v___x_1160_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
lean_object* v___x_1162_; 
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 0, v___x_1160_);
v___x_1162_ = v___x_1157_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v___x_1160_);
lean_ctor_set(v_reuseFailAlloc_1163_, 1, v_a_1155_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
}
else
{
lean_object* v_a_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1174_; 
lean_del_object(v___x_1150_);
v_a_1166_ = lean_ctor_get(v___x_1153_, 1);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1153_);
if (v_isSharedCheck_1174_ == 0)
{
lean_object* v_unused_1175_; 
v_unused_1175_ = lean_ctor_get(v___x_1153_, 0);
lean_dec(v_unused_1175_);
v___x_1168_ = v___x_1153_;
v_isShared_1169_ = v_isSharedCheck_1174_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_a_1166_);
lean_dec(v___x_1153_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1174_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1170_; lean_object* v___x_1172_; 
v___x_1170_ = lean_box(0);
if (v_isShared_1169_ == 0)
{
lean_ctor_set_tag(v___x_1168_, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1170_);
v___x_1172_ = v___x_1168_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v___x_1170_);
lean_ctor_set(v_reuseFailAlloc_1173_, 1, v_a_1166_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_tryDecode_x3f(lean_object* v_00_u03b1_1177_, lean_object* v_dec_1178_, lean_object* v_t_1179_, lean_object* v_k_1180_, lean_object* v_a_1181_){
_start:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1182_ = ((lean_object*)(l_Lake_Toml_Table_decodeValue___closed__0));
v___x_1183_ = l_Lake_Toml_RBDict_findEntry_x3f___redArg(v___x_1182_, v_k_1180_, v_t_1179_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v___x_1184_; lean_object* v___x_1185_; 
lean_dec_ref(v_dec_1178_);
v___x_1184_ = lean_box(0);
v___x_1185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1184_);
lean_ctor_set(v___x_1185_, 1, v_a_1181_);
return v___x_1185_;
}
else
{
lean_object* v_val_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1214_; 
v_val_1186_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1188_ = v___x_1183_;
v_isShared_1189_ = v_isSharedCheck_1214_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_val_1186_);
lean_dec(v___x_1183_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1214_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v_snd_1190_; lean_object* v___x_1191_; 
v_snd_1190_ = lean_ctor_get(v_val_1186_, 1);
lean_inc(v_snd_1190_);
lean_dec(v_val_1186_);
v___x_1191_ = lean_apply_2(v_dec_1178_, v_snd_1190_, v_a_1181_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v_a_1192_; lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1203_; 
v_a_1192_ = lean_ctor_get(v___x_1191_, 0);
v_a_1193_ = lean_ctor_get(v___x_1191_, 1);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1195_ = v___x_1191_;
v_isShared_1196_ = v_isSharedCheck_1203_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_inc(v_a_1192_);
lean_dec(v___x_1191_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1203_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1198_; 
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 0, v_a_1192_);
v___x_1198_ = v___x_1188_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_a_1192_);
v___x_1198_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
lean_object* v___x_1200_; 
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 0, v___x_1198_);
v___x_1200_ = v___x_1195_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v___x_1198_);
lean_ctor_set(v_reuseFailAlloc_1201_, 1, v_a_1193_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
}
}
else
{
lean_object* v_a_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1212_; 
lean_del_object(v___x_1188_);
v_a_1204_ = lean_ctor_get(v___x_1191_, 1);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1212_ == 0)
{
lean_object* v_unused_1213_; 
v_unused_1213_ = lean_ctor_get(v___x_1191_, 0);
lean_dec(v_unused_1213_);
v___x_1206_ = v___x_1191_;
v_isShared_1207_ = v_isSharedCheck_1212_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_a_1204_);
lean_dec(v___x_1191_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1212_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1208_; lean_object* v___x_1210_; 
v___x_1208_ = lean_box(0);
if (v_isShared_1207_ == 0)
{
lean_ctor_set_tag(v___x_1206_, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1208_);
v___x_1210_ = v___x_1206_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v___x_1208_);
lean_ctor_set(v_reuseFailAlloc_1211_, 1, v_a_1204_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_tryDecodeD___redArg(lean_object* v_dec_1215_, lean_object* v_k_1216_, lean_object* v_default_1217_, lean_object* v_t_1218_, lean_object* v_a_1219_){
_start:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1220_ = ((lean_object*)(l_Lake_Toml_Table_decodeValue___closed__0));
v___x_1221_ = l_Lake_Toml_RBDict_findEntry_x3f___redArg(v___x_1220_, v_k_1216_, v_t_1218_);
if (lean_obj_tag(v___x_1221_) == 0)
{
lean_object* v___x_1222_; 
lean_dec_ref(v_dec_1215_);
v___x_1222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1222_, 0, v_default_1217_);
lean_ctor_set(v___x_1222_, 1, v_a_1219_);
return v___x_1222_;
}
else
{
lean_object* v_val_1223_; lean_object* v_snd_1224_; lean_object* v___x_1225_; 
v_val_1223_ = lean_ctor_get(v___x_1221_, 0);
lean_inc(v_val_1223_);
lean_dec_ref(v___x_1221_);
v_snd_1224_ = lean_ctor_get(v_val_1223_, 1);
lean_inc(v_snd_1224_);
lean_dec(v_val_1223_);
v___x_1225_ = lean_apply_2(v_dec_1215_, v_snd_1224_, v_a_1219_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_object* v_a_1226_; lean_object* v_a_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1234_; 
lean_dec(v_default_1217_);
v_a_1226_ = lean_ctor_get(v___x_1225_, 0);
v_a_1227_ = lean_ctor_get(v___x_1225_, 1);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1229_ = v___x_1225_;
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_a_1227_);
lean_inc(v_a_1226_);
lean_dec(v___x_1225_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1232_; 
if (v_isShared_1230_ == 0)
{
v___x_1232_ = v___x_1229_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_a_1226_);
lean_ctor_set(v_reuseFailAlloc_1233_, 1, v_a_1227_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
}
else
{
lean_object* v_a_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1242_; 
v_a_1235_ = lean_ctor_get(v___x_1225_, 1);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1242_ == 0)
{
lean_object* v_unused_1243_; 
v_unused_1243_ = lean_ctor_get(v___x_1225_, 0);
lean_dec(v_unused_1243_);
v___x_1237_ = v___x_1225_;
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_a_1235_);
lean_dec(v___x_1225_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1240_; 
if (v_isShared_1238_ == 0)
{
lean_ctor_set_tag(v___x_1237_, 0);
lean_ctor_set(v___x_1237_, 0, v_default_1217_);
v___x_1240_ = v___x_1237_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_default_1217_);
lean_ctor_set(v_reuseFailAlloc_1241_, 1, v_a_1235_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_tryDecodeD(lean_object* v_00_u03b1_1244_, lean_object* v_dec_1245_, lean_object* v_k_1246_, lean_object* v_default_1247_, lean_object* v_t_1248_, lean_object* v_a_1249_){
_start:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1250_ = ((lean_object*)(l_Lake_Toml_Table_decodeValue___closed__0));
v___x_1251_ = l_Lake_Toml_RBDict_findEntry_x3f___redArg(v___x_1250_, v_k_1246_, v_t_1248_);
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_object* v___x_1252_; 
lean_dec_ref(v_dec_1245_);
v___x_1252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1252_, 0, v_default_1247_);
lean_ctor_set(v___x_1252_, 1, v_a_1249_);
return v___x_1252_;
}
else
{
lean_object* v_val_1253_; lean_object* v_snd_1254_; lean_object* v___x_1255_; 
v_val_1253_ = lean_ctor_get(v___x_1251_, 0);
lean_inc(v_val_1253_);
lean_dec_ref(v___x_1251_);
v_snd_1254_ = lean_ctor_get(v_val_1253_, 1);
lean_inc(v_snd_1254_);
lean_dec(v_val_1253_);
v___x_1255_ = lean_apply_2(v_dec_1245_, v_snd_1254_, v_a_1249_);
if (lean_obj_tag(v___x_1255_) == 0)
{
lean_object* v_a_1256_; lean_object* v_a_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1264_; 
lean_dec(v_default_1247_);
v_a_1256_ = lean_ctor_get(v___x_1255_, 0);
v_a_1257_ = lean_ctor_get(v___x_1255_, 1);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1255_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1259_ = v___x_1255_;
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_a_1257_);
lean_inc(v_a_1256_);
lean_dec(v___x_1255_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1262_; 
if (v_isShared_1260_ == 0)
{
v___x_1262_ = v___x_1259_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_a_1256_);
lean_ctor_set(v_reuseFailAlloc_1263_, 1, v_a_1257_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
}
else
{
lean_object* v_a_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1272_; 
v_a_1265_ = lean_ctor_get(v___x_1255_, 1);
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1255_);
if (v_isSharedCheck_1272_ == 0)
{
lean_object* v_unused_1273_; 
v_unused_1273_ = lean_ctor_get(v___x_1255_, 0);
lean_dec(v_unused_1273_);
v___x_1267_ = v___x_1255_;
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_a_1265_);
lean_dec(v___x_1255_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1270_; 
if (v_isShared_1268_ == 0)
{
lean_ctor_set_tag(v___x_1267_, 0);
lean_ctor_set(v___x_1267_, 0, v_default_1247_);
v___x_1270_ = v___x_1267_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_default_1247_);
lean_ctor_set(v_reuseFailAlloc_1271_, 1, v_a_1265_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
}
}
}
}
lean_object* runtime_initialize_Init_System_FilePath(uint8_t builtin);
lean_object* runtime_initialize_Lake_Toml_Data(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Toml_Decode(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_System_FilePath(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Toml_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Toml_Decode(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_System_FilePath(uint8_t builtin);
lean_object* initialize_Lake_Toml_Data(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Macro(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Toml_Decode(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_FilePath(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Toml_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Toml_Decode(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Toml_Decode(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Toml_Decode(builtin);
}
#ifdef __cplusplus
}
#endif
