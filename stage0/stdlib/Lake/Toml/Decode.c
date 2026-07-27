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
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_Toml_logDecodeErrorAt(lean_object*, lean_object*, lean_object*);
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
lean_dec_ref_known(v_a_x3f_187_, 1);
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
lean_dec_ref_known(v_a_x3f_214_, 1);
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
lean_dec_ref_known(v_a_x3f_239_, 1);
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
lean_dec_ref_known(v_a_x3f_266_, 1);
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
lean_dec_ref_known(v___x_360_, 2);
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
LEAN_EXPORT lean_object* l_Lake_Toml_logDecodeErrorAt(lean_object* v_ref_402_, lean_object* v_msg_403_, lean_object* v_es_404_){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_405_ = lean_box(0);
v___x_406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_406_, 0, v_ref_402_);
lean_ctor_set(v___x_406_, 1, v_msg_403_);
v___x_407_ = lean_array_push(v_es_404_, v___x_406_);
v___x_408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_408_, 0, v___x_405_);
lean_ctor_set(v___x_408_, 1, v___x_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_throwDecodeErrorAt___redArg(lean_object* v_ref_409_, lean_object* v_msg_410_, lean_object* v_es_411_){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_412_ = lean_box(0);
v___x_413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_413_, 0, v_ref_409_);
lean_ctor_set(v___x_413_, 1, v_msg_410_);
v___x_414_ = lean_array_push(v_es_411_, v___x_413_);
v___x_415_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_415_, 0, v___x_412_);
lean_ctor_set(v___x_415_, 1, v___x_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_throwDecodeErrorAt(lean_object* v_00_u03b1_416_, lean_object* v_ref_417_, lean_object* v_msg_418_, lean_object* v_es_419_){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_420_ = lean_box(0);
v___x_421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_421_, 0, v_ref_417_);
lean_ctor_set(v___x_421_, 1, v_msg_418_);
v___x_422_ = lean_array_push(v_es_419_, v___x_421_);
v___x_423_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_423_, 0, v___x_420_);
lean_ctor_set(v___x_423_, 1, v___x_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___redArg___lam__0(lean_object* v_dec_425_, lean_object* v_x1_426_, lean_object* v_x2_427_, lean_object* v___y_428_){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_429_ = lean_apply_1(v_dec_425_, v_x2_427_);
v___x_430_ = ((lean_object*)(l_Lake_Toml_decodeArray___redArg___lam__0___closed__0));
v___x_431_ = l_Lake_Toml_mergeErrors___redArg(v_x1_426_, v___x_429_, v___x_430_, v___y_428_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___redArg(lean_object* v_dec_451_, lean_object* v_vs_452_, lean_object* v_a_453_){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; uint8_t v___x_458_; 
v___x_454_ = lean_array_get_size(v_vs_452_);
v___x_455_ = lean_mk_empty_array_with_capacity(v___x_454_);
v___x_456_ = lean_unsigned_to_nat(0u);
v___x_457_ = ((lean_object*)(l_Lake_Toml_decodeArray___redArg___closed__9));
v___x_458_ = lean_nat_dec_lt(v___x_456_, v___x_454_);
if (v___x_458_ == 0)
{
lean_object* v___x_459_; 
lean_dec_ref(v_vs_452_);
lean_dec_ref(v_dec_451_);
v___x_459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_459_, 0, v___x_455_);
lean_ctor_set(v___x_459_, 1, v_a_453_);
return v___x_459_;
}
else
{
lean_object* v___f_460_; lean_object* v___x_461_; uint8_t v___x_462_; 
v___f_460_ = lean_alloc_closure((void*)(l_Lake_Toml_decodeArray___redArg___lam__0), 4, 1);
lean_closure_set(v___f_460_, 0, v_dec_451_);
lean_inc_ref(v___x_455_);
v___x_461_ = lean_alloc_closure((void*)(l_EStateM_pure), 5, 4);
lean_closure_set(v___x_461_, 0, lean_box(0));
lean_closure_set(v___x_461_, 1, lean_box(0));
lean_closure_set(v___x_461_, 2, lean_box(0));
lean_closure_set(v___x_461_, 3, v___x_455_);
v___x_462_ = lean_nat_dec_le(v___x_454_, v___x_454_);
if (v___x_462_ == 0)
{
if (v___x_458_ == 0)
{
lean_object* v___x_463_; 
lean_dec_ref(v___x_461_);
lean_dec_ref(v___f_460_);
lean_dec_ref(v_vs_452_);
v___x_463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_463_, 0, v___x_455_);
lean_ctor_set(v___x_463_, 1, v_a_453_);
return v___x_463_;
}
else
{
size_t v___x_464_; size_t v___x_465_; lean_object* v___x_133__overap_466_; lean_object* v___x_467_; 
lean_dec_ref(v___x_455_);
v___x_464_ = ((size_t)0ULL);
v___x_465_ = lean_usize_of_nat(v___x_454_);
v___x_133__overap_466_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_457_, v___f_460_, v_vs_452_, v___x_464_, v___x_465_, v___x_461_);
v___x_467_ = lean_apply_1(v___x_133__overap_466_, v_a_453_);
return v___x_467_;
}
}
else
{
size_t v___x_468_; size_t v___x_469_; lean_object* v___x_138__overap_470_; lean_object* v___x_471_; 
lean_dec_ref(v___x_455_);
v___x_468_ = ((size_t)0ULL);
v___x_469_ = lean_usize_of_nat(v___x_454_);
v___x_138__overap_470_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_457_, v___f_460_, v_vs_452_, v___x_468_, v___x_469_, v___x_461_);
v___x_471_ = lean_apply_1(v___x_138__overap_470_, v_a_453_);
return v___x_471_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray(lean_object* v_00_u03b1_472_, lean_object* v_dec_473_, lean_object* v_vs_474_, lean_object* v_a_475_){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = l_Lake_Toml_decodeArray___redArg(v_dec_473_, v_vs_474_, v_a_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_decodeString(lean_object* v_v_480_, lean_object* v_a_481_){
_start:
{
lean_object* v___y_483_; 
if (lean_obj_tag(v_v_480_) == 0)
{
lean_object* v_s_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_496_; 
v_s_489_ = lean_ctor_get(v_v_480_, 1);
v_isSharedCheck_496_ = !lean_is_exclusive(v_v_480_);
if (v_isSharedCheck_496_ == 0)
{
lean_object* v_unused_497_; 
v_unused_497_ = lean_ctor_get(v_v_480_, 0);
lean_dec(v_unused_497_);
v___x_491_ = v_v_480_;
v_isShared_492_ = v_isSharedCheck_496_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_s_489_);
lean_dec(v_v_480_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_496_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___x_494_; 
if (v_isShared_492_ == 0)
{
lean_ctor_set(v___x_491_, 1, v_a_481_);
lean_ctor_set(v___x_491_, 0, v_s_489_);
v___x_494_ = v___x_491_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_s_489_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v_a_481_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
else
{
lean_object* v_ref_498_; 
v_ref_498_ = lean_ctor_get(v_v_480_, 0);
lean_inc(v_ref_498_);
lean_dec_ref(v_v_480_);
v___y_483_ = v_ref_498_;
goto v___jp_482_;
}
v___jp_482_:
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_484_ = ((lean_object*)(l_Lake_Toml_Value_decodeString___closed__0));
v___x_485_ = lean_box(0);
v___x_486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_486_, 0, v___y_483_);
lean_ctor_set(v___x_486_, 1, v___x_484_);
v___x_487_ = lean_array_push(v_a_481_, v___x_486_);
v___x_488_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_488_, 0, v___x_485_);
lean_ctor_set(v___x_488_, 1, v___x_487_);
return v___x_488_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_instDecodeTomlFilePath___lam__0(lean_object* v_x_501_, lean_object* v___y_502_){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = l_Lake_Toml_Value_decodeString(v_x_501_, v___y_502_);
if (lean_obj_tag(v___x_503_) == 0)
{
lean_object* v_a_504_; lean_object* v_a_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_512_; 
v_a_504_ = lean_ctor_get(v___x_503_, 0);
v_a_505_ = lean_ctor_get(v___x_503_, 1);
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_512_ == 0)
{
v___x_507_ = v___x_503_;
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_a_505_);
lean_inc(v_a_504_);
lean_dec(v___x_503_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_510_; 
if (v_isShared_508_ == 0)
{
v___x_510_ = v___x_507_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_a_504_);
lean_ctor_set(v_reuseFailAlloc_511_, 1, v_a_505_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
else
{
lean_object* v_a_513_; lean_object* v_a_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_521_; 
v_a_513_ = lean_ctor_get(v___x_503_, 0);
v_a_514_ = lean_ctor_get(v___x_503_, 1);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_521_ == 0)
{
v___x_516_ = v___x_503_;
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_a_514_);
lean_inc(v_a_513_);
lean_dec(v___x_503_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_519_; 
if (v_isShared_517_ == 0)
{
v___x_519_ = v___x_516_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v_a_513_);
lean_ctor_set(v_reuseFailAlloc_520_, 1, v_a_514_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_decodeName(lean_object* v_v_525_, lean_object* v_a_526_){
_start:
{
lean_object* v___x_527_; 
lean_inc_ref(v_v_525_);
v___x_527_ = l_Lake_Toml_Value_decodeString(v_v_525_, v_a_526_);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_object* v_a_528_; lean_object* v_a_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_545_; 
v_a_528_ = lean_ctor_get(v___x_527_, 0);
v_a_529_ = lean_ctor_get(v___x_527_, 1);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_545_ == 0)
{
v___x_531_ = v___x_527_;
v_isShared_532_ = v_isSharedCheck_545_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_a_529_);
lean_inc(v_a_528_);
lean_dec(v___x_527_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_545_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___y_534_; lean_object* v___x_542_; 
v___x_542_ = l_String_toName(v_a_528_);
if (lean_obj_tag(v___x_542_) == 0)
{
lean_object* v_ref_543_; 
v_ref_543_ = lean_ctor_get(v_v_525_, 0);
lean_inc(v_ref_543_);
lean_dec_ref(v_v_525_);
v___y_534_ = v_ref_543_;
goto v___jp_533_;
}
else
{
lean_object* v___x_544_; 
lean_del_object(v___x_531_);
lean_dec_ref(v_v_525_);
v___x_544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_544_, 0, v___x_542_);
lean_ctor_set(v___x_544_, 1, v_a_529_);
return v___x_544_;
}
v___jp_533_:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_540_; 
v___x_535_ = ((lean_object*)(l_Lake_Toml_Value_decodeName___closed__0));
v___x_536_ = lean_box(0);
v___x_537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_537_, 0, v___y_534_);
lean_ctor_set(v___x_537_, 1, v___x_535_);
v___x_538_ = lean_array_push(v_a_529_, v___x_537_);
if (v_isShared_532_ == 0)
{
lean_ctor_set_tag(v___x_531_, 1);
lean_ctor_set(v___x_531_, 1, v___x_538_);
lean_ctor_set(v___x_531_, 0, v___x_536_);
v___x_540_ = v___x_531_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v___x_536_);
lean_ctor_set(v_reuseFailAlloc_541_, 1, v___x_538_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
}
else
{
lean_object* v_a_546_; lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_554_; 
lean_dec_ref(v_v_525_);
v_a_546_ = lean_ctor_get(v___x_527_, 0);
v_a_547_ = lean_ctor_get(v___x_527_, 1);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_554_ == 0)
{
v___x_549_ = v___x_527_;
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_inc(v_a_546_);
lean_dec(v___x_527_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_a_546_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v_a_547_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_decodeInt(lean_object* v_v_558_, lean_object* v_a_559_){
_start:
{
lean_object* v___y_561_; 
if (lean_obj_tag(v_v_558_) == 1)
{
lean_object* v_n_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_574_; 
v_n_567_ = lean_ctor_get(v_v_558_, 1);
v_isSharedCheck_574_ = !lean_is_exclusive(v_v_558_);
if (v_isSharedCheck_574_ == 0)
{
lean_object* v_unused_575_; 
v_unused_575_ = lean_ctor_get(v_v_558_, 0);
lean_dec(v_unused_575_);
v___x_569_ = v_v_558_;
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_n_567_);
lean_dec(v_v_558_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_572_; 
if (v_isShared_570_ == 0)
{
lean_ctor_set_tag(v___x_569_, 0);
lean_ctor_set(v___x_569_, 1, v_a_559_);
lean_ctor_set(v___x_569_, 0, v_n_567_);
v___x_572_ = v___x_569_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_n_567_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v_a_559_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
else
{
lean_object* v_ref_576_; 
v_ref_576_ = lean_ctor_get(v_v_558_, 0);
lean_inc(v_ref_576_);
lean_dec_ref(v_v_558_);
v___y_561_ = v_ref_576_;
goto v___jp_560_;
}
v___jp_560_:
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_562_ = ((lean_object*)(l_Lake_Toml_Value_decodeInt___closed__0));
v___x_563_ = lean_box(0);
v___x_564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_564_, 0, v___y_561_);
lean_ctor_set(v___x_564_, 1, v___x_562_);
v___x_565_ = lean_array_push(v_a_559_, v___x_564_);
v___x_566_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_566_, 0, v___x_563_);
lean_ctor_set(v___x_566_, 1, v___x_565_);
return v___x_566_;
}
}
}
static lean_object* _init_l_Lake_Toml_Value_decodeNat___closed__1(void){
_start:
{
lean_object* v_natZero_580_; lean_object* v_intZero_581_; 
v_natZero_580_ = lean_unsigned_to_nat(0u);
v_intZero_581_ = lean_nat_to_int(v_natZero_580_);
return v_intZero_581_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_decodeNat(lean_object* v_x_582_, lean_object* v_a_583_){
_start:
{
lean_object* v___y_585_; lean_object* v___y_586_; 
if (lean_obj_tag(v_x_582_) == 1)
{
lean_object* v_ref_592_; lean_object* v_n_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_603_; 
v_ref_592_ = lean_ctor_get(v_x_582_, 0);
v_n_593_ = lean_ctor_get(v_x_582_, 1);
v_isSharedCheck_603_ = !lean_is_exclusive(v_x_582_);
if (v_isSharedCheck_603_ == 0)
{
v___x_595_ = v_x_582_;
v_isShared_596_ = v_isSharedCheck_603_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_n_593_);
lean_inc(v_ref_592_);
lean_dec(v_x_582_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_603_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v_intZero_597_; uint8_t v_isNeg_598_; 
v_intZero_597_ = lean_obj_once(&l_Lake_Toml_Value_decodeNat___closed__1, &l_Lake_Toml_Value_decodeNat___closed__1_once, _init_l_Lake_Toml_Value_decodeNat___closed__1);
v_isNeg_598_ = lean_int_dec_lt(v_n_593_, v_intZero_597_);
if (v_isNeg_598_ == 0)
{
lean_object* v_a_599_; lean_object* v___x_601_; 
lean_dec(v_ref_592_);
v_a_599_ = lean_nat_abs(v_n_593_);
lean_dec(v_n_593_);
if (v_isShared_596_ == 0)
{
lean_ctor_set_tag(v___x_595_, 0);
lean_ctor_set(v___x_595_, 1, v_a_583_);
lean_ctor_set(v___x_595_, 0, v_a_599_);
v___x_601_ = v___x_595_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_a_599_);
lean_ctor_set(v_reuseFailAlloc_602_, 1, v_a_583_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
else
{
lean_del_object(v___x_595_);
lean_dec(v_n_593_);
v___y_585_ = v_a_583_;
v___y_586_ = v_ref_592_;
goto v___jp_584_;
}
}
}
else
{
lean_object* v_ref_604_; 
v_ref_604_ = lean_ctor_get(v_x_582_, 0);
lean_inc(v_ref_604_);
lean_dec_ref(v_x_582_);
v___y_585_ = v_a_583_;
v___y_586_ = v_ref_604_;
goto v___jp_584_;
}
v___jp_584_:
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_587_ = ((lean_object*)(l_Lake_Toml_Value_decodeNat___closed__0));
v___x_588_ = lean_box(0);
v___x_589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_589_, 0, v___y_586_);
lean_ctor_set(v___x_589_, 1, v___x_587_);
v___x_590_ = lean_array_push(v___y_585_, v___x_589_);
v___x_591_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_591_, 0, v___x_588_);
lean_ctor_set(v___x_591_, 1, v___x_590_);
return v___x_591_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_decodeFloat(lean_object* v_v_608_, lean_object* v_a_609_){
_start:
{
lean_object* v___y_611_; 
if (lean_obj_tag(v_v_608_) == 2)
{
double v_n_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
v_n_617_ = lean_ctor_get_float(v_v_608_, sizeof(void*)*1);
lean_dec_ref_known(v_v_608_, 1);
v___x_618_ = lean_box_float(v_n_617_);
v___x_619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_619_, 0, v___x_618_);
lean_ctor_set(v___x_619_, 1, v_a_609_);
return v___x_619_;
}
else
{
lean_object* v_ref_620_; 
v_ref_620_ = lean_ctor_get(v_v_608_, 0);
lean_inc(v_ref_620_);
lean_dec_ref(v_v_608_);
v___y_611_ = v_ref_620_;
goto v___jp_610_;
}
v___jp_610_:
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_612_ = ((lean_object*)(l_Lake_Toml_Value_decodeFloat___closed__0));
v___x_613_ = lean_box(0);
v___x_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_614_, 0, v___y_611_);
lean_ctor_set(v___x_614_, 1, v___x_612_);
v___x_615_ = lean_array_push(v_a_609_, v___x_614_);
v___x_616_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_616_, 0, v___x_613_);
lean_ctor_set(v___x_616_, 1, v___x_615_);
return v___x_616_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_decodeBool(lean_object* v_v_624_, lean_object* v_a_625_){
_start:
{
lean_object* v___y_627_; 
if (lean_obj_tag(v_v_624_) == 3)
{
uint8_t v_b_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v_b_633_ = lean_ctor_get_uint8(v_v_624_, sizeof(void*)*1);
lean_dec_ref_known(v_v_624_, 1);
v___x_634_ = lean_box(v_b_633_);
v___x_635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
lean_ctor_set(v___x_635_, 1, v_a_625_);
return v___x_635_;
}
else
{
lean_object* v_ref_636_; 
v_ref_636_ = lean_ctor_get(v_v_624_, 0);
lean_inc(v_ref_636_);
lean_dec_ref(v_v_624_);
v___y_627_ = v_ref_636_;
goto v___jp_626_;
}
v___jp_626_:
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_628_ = ((lean_object*)(l_Lake_Toml_Value_decodeBool___closed__0));
v___x_629_ = lean_box(0);
v___x_630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_630_, 0, v___y_627_);
lean_ctor_set(v___x_630_, 1, v___x_628_);
v___x_631_ = lean_array_push(v_a_625_, v___x_630_);
v___x_632_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_632_, 0, v___x_629_);
lean_ctor_set(v___x_632_, 1, v___x_631_);
return v___x_632_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_decodeDateTime(lean_object* v_v_640_, lean_object* v_a_641_){
_start:
{
lean_object* v___y_643_; 
if (lean_obj_tag(v_v_640_) == 4)
{
lean_object* v_dt_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_656_; 
v_dt_649_ = lean_ctor_get(v_v_640_, 1);
v_isSharedCheck_656_ = !lean_is_exclusive(v_v_640_);
if (v_isSharedCheck_656_ == 0)
{
lean_object* v_unused_657_; 
v_unused_657_ = lean_ctor_get(v_v_640_, 0);
lean_dec(v_unused_657_);
v___x_651_ = v_v_640_;
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_dt_649_);
lean_dec(v_v_640_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_654_; 
if (v_isShared_652_ == 0)
{
lean_ctor_set_tag(v___x_651_, 0);
lean_ctor_set(v___x_651_, 1, v_a_641_);
lean_ctor_set(v___x_651_, 0, v_dt_649_);
v___x_654_ = v___x_651_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_dt_649_);
lean_ctor_set(v_reuseFailAlloc_655_, 1, v_a_641_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
}
else
{
lean_object* v_ref_658_; 
v_ref_658_ = lean_ctor_get(v_v_640_, 0);
lean_inc(v_ref_658_);
lean_dec_ref(v_v_640_);
v___y_643_ = v_ref_658_;
goto v___jp_642_;
}
v___jp_642_:
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_644_ = ((lean_object*)(l_Lake_Toml_Value_decodeDateTime___closed__0));
v___x_645_ = lean_box(0);
v___x_646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_646_, 0, v___y_643_);
lean_ctor_set(v___x_646_, 1, v___x_644_);
v___x_647_ = lean_array_push(v_a_641_, v___x_646_);
v___x_648_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_648_, 0, v___x_645_);
lean_ctor_set(v___x_648_, 1, v___x_647_);
return v___x_648_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_decodeValueArray(lean_object* v_v_662_, lean_object* v_a_663_){
_start:
{
lean_object* v___y_665_; 
if (lean_obj_tag(v_v_662_) == 5)
{
lean_object* v_xs_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_678_; 
v_xs_671_ = lean_ctor_get(v_v_662_, 1);
v_isSharedCheck_678_ = !lean_is_exclusive(v_v_662_);
if (v_isSharedCheck_678_ == 0)
{
lean_object* v_unused_679_; 
v_unused_679_ = lean_ctor_get(v_v_662_, 0);
lean_dec(v_unused_679_);
v___x_673_ = v_v_662_;
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_xs_671_);
lean_dec(v_v_662_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_676_; 
if (v_isShared_674_ == 0)
{
lean_ctor_set_tag(v___x_673_, 0);
lean_ctor_set(v___x_673_, 1, v_a_663_);
lean_ctor_set(v___x_673_, 0, v_xs_671_);
v___x_676_ = v___x_673_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_xs_671_);
lean_ctor_set(v_reuseFailAlloc_677_, 1, v_a_663_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
else
{
lean_object* v_ref_680_; 
v_ref_680_ = lean_ctor_get(v_v_662_, 0);
lean_inc(v_ref_680_);
lean_dec_ref(v_v_662_);
v___y_665_ = v_ref_680_;
goto v___jp_664_;
}
v___jp_664_:
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_666_ = ((lean_object*)(l_Lake_Toml_Value_decodeValueArray___closed__0));
v___x_667_ = lean_box(0);
v___x_668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_668_, 0, v___y_665_);
lean_ctor_set(v___x_668_, 1, v___x_666_);
v___x_669_ = lean_array_push(v_a_663_, v___x_668_);
v___x_670_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_670_, 0, v___x_667_);
lean_ctor_set(v___x_670_, 1, v___x_669_);
return v___x_670_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_decodeArray___redArg(lean_object* v_dec_681_, lean_object* v_v_682_, lean_object* v_a_683_){
_start:
{
lean_object* v___x_684_; 
v___x_684_ = l_Lake_Toml_Value_decodeValueArray(v_v_682_, v_a_683_);
if (lean_obj_tag(v___x_684_) == 0)
{
lean_object* v_a_685_; lean_object* v_a_686_; lean_object* v___x_687_; 
v_a_685_ = lean_ctor_get(v___x_684_, 0);
lean_inc(v_a_685_);
v_a_686_ = lean_ctor_get(v___x_684_, 1);
lean_inc(v_a_686_);
lean_dec_ref_known(v___x_684_, 2);
v___x_687_ = l_Lake_Toml_decodeArray___redArg(v_dec_681_, v_a_685_, v_a_686_);
return v___x_687_;
}
else
{
lean_object* v_a_688_; lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_696_; 
lean_dec_ref(v_dec_681_);
v_a_688_ = lean_ctor_get(v___x_684_, 0);
v_a_689_ = lean_ctor_get(v___x_684_, 1);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_696_ == 0)
{
v___x_691_ = v___x_684_;
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_inc(v_a_688_);
lean_dec(v___x_684_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_694_; 
if (v_isShared_692_ == 0)
{
v___x_694_ = v___x_691_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_a_688_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v_a_689_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_decodeArray(lean_object* v_00_u03b1_697_, lean_object* v_dec_698_, lean_object* v_v_699_, lean_object* v_a_700_){
_start:
{
lean_object* v___x_701_; 
v___x_701_ = l_Lake_Toml_Value_decodeValueArray(v_v_699_, v_a_700_);
if (lean_obj_tag(v___x_701_) == 0)
{
lean_object* v_a_702_; lean_object* v_a_703_; lean_object* v___x_704_; 
v_a_702_ = lean_ctor_get(v___x_701_, 0);
lean_inc(v_a_702_);
v_a_703_ = lean_ctor_get(v___x_701_, 1);
lean_inc(v_a_703_);
lean_dec_ref_known(v___x_701_, 2);
v___x_704_ = l_Lake_Toml_decodeArray___redArg(v_dec_698_, v_a_702_, v_a_703_);
return v___x_704_;
}
else
{
lean_object* v_a_705_; lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_713_; 
lean_dec_ref(v_dec_698_);
v_a_705_ = lean_ctor_get(v___x_701_, 0);
v_a_706_ = lean_ctor_get(v___x_701_, 1);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_713_ == 0)
{
v___x_708_ = v___x_701_;
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_inc(v_a_705_);
lean_dec(v___x_701_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_711_; 
if (v_isShared_709_ == 0)
{
v___x_711_ = v___x_708_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_a_705_);
lean_ctor_set(v_reuseFailAlloc_712_, 1, v_a_706_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_instDecodeTomlArray___redArg(lean_object* v_inst_714_){
_start:
{
lean_object* v___x_715_; 
v___x_715_ = lean_alloc_closure((void*)(l_Lake_Toml_Value_decodeArray), 4, 2);
lean_closure_set(v___x_715_, 0, lean_box(0));
lean_closure_set(v___x_715_, 1, v_inst_714_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_instDecodeTomlArray(lean_object* v_00_u03b1_716_, lean_object* v_inst_717_){
_start:
{
lean_object* v___x_718_; 
v___x_718_ = lean_alloc_closure((void*)(l_Lake_Toml_Value_decodeArray), 4, 2);
lean_closure_set(v___x_718_, 0, lean_box(0));
lean_closure_set(v___x_718_, 1, v_inst_717_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_decodeArrayOrSingleton___redArg(lean_object* v_dec_719_, lean_object* v_v_720_, lean_object* v_a_721_){
_start:
{
if (lean_obj_tag(v_v_720_) == 5)
{
lean_object* v_xs_722_; lean_object* v___x_723_; 
v_xs_722_ = lean_ctor_get(v_v_720_, 1);
lean_inc_ref(v_xs_722_);
lean_dec_ref_known(v_v_720_, 2);
v___x_723_ = l_Lake_Toml_decodeArray___redArg(v_dec_719_, v_xs_722_, v_a_721_);
return v___x_723_;
}
else
{
lean_object* v___x_724_; 
v___x_724_ = lean_apply_2(v_dec_719_, v_v_720_, v_a_721_);
if (lean_obj_tag(v___x_724_) == 0)
{
lean_object* v_a_725_; lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_736_; 
v_a_725_ = lean_ctor_get(v___x_724_, 0);
v_a_726_ = lean_ctor_get(v___x_724_, 1);
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_736_ == 0)
{
v___x_728_ = v___x_724_;
v_isShared_729_ = v_isSharedCheck_736_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_inc(v_a_725_);
lean_dec(v___x_724_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_736_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_734_; 
v___x_730_ = lean_unsigned_to_nat(1u);
v___x_731_ = lean_mk_empty_array_with_capacity(v___x_730_);
v___x_732_ = lean_array_push(v___x_731_, v_a_725_);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 0, v___x_732_);
v___x_734_ = v___x_728_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v___x_732_);
lean_ctor_set(v_reuseFailAlloc_735_, 1, v_a_726_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
}
else
{
lean_object* v_a_737_; lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_745_; 
v_a_737_ = lean_ctor_get(v___x_724_, 0);
v_a_738_ = lean_ctor_get(v___x_724_, 1);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_745_ == 0)
{
v___x_740_ = v___x_724_;
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_inc(v_a_737_);
lean_dec(v___x_724_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
if (v_isShared_741_ == 0)
{
v___x_743_ = v___x_740_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_a_737_);
lean_ctor_set(v_reuseFailAlloc_744_, 1, v_a_738_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_decodeArrayOrSingleton(lean_object* v_00_u03b1_746_, lean_object* v_dec_747_, lean_object* v_v_748_, lean_object* v_a_749_){
_start:
{
if (lean_obj_tag(v_v_748_) == 5)
{
lean_object* v_xs_750_; lean_object* v___x_751_; 
v_xs_750_ = lean_ctor_get(v_v_748_, 1);
lean_inc_ref(v_xs_750_);
lean_dec_ref_known(v_v_748_, 2);
v___x_751_ = l_Lake_Toml_decodeArray___redArg(v_dec_747_, v_xs_750_, v_a_749_);
return v___x_751_;
}
else
{
lean_object* v___x_752_; 
v___x_752_ = lean_apply_2(v_dec_747_, v_v_748_, v_a_749_);
if (lean_obj_tag(v___x_752_) == 0)
{
lean_object* v_a_753_; lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_764_; 
v_a_753_ = lean_ctor_get(v___x_752_, 0);
v_a_754_ = lean_ctor_get(v___x_752_, 1);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_752_);
if (v_isSharedCheck_764_ == 0)
{
v___x_756_ = v___x_752_;
v_isShared_757_ = v_isSharedCheck_764_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_inc(v_a_753_);
lean_dec(v___x_752_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_764_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_762_; 
v___x_758_ = lean_unsigned_to_nat(1u);
v___x_759_ = lean_mk_empty_array_with_capacity(v___x_758_);
v___x_760_ = lean_array_push(v___x_759_, v_a_753_);
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 0, v___x_760_);
v___x_762_ = v___x_756_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_760_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v_a_754_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
else
{
lean_object* v_a_765_; lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_773_; 
v_a_765_ = lean_ctor_get(v___x_752_, 0);
v_a_766_ = lean_ctor_get(v___x_752_, 1);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_752_);
if (v_isSharedCheck_773_ == 0)
{
v___x_768_ = v___x_752_;
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_inc(v_a_765_);
lean_dec(v___x_752_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_771_; 
if (v_isShared_769_ == 0)
{
v___x_771_ = v___x_768_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_a_765_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v_a_766_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_decodeTable(lean_object* v_v_775_, lean_object* v_a_776_){
_start:
{
lean_object* v___y_778_; 
if (lean_obj_tag(v_v_775_) == 6)
{
lean_object* v_xs_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_791_; 
v_xs_784_ = lean_ctor_get(v_v_775_, 1);
v_isSharedCheck_791_ = !lean_is_exclusive(v_v_775_);
if (v_isSharedCheck_791_ == 0)
{
lean_object* v_unused_792_; 
v_unused_792_ = lean_ctor_get(v_v_775_, 0);
lean_dec(v_unused_792_);
v___x_786_ = v_v_775_;
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_xs_784_);
lean_dec(v_v_775_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_789_; 
if (v_isShared_787_ == 0)
{
lean_ctor_set_tag(v___x_786_, 0);
lean_ctor_set(v___x_786_, 1, v_a_776_);
lean_ctor_set(v___x_786_, 0, v_xs_784_);
v___x_789_ = v___x_786_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_xs_784_);
lean_ctor_set(v_reuseFailAlloc_790_, 1, v_a_776_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
else
{
lean_object* v_ref_793_; 
v_ref_793_ = lean_ctor_get(v_v_775_, 0);
lean_inc(v_ref_793_);
lean_dec_ref(v_v_775_);
v___y_778_ = v_ref_793_;
goto v___jp_777_;
}
v___jp_777_:
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_779_ = ((lean_object*)(l_Lake_Toml_Value_decodeTable___closed__0));
v___x_780_ = lean_box(0);
v___x_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_781_, 0, v___y_778_);
lean_ctor_set(v___x_781_, 1, v___x_779_);
v___x_782_ = lean_array_push(v_a_776_, v___x_781_);
v___x_783_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_783_, 0, v___x_780_);
lean_ctor_set(v___x_783_, 1, v___x_782_);
return v___x_783_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_decodeKeyval___redArg___lam__0(lean_object* v_iniPos_798_, lean_object* v_k_799_, lean_object* v_i_800_, lean_object* v_a_801_, lean_object* v_x_802_){
_start:
{
uint8_t v___x_803_; 
v___x_803_ = lean_nat_dec_le(v_iniPos_798_, v_i_800_);
if (v___x_803_ == 0)
{
lean_dec(v_k_799_);
return v_a_801_;
}
else
{
lean_object* v_ref_804_; lean_object* v_msg_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_818_; 
v_ref_804_ = lean_ctor_get(v_a_801_, 0);
v_msg_805_ = lean_ctor_get(v_a_801_, 1);
v_isSharedCheck_818_ = !lean_is_exclusive(v_a_801_);
if (v_isSharedCheck_818_ == 0)
{
v___x_807_ = v_a_801_;
v_isShared_808_ = v_isSharedCheck_818_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_msg_805_);
lean_inc(v_ref_804_);
lean_dec(v_a_801_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_818_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_816_; 
v___x_809_ = ((lean_object*)(l_Lake_Toml_decodeKeyval___redArg___lam__0___closed__0));
v___x_810_ = l_Lake_Toml_ppKey(v_k_799_);
v___x_811_ = lean_string_append(v___x_809_, v___x_810_);
lean_dec_ref(v___x_810_);
v___x_812_ = ((lean_object*)(l_Lake_Toml_decodeKeyval___redArg___lam__0___closed__1));
v___x_813_ = lean_string_append(v___x_811_, v___x_812_);
v___x_814_ = lean_string_append(v___x_813_, v_msg_805_);
lean_dec_ref(v_msg_805_);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 1, v___x_814_);
v___x_816_ = v___x_807_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_ref_804_);
lean_ctor_set(v_reuseFailAlloc_817_, 1, v___x_814_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_decodeKeyval___redArg___lam__0___boxed(lean_object* v_iniPos_819_, lean_object* v_k_820_, lean_object* v_i_821_, lean_object* v_a_822_, lean_object* v_x_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_Lake_Toml_decodeKeyval___redArg___lam__0(v_iniPos_819_, v_k_820_, v_i_821_, v_a_822_, v_x_823_);
lean_dec(v_i_821_);
lean_dec(v_iniPos_819_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_decodeKeyval___redArg___lam__1(lean_object* v___f_825_, lean_object* v_es_826_){
_start:
{
lean_object* v___x_827_; size_t v_sz_828_; size_t v___x_829_; lean_object* v___x_830_; 
v___x_827_ = ((lean_object*)(l_Lake_Toml_decodeArray___redArg___closed__9));
v_sz_828_ = lean_array_size(v_es_826_);
v___x_829_ = ((size_t)0ULL);
lean_inc_ref(v_es_826_);
v___x_830_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_827_, v_es_826_, v___f_825_, v_sz_828_, v___x_829_, v_es_826_);
lean_dec_ref(v_es_826_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_decodeKeyval___redArg(lean_object* v_dec_831_, lean_object* v_k_832_, lean_object* v_v_833_, lean_object* v_es_834_){
_start:
{
lean_object* v_iniPos_835_; lean_object* v___f_836_; lean_object* v___x_837_; 
v_iniPos_835_ = lean_array_get_size(v_es_834_);
v___f_836_ = lean_alloc_closure((void*)(l_Lake_Toml_decodeKeyval___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_836_, 0, v_iniPos_835_);
lean_closure_set(v___f_836_, 1, v_k_832_);
v___x_837_ = lean_apply_2(v_dec_831_, v_v_833_, v_es_834_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v_a_838_; lean_object* v_a_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_847_; 
v_a_838_ = lean_ctor_get(v___x_837_, 0);
v_a_839_ = lean_ctor_get(v___x_837_, 1);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_847_ == 0)
{
v___x_841_ = v___x_837_;
v_isShared_842_ = v_isSharedCheck_847_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_a_839_);
lean_inc(v_a_838_);
lean_dec(v___x_837_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_847_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_843_; lean_object* v___x_845_; 
v___x_843_ = l_Lake_Toml_decodeKeyval___redArg___lam__1(v___f_836_, v_a_839_);
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 1, v___x_843_);
v___x_845_ = v___x_841_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_a_838_);
lean_ctor_set(v_reuseFailAlloc_846_, 1, v___x_843_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
else
{
lean_object* v_a_848_; lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_857_; 
v_a_848_ = lean_ctor_get(v___x_837_, 0);
v_a_849_ = lean_ctor_get(v___x_837_, 1);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_857_ == 0)
{
v___x_851_ = v___x_837_;
v_isShared_852_ = v_isSharedCheck_857_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_inc(v_a_848_);
lean_dec(v___x_837_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_857_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_853_; lean_object* v___x_855_; 
v___x_853_ = l_Lake_Toml_decodeKeyval___redArg___lam__1(v___f_836_, v_a_849_);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 1, v___x_853_);
v___x_855_ = v___x_851_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_a_848_);
lean_ctor_set(v_reuseFailAlloc_856_, 1, v___x_853_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_decodeKeyval(lean_object* v_00_u03b1_858_, lean_object* v_dec_859_, lean_object* v_k_860_, lean_object* v_v_861_, lean_object* v_es_862_){
_start:
{
lean_object* v___x_863_; 
v___x_863_ = l_Lake_Toml_decodeKeyval___redArg(v_dec_859_, v_k_860_, v_v_861_, v_es_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decodeValue(lean_object* v_t_866_, lean_object* v_k_867_, lean_object* v_ref_868_, lean_object* v_a_869_){
_start:
{
lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_870_ = ((lean_object*)(l_Lake_Toml_Table_decodeValue___closed__0));
lean_inc(v_k_867_);
v___x_871_ = l_Lake_Toml_RBDict_findEntry_x3f___redArg(v___x_870_, v_k_867_, v_t_866_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_872_ = ((lean_object*)(l_Lake_Toml_Table_decodeValue___closed__1));
v___x_873_ = l_Lake_Toml_ppKey(v_k_867_);
v___x_874_ = lean_string_append(v___x_872_, v___x_873_);
lean_dec_ref(v___x_873_);
v___x_875_ = lean_box(0);
v___x_876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_876_, 0, v_ref_868_);
lean_ctor_set(v___x_876_, 1, v___x_874_);
v___x_877_ = lean_array_push(v_a_869_, v___x_876_);
v___x_878_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_878_, 0, v___x_875_);
lean_ctor_set(v___x_878_, 1, v___x_877_);
return v___x_878_;
}
else
{
lean_object* v_val_879_; lean_object* v_snd_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_887_; 
lean_dec(v_ref_868_);
lean_dec(v_k_867_);
v_val_879_ = lean_ctor_get(v___x_871_, 0);
lean_inc(v_val_879_);
lean_dec_ref_known(v___x_871_, 1);
v_snd_880_ = lean_ctor_get(v_val_879_, 1);
v_isSharedCheck_887_ = !lean_is_exclusive(v_val_879_);
if (v_isSharedCheck_887_ == 0)
{
lean_object* v_unused_888_; 
v_unused_888_ = lean_ctor_get(v_val_879_, 0);
lean_dec(v_unused_888_);
v___x_882_ = v_val_879_;
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_snd_880_);
lean_dec(v_val_879_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_885_; 
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 1, v_a_869_);
lean_ctor_set(v___x_882_, 0, v_snd_880_);
v___x_885_ = v___x_882_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_snd_880_);
lean_ctor_set(v_reuseFailAlloc_886_, 1, v_a_869_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decode___redArg(lean_object* v_dec_889_, lean_object* v_t_890_, lean_object* v_k_891_, lean_object* v_ref_892_, lean_object* v_a_893_){
_start:
{
lean_object* v___x_894_; 
lean_inc(v_k_891_);
v___x_894_ = l_Lake_Toml_Table_decodeValue(v_t_890_, v_k_891_, v_ref_892_, v_a_893_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v_a_895_; lean_object* v_a_896_; lean_object* v___x_897_; 
v_a_895_ = lean_ctor_get(v___x_894_, 0);
lean_inc(v_a_895_);
v_a_896_ = lean_ctor_get(v___x_894_, 1);
lean_inc(v_a_896_);
lean_dec_ref_known(v___x_894_, 2);
v___x_897_ = l_Lake_Toml_decodeKeyval___redArg(v_dec_889_, v_k_891_, v_a_895_, v_a_896_);
return v___x_897_;
}
else
{
lean_object* v_a_898_; lean_object* v_a_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_906_; 
lean_dec(v_k_891_);
lean_dec_ref(v_dec_889_);
v_a_898_ = lean_ctor_get(v___x_894_, 0);
v_a_899_ = lean_ctor_get(v___x_894_, 1);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_906_ == 0)
{
v___x_901_ = v___x_894_;
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_a_899_);
lean_inc(v_a_898_);
lean_dec(v___x_894_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_904_; 
if (v_isShared_902_ == 0)
{
v___x_904_ = v___x_901_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_a_898_);
lean_ctor_set(v_reuseFailAlloc_905_, 1, v_a_899_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decode(lean_object* v_00_u03b1_907_, lean_object* v_dec_908_, lean_object* v_t_909_, lean_object* v_k_910_, lean_object* v_ref_911_, lean_object* v_a_912_){
_start:
{
lean_object* v___x_913_; 
lean_inc(v_k_910_);
v___x_913_ = l_Lake_Toml_Table_decodeValue(v_t_909_, v_k_910_, v_ref_911_, v_a_912_);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v_a_914_; lean_object* v_a_915_; lean_object* v___x_916_; 
v_a_914_ = lean_ctor_get(v___x_913_, 0);
lean_inc(v_a_914_);
v_a_915_ = lean_ctor_get(v___x_913_, 1);
lean_inc(v_a_915_);
lean_dec_ref_known(v___x_913_, 2);
v___x_916_ = l_Lake_Toml_decodeKeyval___redArg(v_dec_908_, v_k_910_, v_a_914_, v_a_915_);
return v___x_916_;
}
else
{
lean_object* v_a_917_; lean_object* v_a_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_925_; 
lean_dec(v_k_910_);
lean_dec_ref(v_dec_908_);
v_a_917_ = lean_ctor_get(v___x_913_, 0);
v_a_918_ = lean_ctor_get(v___x_913_, 1);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_925_ == 0)
{
v___x_920_ = v___x_913_;
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_a_918_);
lean_inc(v_a_917_);
lean_dec(v___x_913_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___x_923_; 
if (v_isShared_921_ == 0)
{
v___x_923_ = v___x_920_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v_a_917_);
lean_ctor_set(v_reuseFailAlloc_924_, 1, v_a_918_);
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
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decode_x3f___redArg(lean_object* v_dec_926_, lean_object* v_t_927_, lean_object* v_k_928_, lean_object* v_a_929_){
_start:
{
lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_930_ = ((lean_object*)(l_Lake_Toml_Table_decodeValue___closed__0));
lean_inc(v_k_928_);
v___x_931_ = l_Lake_Toml_RBDict_findEntry_x3f___redArg(v___x_930_, v_k_928_, v_t_927_);
if (lean_obj_tag(v___x_931_) == 0)
{
lean_object* v___x_932_; lean_object* v___x_933_; 
lean_dec(v_k_928_);
lean_dec_ref(v_dec_926_);
v___x_932_ = lean_box(0);
v___x_933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_933_, 0, v___x_932_);
lean_ctor_set(v___x_933_, 1, v_a_929_);
return v___x_933_;
}
else
{
lean_object* v_val_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_961_; 
v_val_934_ = lean_ctor_get(v___x_931_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_931_);
if (v_isSharedCheck_961_ == 0)
{
v___x_936_ = v___x_931_;
v_isShared_937_ = v_isSharedCheck_961_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_val_934_);
lean_dec(v___x_931_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_961_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v_snd_938_; lean_object* v___x_939_; 
v_snd_938_ = lean_ctor_get(v_val_934_, 1);
lean_inc(v_snd_938_);
lean_dec(v_val_934_);
v___x_939_ = l_Lake_Toml_decodeKeyval___redArg(v_dec_926_, v_k_928_, v_snd_938_, v_a_929_);
if (lean_obj_tag(v___x_939_) == 0)
{
lean_object* v_a_940_; lean_object* v_a_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_951_; 
v_a_940_ = lean_ctor_get(v___x_939_, 0);
v_a_941_ = lean_ctor_get(v___x_939_, 1);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_939_);
if (v_isSharedCheck_951_ == 0)
{
v___x_943_ = v___x_939_;
v_isShared_944_ = v_isSharedCheck_951_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_inc(v_a_940_);
lean_dec(v___x_939_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_951_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_946_; 
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 0, v_a_940_);
v___x_946_ = v___x_936_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_a_940_);
v___x_946_ = v_reuseFailAlloc_950_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
lean_object* v___x_948_; 
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 0, v___x_946_);
v___x_948_ = v___x_943_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v___x_946_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v_a_941_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
}
else
{
lean_object* v_a_952_; lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_960_; 
lean_del_object(v___x_936_);
v_a_952_ = lean_ctor_get(v___x_939_, 0);
v_a_953_ = lean_ctor_get(v___x_939_, 1);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_939_);
if (v_isSharedCheck_960_ == 0)
{
v___x_955_ = v___x_939_;
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_inc(v_a_952_);
lean_dec(v___x_939_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_958_; 
if (v_isShared_956_ == 0)
{
v___x_958_ = v___x_955_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_a_952_);
lean_ctor_set(v_reuseFailAlloc_959_, 1, v_a_953_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decode_x3f(lean_object* v_00_u03b1_962_, lean_object* v_dec_963_, lean_object* v_t_964_, lean_object* v_k_965_, lean_object* v_a_966_){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_967_ = ((lean_object*)(l_Lake_Toml_Table_decodeValue___closed__0));
lean_inc(v_k_965_);
v___x_968_ = l_Lake_Toml_RBDict_findEntry_x3f___redArg(v___x_967_, v_k_965_, v_t_964_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_object* v___x_969_; lean_object* v___x_970_; 
lean_dec(v_k_965_);
lean_dec_ref(v_dec_963_);
v___x_969_ = lean_box(0);
v___x_970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_970_, 0, v___x_969_);
lean_ctor_set(v___x_970_, 1, v_a_966_);
return v___x_970_;
}
else
{
lean_object* v_val_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_998_; 
v_val_971_ = lean_ctor_get(v___x_968_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_998_ == 0)
{
v___x_973_ = v___x_968_;
v_isShared_974_ = v_isSharedCheck_998_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_val_971_);
lean_dec(v___x_968_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_998_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v_snd_975_; lean_object* v___x_976_; 
v_snd_975_ = lean_ctor_get(v_val_971_, 1);
lean_inc(v_snd_975_);
lean_dec(v_val_971_);
v___x_976_ = l_Lake_Toml_decodeKeyval___redArg(v_dec_963_, v_k_965_, v_snd_975_, v_a_966_);
if (lean_obj_tag(v___x_976_) == 0)
{
lean_object* v_a_977_; lean_object* v_a_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_988_; 
v_a_977_ = lean_ctor_get(v___x_976_, 0);
v_a_978_ = lean_ctor_get(v___x_976_, 1);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_988_ == 0)
{
v___x_980_ = v___x_976_;
v_isShared_981_ = v_isSharedCheck_988_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_a_978_);
lean_inc(v_a_977_);
lean_dec(v___x_976_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_988_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_983_; 
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 0, v_a_977_);
v___x_983_ = v___x_973_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_a_977_);
v___x_983_ = v_reuseFailAlloc_987_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
lean_object* v___x_985_; 
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 0, v___x_983_);
v___x_985_ = v___x_980_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v___x_983_);
lean_ctor_set(v_reuseFailAlloc_986_, 1, v_a_978_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
}
else
{
lean_object* v_a_989_; lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_997_; 
lean_del_object(v___x_973_);
v_a_989_ = lean_ctor_get(v___x_976_, 0);
v_a_990_ = lean_ctor_get(v___x_976_, 1);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_997_ == 0)
{
v___x_992_ = v___x_976_;
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_inc(v_a_989_);
lean_dec(v___x_976_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_995_; 
if (v_isShared_993_ == 0)
{
v___x_995_ = v___x_992_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_a_989_);
lean_ctor_set(v_reuseFailAlloc_996_, 1, v_a_990_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decodeNameMap___redArg___lam__0(lean_object* v_fst_999_, lean_object* v_m_1000_, lean_object* v_v_1001_){
_start:
{
lean_object* v___x_1002_; 
v___x_1002_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_999_, v_v_1001_, v_m_1000_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decodeNameMap___redArg___lam__1(lean_object* v_dec_1003_, lean_object* v_x1_1004_, lean_object* v_x2_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v_fst_1007_; lean_object* v_snd_1008_; lean_object* v___f_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v_fst_1007_ = lean_ctor_get(v_x2_1005_, 0);
lean_inc(v_fst_1007_);
v_snd_1008_ = lean_ctor_get(v_x2_1005_, 1);
lean_inc(v_snd_1008_);
lean_dec_ref(v_x2_1005_);
v___f_1009_ = lean_alloc_closure((void*)(l_Lake_Toml_Table_decodeNameMap___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1009_, 0, v_fst_1007_);
v___x_1010_ = lean_apply_1(v_dec_1003_, v_snd_1008_);
v___x_1011_ = l_Lake_Toml_mergeErrors___redArg(v_x1_1004_, v___x_1010_, v___f_1009_, v___y_1006_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decodeNameMap___redArg(lean_object* v_dec_1014_, lean_object* v_t_1015_, lean_object* v_a_1016_){
_start:
{
lean_object* v_items_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1043_; 
v_items_1017_ = lean_ctor_get(v_t_1015_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v_t_1015_);
if (v_isSharedCheck_1043_ == 0)
{
lean_object* v_unused_1044_; 
v_unused_1044_ = lean_ctor_get(v_t_1015_, 1);
lean_dec(v_unused_1044_);
v___x_1019_ = v_t_1015_;
v_isShared_1020_ = v_isSharedCheck_1043_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_items_1017_);
lean_dec(v_t_1015_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1043_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; uint8_t v___x_1025_; 
v___x_1021_ = lean_box(1);
v___x_1022_ = lean_unsigned_to_nat(0u);
v___x_1023_ = lean_array_get_size(v_items_1017_);
v___x_1024_ = ((lean_object*)(l_Lake_Toml_decodeArray___redArg___closed__9));
v___x_1025_ = lean_nat_dec_lt(v___x_1022_, v___x_1023_);
if (v___x_1025_ == 0)
{
lean_object* v___x_1027_; 
lean_dec_ref(v_items_1017_);
lean_dec_ref(v_dec_1014_);
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 1, v_a_1016_);
lean_ctor_set(v___x_1019_, 0, v___x_1021_);
v___x_1027_ = v___x_1019_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v___x_1021_);
lean_ctor_set(v_reuseFailAlloc_1028_, 1, v_a_1016_);
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
lean_object* v___f_1029_; lean_object* v___x_1030_; uint8_t v___x_1031_; 
v___f_1029_ = lean_alloc_closure((void*)(l_Lake_Toml_Table_decodeNameMap___redArg___lam__1), 4, 1);
lean_closure_set(v___f_1029_, 0, v_dec_1014_);
v___x_1030_ = ((lean_object*)(l_Lake_Toml_Table_decodeNameMap___redArg___closed__0));
v___x_1031_ = lean_nat_dec_le(v___x_1023_, v___x_1023_);
if (v___x_1031_ == 0)
{
if (v___x_1025_ == 0)
{
lean_object* v___x_1033_; 
lean_dec_ref(v___f_1029_);
lean_dec_ref(v_items_1017_);
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 1, v_a_1016_);
lean_ctor_set(v___x_1019_, 0, v___x_1021_);
v___x_1033_ = v___x_1019_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v___x_1021_);
lean_ctor_set(v_reuseFailAlloc_1034_, 1, v_a_1016_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
else
{
size_t v___x_1035_; size_t v___x_1036_; lean_object* v___x_150__overap_1037_; lean_object* v___x_1038_; 
lean_del_object(v___x_1019_);
v___x_1035_ = ((size_t)0ULL);
v___x_1036_ = lean_usize_of_nat(v___x_1023_);
v___x_150__overap_1037_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1024_, v___f_1029_, v_items_1017_, v___x_1035_, v___x_1036_, v___x_1030_);
v___x_1038_ = lean_apply_1(v___x_150__overap_1037_, v_a_1016_);
return v___x_1038_;
}
}
else
{
size_t v___x_1039_; size_t v___x_1040_; lean_object* v___x_155__overap_1041_; lean_object* v___x_1042_; 
lean_del_object(v___x_1019_);
v___x_1039_ = ((size_t)0ULL);
v___x_1040_ = lean_usize_of_nat(v___x_1023_);
v___x_155__overap_1041_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1024_, v___f_1029_, v_items_1017_, v___x_1039_, v___x_1040_, v___x_1030_);
v___x_1042_ = lean_apply_1(v___x_155__overap_1041_, v_a_1016_);
return v___x_1042_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decodeNameMap(lean_object* v_00_u03b1_1045_, lean_object* v_dec_1046_, lean_object* v_t_1047_, lean_object* v_a_1048_){
_start:
{
lean_object* v___x_1049_; 
v___x_1049_ = l_Lake_Toml_Table_decodeNameMap___redArg(v_dec_1046_, v_t_1047_, v_a_1048_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_instDecodeTomlNameMap___redArg___lam__0(lean_object* v_inst_1050_, lean_object* v_x_1051_, lean_object* v___y_1052_){
_start:
{
lean_object* v___x_1053_; 
v___x_1053_ = l_Lake_Toml_Value_decodeTable(v_x_1051_, v___y_1052_);
if (lean_obj_tag(v___x_1053_) == 0)
{
lean_object* v_a_1054_; lean_object* v_a_1055_; lean_object* v___x_1056_; 
v_a_1054_ = lean_ctor_get(v___x_1053_, 0);
lean_inc(v_a_1054_);
v_a_1055_ = lean_ctor_get(v___x_1053_, 1);
lean_inc(v_a_1055_);
lean_dec_ref_known(v___x_1053_, 2);
v___x_1056_ = l_Lake_Toml_Table_decodeNameMap___redArg(v_inst_1050_, v_a_1054_, v_a_1055_);
return v___x_1056_;
}
else
{
lean_object* v_a_1057_; lean_object* v_a_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1065_; 
lean_dec_ref(v_inst_1050_);
v_a_1057_ = lean_ctor_get(v___x_1053_, 0);
v_a_1058_ = lean_ctor_get(v___x_1053_, 1);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1060_ = v___x_1053_;
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_a_1058_);
lean_inc(v_a_1057_);
lean_dec(v___x_1053_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1063_; 
if (v_isShared_1061_ == 0)
{
v___x_1063_ = v___x_1060_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_a_1057_);
lean_ctor_set(v_reuseFailAlloc_1064_, 1, v_a_1058_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_instDecodeTomlNameMap___redArg(lean_object* v_inst_1066_){
_start:
{
lean_object* v___f_1067_; 
v___f_1067_ = lean_alloc_closure((void*)(l_Lake_Toml_Table_instDecodeTomlNameMap___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1067_, 0, v_inst_1066_);
return v___f_1067_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_instDecodeTomlNameMap(lean_object* v_00_u03b1_1068_, lean_object* v_inst_1069_){
_start:
{
lean_object* v___f_1070_; 
v___f_1070_ = lean_alloc_closure((void*)(l_Lake_Toml_Table_instDecodeTomlNameMap___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1070_, 0, v_inst_1069_);
return v___f_1070_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_tryDecode___redArg(lean_object* v_inst_1071_, lean_object* v_dec_1072_, lean_object* v_t_1073_, lean_object* v_k_1074_, lean_object* v_ref_1075_, lean_object* v_a_1076_){
_start:
{
lean_object* v___x_1077_; 
lean_inc(v_k_1074_);
v___x_1077_ = l_Lake_Toml_Table_decodeValue(v_t_1073_, v_k_1074_, v_ref_1075_, v_a_1076_);
if (lean_obj_tag(v___x_1077_) == 0)
{
lean_object* v_a_1078_; lean_object* v_a_1079_; lean_object* v___x_1080_; 
v_a_1078_ = lean_ctor_get(v___x_1077_, 0);
lean_inc(v_a_1078_);
v_a_1079_ = lean_ctor_get(v___x_1077_, 1);
lean_inc(v_a_1079_);
lean_dec_ref_known(v___x_1077_, 2);
v___x_1080_ = l_Lake_Toml_decodeKeyval___redArg(v_dec_1072_, v_k_1074_, v_a_1078_, v_a_1079_);
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v_a_1081_; lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1089_; 
lean_dec(v_inst_1071_);
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
v_a_1082_ = lean_ctor_get(v___x_1080_, 1);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1084_ = v___x_1080_;
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_inc(v_a_1081_);
lean_dec(v___x_1080_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1087_; 
if (v_isShared_1085_ == 0)
{
v___x_1087_ = v___x_1084_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_a_1081_);
lean_ctor_set(v_reuseFailAlloc_1088_, 1, v_a_1082_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
else
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1097_; 
v_a_1090_ = lean_ctor_get(v___x_1080_, 1);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1097_ == 0)
{
lean_object* v_unused_1098_; 
v_unused_1098_ = lean_ctor_get(v___x_1080_, 0);
lean_dec(v_unused_1098_);
v___x_1092_ = v___x_1080_;
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1080_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1095_; 
if (v_isShared_1093_ == 0)
{
lean_ctor_set_tag(v___x_1092_, 0);
lean_ctor_set(v___x_1092_, 0, v_inst_1071_);
v___x_1095_ = v___x_1092_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_inst_1071_);
lean_ctor_set(v_reuseFailAlloc_1096_, 1, v_a_1090_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
}
else
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1106_; 
lean_dec(v_k_1074_);
lean_dec_ref(v_dec_1072_);
v_a_1099_ = lean_ctor_get(v___x_1077_, 1);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1106_ == 0)
{
lean_object* v_unused_1107_; 
v_unused_1107_ = lean_ctor_get(v___x_1077_, 0);
lean_dec(v_unused_1107_);
v___x_1101_ = v___x_1077_;
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1077_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1104_; 
if (v_isShared_1102_ == 0)
{
lean_ctor_set_tag(v___x_1101_, 0);
lean_ctor_set(v___x_1101_, 0, v_inst_1071_);
v___x_1104_ = v___x_1101_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_inst_1071_);
lean_ctor_set(v_reuseFailAlloc_1105_, 1, v_a_1099_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_tryDecode(lean_object* v_00_u03b1_1108_, lean_object* v_inst_1109_, lean_object* v_dec_1110_, lean_object* v_t_1111_, lean_object* v_k_1112_, lean_object* v_ref_1113_, lean_object* v_a_1114_){
_start:
{
lean_object* v___x_1115_; 
lean_inc(v_k_1112_);
v___x_1115_ = l_Lake_Toml_Table_decodeValue(v_t_1111_, v_k_1112_, v_ref_1113_, v_a_1114_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v_a_1116_; lean_object* v_a_1117_; lean_object* v___x_1118_; 
v_a_1116_ = lean_ctor_get(v___x_1115_, 0);
lean_inc(v_a_1116_);
v_a_1117_ = lean_ctor_get(v___x_1115_, 1);
lean_inc(v_a_1117_);
lean_dec_ref_known(v___x_1115_, 2);
v___x_1118_ = l_Lake_Toml_decodeKeyval___redArg(v_dec_1110_, v_k_1112_, v_a_1116_, v_a_1117_);
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v_a_1119_; lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1127_; 
lean_dec(v_inst_1109_);
v_a_1119_ = lean_ctor_get(v___x_1118_, 0);
v_a_1120_ = lean_ctor_get(v___x_1118_, 1);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1122_ = v___x_1118_;
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_inc(v_a_1119_);
lean_dec(v___x_1118_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1123_ == 0)
{
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_a_1119_);
lean_ctor_set(v_reuseFailAlloc_1126_, 1, v_a_1120_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
else
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1135_; 
v_a_1128_ = lean_ctor_get(v___x_1118_, 1);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1135_ == 0)
{
lean_object* v_unused_1136_; 
v_unused_1136_ = lean_ctor_get(v___x_1118_, 0);
lean_dec(v_unused_1136_);
v___x_1130_ = v___x_1118_;
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1118_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1133_; 
if (v_isShared_1131_ == 0)
{
lean_ctor_set_tag(v___x_1130_, 0);
lean_ctor_set(v___x_1130_, 0, v_inst_1109_);
v___x_1133_ = v___x_1130_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_inst_1109_);
lean_ctor_set(v_reuseFailAlloc_1134_, 1, v_a_1128_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
}
else
{
lean_object* v_a_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1144_; 
lean_dec(v_k_1112_);
lean_dec_ref(v_dec_1110_);
v_a_1137_ = lean_ctor_get(v___x_1115_, 1);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1144_ == 0)
{
lean_object* v_unused_1145_; 
v_unused_1145_ = lean_ctor_get(v___x_1115_, 0);
lean_dec(v_unused_1145_);
v___x_1139_ = v___x_1115_;
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_a_1137_);
lean_dec(v___x_1115_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1142_; 
if (v_isShared_1140_ == 0)
{
lean_ctor_set_tag(v___x_1139_, 0);
lean_ctor_set(v___x_1139_, 0, v_inst_1109_);
v___x_1142_ = v___x_1139_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_inst_1109_);
lean_ctor_set(v_reuseFailAlloc_1143_, 1, v_a_1137_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_tryDecode_x3f___redArg(lean_object* v_dec_1146_, lean_object* v_t_1147_, lean_object* v_k_1148_, lean_object* v_a_1149_){
_start:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1150_ = ((lean_object*)(l_Lake_Toml_Table_decodeValue___closed__0));
v___x_1151_ = l_Lake_Toml_RBDict_findEntry_x3f___redArg(v___x_1150_, v_k_1148_, v_t_1147_);
if (lean_obj_tag(v___x_1151_) == 0)
{
lean_object* v___x_1152_; lean_object* v___x_1153_; 
lean_dec_ref(v_dec_1146_);
v___x_1152_ = lean_box(0);
v___x_1153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1152_);
lean_ctor_set(v___x_1153_, 1, v_a_1149_);
return v___x_1153_;
}
else
{
lean_object* v_val_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1182_; 
v_val_1154_ = lean_ctor_get(v___x_1151_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1156_ = v___x_1151_;
v_isShared_1157_ = v_isSharedCheck_1182_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_val_1154_);
lean_dec(v___x_1151_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1182_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v_snd_1158_; lean_object* v___x_1159_; 
v_snd_1158_ = lean_ctor_get(v_val_1154_, 1);
lean_inc(v_snd_1158_);
lean_dec(v_val_1154_);
v___x_1159_ = lean_apply_2(v_dec_1146_, v_snd_1158_, v_a_1149_);
if (lean_obj_tag(v___x_1159_) == 0)
{
lean_object* v_a_1160_; lean_object* v_a_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1171_; 
v_a_1160_ = lean_ctor_get(v___x_1159_, 0);
v_a_1161_ = lean_ctor_get(v___x_1159_, 1);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1163_ = v___x_1159_;
v_isShared_1164_ = v_isSharedCheck_1171_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_a_1161_);
lean_inc(v_a_1160_);
lean_dec(v___x_1159_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1171_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1166_; 
if (v_isShared_1157_ == 0)
{
lean_ctor_set(v___x_1156_, 0, v_a_1160_);
v___x_1166_ = v___x_1156_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_a_1160_);
v___x_1166_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
lean_object* v___x_1168_; 
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 0, v___x_1166_);
v___x_1168_ = v___x_1163_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1166_);
lean_ctor_set(v_reuseFailAlloc_1169_, 1, v_a_1161_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
}
else
{
lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1180_; 
lean_del_object(v___x_1156_);
v_a_1172_ = lean_ctor_get(v___x_1159_, 1);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1180_ == 0)
{
lean_object* v_unused_1181_; 
v_unused_1181_ = lean_ctor_get(v___x_1159_, 0);
lean_dec(v_unused_1181_);
v___x_1174_ = v___x_1159_;
v_isShared_1175_ = v_isSharedCheck_1180_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_a_1172_);
lean_dec(v___x_1159_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1180_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1176_; lean_object* v___x_1178_; 
v___x_1176_ = lean_box(0);
if (v_isShared_1175_ == 0)
{
lean_ctor_set_tag(v___x_1174_, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1176_);
v___x_1178_ = v___x_1174_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v___x_1176_);
lean_ctor_set(v_reuseFailAlloc_1179_, 1, v_a_1172_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_tryDecode_x3f(lean_object* v_00_u03b1_1183_, lean_object* v_dec_1184_, lean_object* v_t_1185_, lean_object* v_k_1186_, lean_object* v_a_1187_){
_start:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1188_ = ((lean_object*)(l_Lake_Toml_Table_decodeValue___closed__0));
v___x_1189_ = l_Lake_Toml_RBDict_findEntry_x3f___redArg(v___x_1188_, v_k_1186_, v_t_1185_);
if (lean_obj_tag(v___x_1189_) == 0)
{
lean_object* v___x_1190_; lean_object* v___x_1191_; 
lean_dec_ref(v_dec_1184_);
v___x_1190_ = lean_box(0);
v___x_1191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1190_);
lean_ctor_set(v___x_1191_, 1, v_a_1187_);
return v___x_1191_;
}
else
{
lean_object* v_val_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1220_; 
v_val_1192_ = lean_ctor_get(v___x_1189_, 0);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1194_ = v___x_1189_;
v_isShared_1195_ = v_isSharedCheck_1220_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_val_1192_);
lean_dec(v___x_1189_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1220_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v_snd_1196_; lean_object* v___x_1197_; 
v_snd_1196_ = lean_ctor_get(v_val_1192_, 1);
lean_inc(v_snd_1196_);
lean_dec(v_val_1192_);
v___x_1197_ = lean_apply_2(v_dec_1184_, v_snd_1196_, v_a_1187_);
if (lean_obj_tag(v___x_1197_) == 0)
{
lean_object* v_a_1198_; lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1209_; 
v_a_1198_ = lean_ctor_get(v___x_1197_, 0);
v_a_1199_ = lean_ctor_get(v___x_1197_, 1);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1201_ = v___x_1197_;
v_isShared_1202_ = v_isSharedCheck_1209_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_inc(v_a_1198_);
lean_dec(v___x_1197_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1209_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1204_; 
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 0, v_a_1198_);
v___x_1204_ = v___x_1194_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_a_1198_);
v___x_1204_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
lean_object* v___x_1206_; 
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 0, v___x_1204_);
v___x_1206_ = v___x_1201_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v___x_1204_);
lean_ctor_set(v_reuseFailAlloc_1207_, 1, v_a_1199_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
}
else
{
lean_object* v_a_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1218_; 
lean_del_object(v___x_1194_);
v_a_1210_ = lean_ctor_get(v___x_1197_, 1);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1218_ == 0)
{
lean_object* v_unused_1219_; 
v_unused_1219_ = lean_ctor_get(v___x_1197_, 0);
lean_dec(v_unused_1219_);
v___x_1212_ = v___x_1197_;
v_isShared_1213_ = v_isSharedCheck_1218_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_a_1210_);
lean_dec(v___x_1197_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1218_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1214_; lean_object* v___x_1216_; 
v___x_1214_ = lean_box(0);
if (v_isShared_1213_ == 0)
{
lean_ctor_set_tag(v___x_1212_, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1214_);
v___x_1216_ = v___x_1212_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v___x_1214_);
lean_ctor_set(v_reuseFailAlloc_1217_, 1, v_a_1210_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
return v___x_1216_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_tryDecodeD___redArg(lean_object* v_dec_1221_, lean_object* v_k_1222_, lean_object* v_default_1223_, lean_object* v_t_1224_, lean_object* v_a_1225_){
_start:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1226_ = ((lean_object*)(l_Lake_Toml_Table_decodeValue___closed__0));
v___x_1227_ = l_Lake_Toml_RBDict_findEntry_x3f___redArg(v___x_1226_, v_k_1222_, v_t_1224_);
if (lean_obj_tag(v___x_1227_) == 0)
{
lean_object* v___x_1228_; 
lean_dec_ref(v_dec_1221_);
v___x_1228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1228_, 0, v_default_1223_);
lean_ctor_set(v___x_1228_, 1, v_a_1225_);
return v___x_1228_;
}
else
{
lean_object* v_val_1229_; lean_object* v_snd_1230_; lean_object* v___x_1231_; 
v_val_1229_ = lean_ctor_get(v___x_1227_, 0);
lean_inc(v_val_1229_);
lean_dec_ref_known(v___x_1227_, 1);
v_snd_1230_ = lean_ctor_get(v_val_1229_, 1);
lean_inc(v_snd_1230_);
lean_dec(v_val_1229_);
v___x_1231_ = lean_apply_2(v_dec_1221_, v_snd_1230_, v_a_1225_);
if (lean_obj_tag(v___x_1231_) == 0)
{
lean_object* v_a_1232_; lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1240_; 
lean_dec(v_default_1223_);
v_a_1232_ = lean_ctor_get(v___x_1231_, 0);
v_a_1233_ = lean_ctor_get(v___x_1231_, 1);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1231_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1235_ = v___x_1231_;
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_inc(v_a_1232_);
lean_dec(v___x_1231_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1238_; 
if (v_isShared_1236_ == 0)
{
v___x_1238_ = v___x_1235_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_a_1232_);
lean_ctor_set(v_reuseFailAlloc_1239_, 1, v_a_1233_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
}
else
{
lean_object* v_a_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1248_; 
v_a_1241_ = lean_ctor_get(v___x_1231_, 1);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1231_);
if (v_isSharedCheck_1248_ == 0)
{
lean_object* v_unused_1249_; 
v_unused_1249_ = lean_ctor_get(v___x_1231_, 0);
lean_dec(v_unused_1249_);
v___x_1243_ = v___x_1231_;
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_a_1241_);
lean_dec(v___x_1231_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1246_; 
if (v_isShared_1244_ == 0)
{
lean_ctor_set_tag(v___x_1243_, 0);
lean_ctor_set(v___x_1243_, 0, v_default_1223_);
v___x_1246_ = v___x_1243_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_default_1223_);
lean_ctor_set(v_reuseFailAlloc_1247_, 1, v_a_1241_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_tryDecodeD(lean_object* v_00_u03b1_1250_, lean_object* v_dec_1251_, lean_object* v_k_1252_, lean_object* v_default_1253_, lean_object* v_t_1254_, lean_object* v_a_1255_){
_start:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1256_ = ((lean_object*)(l_Lake_Toml_Table_decodeValue___closed__0));
v___x_1257_ = l_Lake_Toml_RBDict_findEntry_x3f___redArg(v___x_1256_, v_k_1252_, v_t_1254_);
if (lean_obj_tag(v___x_1257_) == 0)
{
lean_object* v___x_1258_; 
lean_dec_ref(v_dec_1251_);
v___x_1258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1258_, 0, v_default_1253_);
lean_ctor_set(v___x_1258_, 1, v_a_1255_);
return v___x_1258_;
}
else
{
lean_object* v_val_1259_; lean_object* v_snd_1260_; lean_object* v___x_1261_; 
v_val_1259_ = lean_ctor_get(v___x_1257_, 0);
lean_inc(v_val_1259_);
lean_dec_ref_known(v___x_1257_, 1);
v_snd_1260_ = lean_ctor_get(v_val_1259_, 1);
lean_inc(v_snd_1260_);
lean_dec(v_val_1259_);
v___x_1261_ = lean_apply_2(v_dec_1251_, v_snd_1260_, v_a_1255_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v_a_1262_; lean_object* v_a_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1270_; 
lean_dec(v_default_1253_);
v_a_1262_ = lean_ctor_get(v___x_1261_, 0);
v_a_1263_ = lean_ctor_get(v___x_1261_, 1);
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1265_ = v___x_1261_;
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_a_1263_);
lean_inc(v_a_1262_);
lean_dec(v___x_1261_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1268_; 
if (v_isShared_1266_ == 0)
{
v___x_1268_ = v___x_1265_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_a_1262_);
lean_ctor_set(v_reuseFailAlloc_1269_, 1, v_a_1263_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
}
else
{
lean_object* v_a_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1278_; 
v_a_1271_ = lean_ctor_get(v___x_1261_, 1);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1278_ == 0)
{
lean_object* v_unused_1279_; 
v_unused_1279_ = lean_ctor_get(v___x_1261_, 0);
lean_dec(v_unused_1279_);
v___x_1273_ = v___x_1261_;
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_a_1271_);
lean_dec(v___x_1261_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1276_; 
if (v_isShared_1274_ == 0)
{
lean_ctor_set_tag(v___x_1273_, 0);
lean_ctor_set(v___x_1273_, 0, v_default_1253_);
v___x_1276_ = v___x_1273_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_default_1253_);
lean_ctor_set(v_reuseFailAlloc_1277_, 1, v_a_1271_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
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
