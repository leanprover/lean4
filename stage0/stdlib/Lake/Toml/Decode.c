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
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decodeD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decodeD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___f_460_; lean_object* v___x_461_; size_t v___x_462_; size_t v___x_463_; lean_object* v___x_128__overap_464_; lean_object* v___x_465_; 
v___f_460_ = lean_alloc_closure((void*)(l_Lake_Toml_decodeArray___redArg___lam__0), 4, 1);
lean_closure_set(v___f_460_, 0, v_dec_451_);
v___x_461_ = lean_alloc_closure((void*)(l_EStateM_pure), 5, 4);
lean_closure_set(v___x_461_, 0, lean_box(0));
lean_closure_set(v___x_461_, 1, lean_box(0));
lean_closure_set(v___x_461_, 2, lean_box(0));
lean_closure_set(v___x_461_, 3, v___x_455_);
v___x_462_ = ((size_t)0ULL);
v___x_463_ = lean_usize_of_nat(v___x_454_);
v___x_128__overap_464_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_457_, v___f_460_, v_vs_452_, v___x_462_, v___x_463_, v___x_461_);
v___x_465_ = lean_apply_1(v___x_128__overap_464_, v_a_453_);
return v___x_465_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray(lean_object* v_00_u03b1_466_, lean_object* v_dec_467_, lean_object* v_vs_468_, lean_object* v_a_469_){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = l_Lake_Toml_decodeArray___redArg(v_dec_467_, v_vs_468_, v_a_469_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_decodeString(lean_object* v_v_474_, lean_object* v_a_475_){
_start:
{
lean_object* v___y_477_; 
if (lean_obj_tag(v_v_474_) == 0)
{
lean_object* v_s_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_490_; 
v_s_483_ = lean_ctor_get(v_v_474_, 1);
v_isSharedCheck_490_ = !lean_is_exclusive(v_v_474_);
if (v_isSharedCheck_490_ == 0)
{
lean_object* v_unused_491_; 
v_unused_491_ = lean_ctor_get(v_v_474_, 0);
lean_dec(v_unused_491_);
v___x_485_ = v_v_474_;
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_s_483_);
lean_dec(v_v_474_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_488_; 
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 1, v_a_475_);
lean_ctor_set(v___x_485_, 0, v_s_483_);
v___x_488_ = v___x_485_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_s_483_);
lean_ctor_set(v_reuseFailAlloc_489_, 1, v_a_475_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
else
{
lean_object* v_ref_492_; 
v_ref_492_ = lean_ctor_get(v_v_474_, 0);
lean_inc(v_ref_492_);
lean_dec_ref(v_v_474_);
v___y_477_ = v_ref_492_;
goto v___jp_476_;
}
v___jp_476_:
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_478_ = ((lean_object*)(l_Lake_Toml_Value_decodeString___closed__0));
v___x_479_ = lean_box(0);
v___x_480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_480_, 0, v___y_477_);
lean_ctor_set(v___x_480_, 1, v___x_478_);
v___x_481_ = lean_array_push(v_a_475_, v___x_480_);
v___x_482_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_482_, 0, v___x_479_);
lean_ctor_set(v___x_482_, 1, v___x_481_);
return v___x_482_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_instDecodeTomlFilePath___lam__0(lean_object* v_x_495_, lean_object* v___y_496_){
_start:
{
lean_object* v___x_497_; 
v___x_497_ = l_Lake_Toml_Value_decodeString(v_x_495_, v___y_496_);
if (lean_obj_tag(v___x_497_) == 0)
{
lean_object* v_a_498_; lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_506_; 
v_a_498_ = lean_ctor_get(v___x_497_, 0);
v_a_499_ = lean_ctor_get(v___x_497_, 1);
v_isSharedCheck_506_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_506_ == 0)
{
v___x_501_ = v___x_497_;
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_inc(v_a_498_);
lean_dec(v___x_497_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_504_; 
if (v_isShared_502_ == 0)
{
v___x_504_ = v___x_501_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_a_498_);
lean_ctor_set(v_reuseFailAlloc_505_, 1, v_a_499_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
else
{
lean_object* v_a_507_; lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_515_; 
v_a_507_ = lean_ctor_get(v___x_497_, 0);
v_a_508_ = lean_ctor_get(v___x_497_, 1);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_515_ == 0)
{
v___x_510_ = v___x_497_;
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_a_508_);
lean_inc(v_a_507_);
lean_dec(v___x_497_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_513_; 
if (v_isShared_511_ == 0)
{
v___x_513_ = v___x_510_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_a_507_);
lean_ctor_set(v_reuseFailAlloc_514_, 1, v_a_508_);
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
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_decodeName(lean_object* v_v_519_, lean_object* v_a_520_){
_start:
{
lean_object* v___x_521_; 
lean_inc_ref(v_v_519_);
v___x_521_ = l_Lake_Toml_Value_decodeString(v_v_519_, v_a_520_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v_a_522_; lean_object* v_a_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_539_; 
v_a_522_ = lean_ctor_get(v___x_521_, 0);
v_a_523_ = lean_ctor_get(v___x_521_, 1);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_539_ == 0)
{
v___x_525_ = v___x_521_;
v_isShared_526_ = v_isSharedCheck_539_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_a_523_);
lean_inc(v_a_522_);
lean_dec(v___x_521_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_539_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___y_528_; lean_object* v___x_536_; 
v___x_536_ = l_String_toName(v_a_522_);
if (lean_obj_tag(v___x_536_) == 0)
{
lean_object* v_ref_537_; 
v_ref_537_ = lean_ctor_get(v_v_519_, 0);
lean_inc(v_ref_537_);
lean_dec_ref(v_v_519_);
v___y_528_ = v_ref_537_;
goto v___jp_527_;
}
else
{
lean_object* v___x_538_; 
lean_del_object(v___x_525_);
lean_dec_ref(v_v_519_);
v___x_538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_538_, 0, v___x_536_);
lean_ctor_set(v___x_538_, 1, v_a_523_);
return v___x_538_;
}
v___jp_527_:
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_534_; 
v___x_529_ = ((lean_object*)(l_Lake_Toml_Value_decodeName___closed__0));
v___x_530_ = lean_box(0);
v___x_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_531_, 0, v___y_528_);
lean_ctor_set(v___x_531_, 1, v___x_529_);
v___x_532_ = lean_array_push(v_a_523_, v___x_531_);
if (v_isShared_526_ == 0)
{
lean_ctor_set_tag(v___x_525_, 1);
lean_ctor_set(v___x_525_, 1, v___x_532_);
lean_ctor_set(v___x_525_, 0, v___x_530_);
v___x_534_ = v___x_525_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_530_);
lean_ctor_set(v_reuseFailAlloc_535_, 1, v___x_532_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
}
else
{
lean_object* v_a_540_; lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_548_; 
lean_dec_ref(v_v_519_);
v_a_540_ = lean_ctor_get(v___x_521_, 0);
v_a_541_ = lean_ctor_get(v___x_521_, 1);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_548_ == 0)
{
v___x_543_ = v___x_521_;
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_inc(v_a_540_);
lean_dec(v___x_521_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_546_; 
if (v_isShared_544_ == 0)
{
v___x_546_ = v___x_543_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_a_540_);
lean_ctor_set(v_reuseFailAlloc_547_, 1, v_a_541_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_decodeInt(lean_object* v_v_552_, lean_object* v_a_553_){
_start:
{
lean_object* v___y_555_; 
if (lean_obj_tag(v_v_552_) == 1)
{
lean_object* v_n_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_568_; 
v_n_561_ = lean_ctor_get(v_v_552_, 1);
v_isSharedCheck_568_ = !lean_is_exclusive(v_v_552_);
if (v_isSharedCheck_568_ == 0)
{
lean_object* v_unused_569_; 
v_unused_569_ = lean_ctor_get(v_v_552_, 0);
lean_dec(v_unused_569_);
v___x_563_ = v_v_552_;
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_n_561_);
lean_dec(v_v_552_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_566_; 
if (v_isShared_564_ == 0)
{
lean_ctor_set_tag(v___x_563_, 0);
lean_ctor_set(v___x_563_, 1, v_a_553_);
lean_ctor_set(v___x_563_, 0, v_n_561_);
v___x_566_ = v___x_563_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_n_561_);
lean_ctor_set(v_reuseFailAlloc_567_, 1, v_a_553_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
}
else
{
lean_object* v_ref_570_; 
v_ref_570_ = lean_ctor_get(v_v_552_, 0);
lean_inc(v_ref_570_);
lean_dec_ref(v_v_552_);
v___y_555_ = v_ref_570_;
goto v___jp_554_;
}
v___jp_554_:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_556_ = ((lean_object*)(l_Lake_Toml_Value_decodeInt___closed__0));
v___x_557_ = lean_box(0);
v___x_558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_558_, 0, v___y_555_);
lean_ctor_set(v___x_558_, 1, v___x_556_);
v___x_559_ = lean_array_push(v_a_553_, v___x_558_);
v___x_560_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_560_, 0, v___x_557_);
lean_ctor_set(v___x_560_, 1, v___x_559_);
return v___x_560_;
}
}
}
static lean_object* _init_l_Lake_Toml_Value_decodeNat___closed__1(void){
_start:
{
lean_object* v_natZero_574_; lean_object* v_intZero_575_; 
v_natZero_574_ = lean_unsigned_to_nat(0u);
v_intZero_575_ = lean_nat_to_int(v_natZero_574_);
return v_intZero_575_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_decodeNat(lean_object* v_x_576_, lean_object* v_a_577_){
_start:
{
lean_object* v___y_579_; lean_object* v___y_580_; 
if (lean_obj_tag(v_x_576_) == 1)
{
lean_object* v_ref_586_; lean_object* v_n_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_597_; 
v_ref_586_ = lean_ctor_get(v_x_576_, 0);
v_n_587_ = lean_ctor_get(v_x_576_, 1);
v_isSharedCheck_597_ = !lean_is_exclusive(v_x_576_);
if (v_isSharedCheck_597_ == 0)
{
v___x_589_ = v_x_576_;
v_isShared_590_ = v_isSharedCheck_597_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_n_587_);
lean_inc(v_ref_586_);
lean_dec(v_x_576_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_597_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v_intZero_591_; uint8_t v_isNeg_592_; 
v_intZero_591_ = lean_obj_once(&l_Lake_Toml_Value_decodeNat___closed__1, &l_Lake_Toml_Value_decodeNat___closed__1_once, _init_l_Lake_Toml_Value_decodeNat___closed__1);
v_isNeg_592_ = lean_int_dec_lt(v_n_587_, v_intZero_591_);
if (v_isNeg_592_ == 0)
{
lean_object* v_a_593_; lean_object* v___x_595_; 
lean_dec(v_ref_586_);
v_a_593_ = lean_nat_abs(v_n_587_);
lean_dec(v_n_587_);
if (v_isShared_590_ == 0)
{
lean_ctor_set_tag(v___x_589_, 0);
lean_ctor_set(v___x_589_, 1, v_a_577_);
lean_ctor_set(v___x_589_, 0, v_a_593_);
v___x_595_ = v___x_589_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_a_593_);
lean_ctor_set(v_reuseFailAlloc_596_, 1, v_a_577_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
else
{
lean_del_object(v___x_589_);
lean_dec(v_n_587_);
v___y_579_ = v_a_577_;
v___y_580_ = v_ref_586_;
goto v___jp_578_;
}
}
}
else
{
lean_object* v_ref_598_; 
v_ref_598_ = lean_ctor_get(v_x_576_, 0);
lean_inc(v_ref_598_);
lean_dec_ref(v_x_576_);
v___y_579_ = v_a_577_;
v___y_580_ = v_ref_598_;
goto v___jp_578_;
}
v___jp_578_:
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_581_ = ((lean_object*)(l_Lake_Toml_Value_decodeNat___closed__0));
v___x_582_ = lean_box(0);
v___x_583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_583_, 0, v___y_580_);
lean_ctor_set(v___x_583_, 1, v___x_581_);
v___x_584_ = lean_array_push(v___y_579_, v___x_583_);
v___x_585_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_585_, 0, v___x_582_);
lean_ctor_set(v___x_585_, 1, v___x_584_);
return v___x_585_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_decodeFloat(lean_object* v_v_602_, lean_object* v_a_603_){
_start:
{
lean_object* v___y_605_; 
if (lean_obj_tag(v_v_602_) == 2)
{
double v_n_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v_n_611_ = lean_ctor_get_float(v_v_602_, sizeof(void*)*1);
lean_dec_ref_known(v_v_602_, 1);
v___x_612_ = lean_box_float(v_n_611_);
v___x_613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
lean_ctor_set(v___x_613_, 1, v_a_603_);
return v___x_613_;
}
else
{
lean_object* v_ref_614_; 
v_ref_614_ = lean_ctor_get(v_v_602_, 0);
lean_inc(v_ref_614_);
lean_dec_ref(v_v_602_);
v___y_605_ = v_ref_614_;
goto v___jp_604_;
}
v___jp_604_:
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_606_ = ((lean_object*)(l_Lake_Toml_Value_decodeFloat___closed__0));
v___x_607_ = lean_box(0);
v___x_608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_608_, 0, v___y_605_);
lean_ctor_set(v___x_608_, 1, v___x_606_);
v___x_609_ = lean_array_push(v_a_603_, v___x_608_);
v___x_610_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_607_);
lean_ctor_set(v___x_610_, 1, v___x_609_);
return v___x_610_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_decodeBool(lean_object* v_v_618_, lean_object* v_a_619_){
_start:
{
lean_object* v___y_621_; 
if (lean_obj_tag(v_v_618_) == 3)
{
uint8_t v_b_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v_b_627_ = lean_ctor_get_uint8(v_v_618_, sizeof(void*)*1);
lean_dec_ref_known(v_v_618_, 1);
v___x_628_ = lean_box(v_b_627_);
v___x_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
lean_ctor_set(v___x_629_, 1, v_a_619_);
return v___x_629_;
}
else
{
lean_object* v_ref_630_; 
v_ref_630_ = lean_ctor_get(v_v_618_, 0);
lean_inc(v_ref_630_);
lean_dec_ref(v_v_618_);
v___y_621_ = v_ref_630_;
goto v___jp_620_;
}
v___jp_620_:
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_622_ = ((lean_object*)(l_Lake_Toml_Value_decodeBool___closed__0));
v___x_623_ = lean_box(0);
v___x_624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_624_, 0, v___y_621_);
lean_ctor_set(v___x_624_, 1, v___x_622_);
v___x_625_ = lean_array_push(v_a_619_, v___x_624_);
v___x_626_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_626_, 0, v___x_623_);
lean_ctor_set(v___x_626_, 1, v___x_625_);
return v___x_626_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_decodeDateTime(lean_object* v_v_634_, lean_object* v_a_635_){
_start:
{
lean_object* v___y_637_; 
if (lean_obj_tag(v_v_634_) == 4)
{
lean_object* v_dt_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_650_; 
v_dt_643_ = lean_ctor_get(v_v_634_, 1);
v_isSharedCheck_650_ = !lean_is_exclusive(v_v_634_);
if (v_isSharedCheck_650_ == 0)
{
lean_object* v_unused_651_; 
v_unused_651_ = lean_ctor_get(v_v_634_, 0);
lean_dec(v_unused_651_);
v___x_645_ = v_v_634_;
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_dt_643_);
lean_dec(v_v_634_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_648_; 
if (v_isShared_646_ == 0)
{
lean_ctor_set_tag(v___x_645_, 0);
lean_ctor_set(v___x_645_, 1, v_a_635_);
lean_ctor_set(v___x_645_, 0, v_dt_643_);
v___x_648_ = v___x_645_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_dt_643_);
lean_ctor_set(v_reuseFailAlloc_649_, 1, v_a_635_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
else
{
lean_object* v_ref_652_; 
v_ref_652_ = lean_ctor_get(v_v_634_, 0);
lean_inc(v_ref_652_);
lean_dec_ref(v_v_634_);
v___y_637_ = v_ref_652_;
goto v___jp_636_;
}
v___jp_636_:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_638_ = ((lean_object*)(l_Lake_Toml_Value_decodeDateTime___closed__0));
v___x_639_ = lean_box(0);
v___x_640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_640_, 0, v___y_637_);
lean_ctor_set(v___x_640_, 1, v___x_638_);
v___x_641_ = lean_array_push(v_a_635_, v___x_640_);
v___x_642_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_642_, 0, v___x_639_);
lean_ctor_set(v___x_642_, 1, v___x_641_);
return v___x_642_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_decodeValueArray(lean_object* v_v_656_, lean_object* v_a_657_){
_start:
{
lean_object* v___y_659_; 
if (lean_obj_tag(v_v_656_) == 5)
{
lean_object* v_xs_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_672_; 
v_xs_665_ = lean_ctor_get(v_v_656_, 1);
v_isSharedCheck_672_ = !lean_is_exclusive(v_v_656_);
if (v_isSharedCheck_672_ == 0)
{
lean_object* v_unused_673_; 
v_unused_673_ = lean_ctor_get(v_v_656_, 0);
lean_dec(v_unused_673_);
v___x_667_ = v_v_656_;
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_xs_665_);
lean_dec(v_v_656_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_670_; 
if (v_isShared_668_ == 0)
{
lean_ctor_set_tag(v___x_667_, 0);
lean_ctor_set(v___x_667_, 1, v_a_657_);
lean_ctor_set(v___x_667_, 0, v_xs_665_);
v___x_670_ = v___x_667_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_xs_665_);
lean_ctor_set(v_reuseFailAlloc_671_, 1, v_a_657_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
else
{
lean_object* v_ref_674_; 
v_ref_674_ = lean_ctor_get(v_v_656_, 0);
lean_inc(v_ref_674_);
lean_dec_ref(v_v_656_);
v___y_659_ = v_ref_674_;
goto v___jp_658_;
}
v___jp_658_:
{
lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_660_ = ((lean_object*)(l_Lake_Toml_Value_decodeValueArray___closed__0));
v___x_661_ = lean_box(0);
v___x_662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_662_, 0, v___y_659_);
lean_ctor_set(v___x_662_, 1, v___x_660_);
v___x_663_ = lean_array_push(v_a_657_, v___x_662_);
v___x_664_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_664_, 0, v___x_661_);
lean_ctor_set(v___x_664_, 1, v___x_663_);
return v___x_664_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_decodeArray___redArg(lean_object* v_dec_675_, lean_object* v_v_676_, lean_object* v_a_677_){
_start:
{
lean_object* v___x_678_; 
v___x_678_ = l_Lake_Toml_Value_decodeValueArray(v_v_676_, v_a_677_);
if (lean_obj_tag(v___x_678_) == 0)
{
lean_object* v_a_679_; lean_object* v_a_680_; lean_object* v___x_681_; 
v_a_679_ = lean_ctor_get(v___x_678_, 0);
lean_inc(v_a_679_);
v_a_680_ = lean_ctor_get(v___x_678_, 1);
lean_inc(v_a_680_);
lean_dec_ref_known(v___x_678_, 2);
v___x_681_ = l_Lake_Toml_decodeArray___redArg(v_dec_675_, v_a_679_, v_a_680_);
return v___x_681_;
}
else
{
lean_object* v_a_682_; lean_object* v_a_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_690_; 
lean_dec_ref(v_dec_675_);
v_a_682_ = lean_ctor_get(v___x_678_, 0);
v_a_683_ = lean_ctor_get(v___x_678_, 1);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_690_ == 0)
{
v___x_685_ = v___x_678_;
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_a_683_);
lean_inc(v_a_682_);
lean_dec(v___x_678_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_688_; 
if (v_isShared_686_ == 0)
{
v___x_688_ = v___x_685_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_a_682_);
lean_ctor_set(v_reuseFailAlloc_689_, 1, v_a_683_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_decodeArray(lean_object* v_00_u03b1_691_, lean_object* v_dec_692_, lean_object* v_v_693_, lean_object* v_a_694_){
_start:
{
lean_object* v___x_695_; 
v___x_695_ = l_Lake_Toml_Value_decodeValueArray(v_v_693_, v_a_694_);
if (lean_obj_tag(v___x_695_) == 0)
{
lean_object* v_a_696_; lean_object* v_a_697_; lean_object* v___x_698_; 
v_a_696_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_a_696_);
v_a_697_ = lean_ctor_get(v___x_695_, 1);
lean_inc(v_a_697_);
lean_dec_ref_known(v___x_695_, 2);
v___x_698_ = l_Lake_Toml_decodeArray___redArg(v_dec_692_, v_a_696_, v_a_697_);
return v___x_698_;
}
else
{
lean_object* v_a_699_; lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_707_; 
lean_dec_ref(v_dec_692_);
v_a_699_ = lean_ctor_get(v___x_695_, 0);
v_a_700_ = lean_ctor_get(v___x_695_, 1);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_707_ == 0)
{
v___x_702_ = v___x_695_;
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_inc(v_a_699_);
lean_dec(v___x_695_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_705_; 
if (v_isShared_703_ == 0)
{
v___x_705_ = v___x_702_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_a_699_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v_a_700_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_instDecodeTomlArray___redArg(lean_object* v_inst_708_){
_start:
{
lean_object* v___x_709_; 
v___x_709_ = lean_alloc_closure((void*)(l_Lake_Toml_Value_decodeArray), 4, 2);
lean_closure_set(v___x_709_, 0, lean_box(0));
lean_closure_set(v___x_709_, 1, v_inst_708_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_instDecodeTomlArray(lean_object* v_00_u03b1_710_, lean_object* v_inst_711_){
_start:
{
lean_object* v___x_712_; 
v___x_712_ = lean_alloc_closure((void*)(l_Lake_Toml_Value_decodeArray), 4, 2);
lean_closure_set(v___x_712_, 0, lean_box(0));
lean_closure_set(v___x_712_, 1, v_inst_711_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_decodeArrayOrSingleton___redArg(lean_object* v_dec_713_, lean_object* v_v_714_, lean_object* v_a_715_){
_start:
{
if (lean_obj_tag(v_v_714_) == 5)
{
lean_object* v_xs_716_; lean_object* v___x_717_; 
v_xs_716_ = lean_ctor_get(v_v_714_, 1);
lean_inc_ref(v_xs_716_);
lean_dec_ref_known(v_v_714_, 2);
v___x_717_ = l_Lake_Toml_decodeArray___redArg(v_dec_713_, v_xs_716_, v_a_715_);
return v___x_717_;
}
else
{
lean_object* v___x_718_; 
v___x_718_ = lean_apply_2(v_dec_713_, v_v_714_, v_a_715_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v_a_719_; lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_730_; 
v_a_719_ = lean_ctor_get(v___x_718_, 0);
v_a_720_ = lean_ctor_get(v___x_718_, 1);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_730_ == 0)
{
v___x_722_ = v___x_718_;
v_isShared_723_ = v_isSharedCheck_730_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_inc(v_a_719_);
lean_dec(v___x_718_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_730_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_728_; 
v___x_724_ = lean_unsigned_to_nat(1u);
v___x_725_ = lean_mk_empty_array_with_capacity(v___x_724_);
v___x_726_ = lean_array_push(v___x_725_, v_a_719_);
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 0, v___x_726_);
v___x_728_ = v___x_722_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v___x_726_);
lean_ctor_set(v_reuseFailAlloc_729_, 1, v_a_720_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
else
{
lean_object* v_a_731_; lean_object* v_a_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_739_; 
v_a_731_ = lean_ctor_get(v___x_718_, 0);
v_a_732_ = lean_ctor_get(v___x_718_, 1);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_739_ == 0)
{
v___x_734_ = v___x_718_;
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_a_732_);
lean_inc(v_a_731_);
lean_dec(v___x_718_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_737_; 
if (v_isShared_735_ == 0)
{
v___x_737_ = v___x_734_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_a_731_);
lean_ctor_set(v_reuseFailAlloc_738_, 1, v_a_732_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_decodeArrayOrSingleton(lean_object* v_00_u03b1_740_, lean_object* v_dec_741_, lean_object* v_v_742_, lean_object* v_a_743_){
_start:
{
if (lean_obj_tag(v_v_742_) == 5)
{
lean_object* v_xs_744_; lean_object* v___x_745_; 
v_xs_744_ = lean_ctor_get(v_v_742_, 1);
lean_inc_ref(v_xs_744_);
lean_dec_ref_known(v_v_742_, 2);
v___x_745_ = l_Lake_Toml_decodeArray___redArg(v_dec_741_, v_xs_744_, v_a_743_);
return v___x_745_;
}
else
{
lean_object* v___x_746_; 
v___x_746_ = lean_apply_2(v_dec_741_, v_v_742_, v_a_743_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v_a_747_; lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_758_; 
v_a_747_ = lean_ctor_get(v___x_746_, 0);
v_a_748_ = lean_ctor_get(v___x_746_, 1);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_758_ == 0)
{
v___x_750_ = v___x_746_;
v_isShared_751_ = v_isSharedCheck_758_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_inc(v_a_747_);
lean_dec(v___x_746_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_758_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_756_; 
v___x_752_ = lean_unsigned_to_nat(1u);
v___x_753_ = lean_mk_empty_array_with_capacity(v___x_752_);
v___x_754_ = lean_array_push(v___x_753_, v_a_747_);
if (v_isShared_751_ == 0)
{
lean_ctor_set(v___x_750_, 0, v___x_754_);
v___x_756_ = v___x_750_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v___x_754_);
lean_ctor_set(v_reuseFailAlloc_757_, 1, v_a_748_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
else
{
lean_object* v_a_759_; lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_767_; 
v_a_759_ = lean_ctor_get(v___x_746_, 0);
v_a_760_ = lean_ctor_get(v___x_746_, 1);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_767_ == 0)
{
v___x_762_ = v___x_746_;
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_inc(v_a_759_);
lean_dec(v___x_746_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_765_; 
if (v_isShared_763_ == 0)
{
v___x_765_ = v___x_762_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_a_759_);
lean_ctor_set(v_reuseFailAlloc_766_, 1, v_a_760_);
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
LEAN_EXPORT lean_object* l_Lake_Toml_Value_decodeTable(lean_object* v_v_769_, lean_object* v_a_770_){
_start:
{
lean_object* v___y_772_; 
if (lean_obj_tag(v_v_769_) == 6)
{
lean_object* v_xs_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_785_; 
v_xs_778_ = lean_ctor_get(v_v_769_, 1);
v_isSharedCheck_785_ = !lean_is_exclusive(v_v_769_);
if (v_isSharedCheck_785_ == 0)
{
lean_object* v_unused_786_; 
v_unused_786_ = lean_ctor_get(v_v_769_, 0);
lean_dec(v_unused_786_);
v___x_780_ = v_v_769_;
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_xs_778_);
lean_dec(v_v_769_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_783_; 
if (v_isShared_781_ == 0)
{
lean_ctor_set_tag(v___x_780_, 0);
lean_ctor_set(v___x_780_, 1, v_a_770_);
lean_ctor_set(v___x_780_, 0, v_xs_778_);
v___x_783_ = v___x_780_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_xs_778_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v_a_770_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
else
{
lean_object* v_ref_787_; 
v_ref_787_ = lean_ctor_get(v_v_769_, 0);
lean_inc(v_ref_787_);
lean_dec_ref(v_v_769_);
v___y_772_ = v_ref_787_;
goto v___jp_771_;
}
v___jp_771_:
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_773_ = ((lean_object*)(l_Lake_Toml_Value_decodeTable___closed__0));
v___x_774_ = lean_box(0);
v___x_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_775_, 0, v___y_772_);
lean_ctor_set(v___x_775_, 1, v___x_773_);
v___x_776_ = lean_array_push(v_a_770_, v___x_775_);
v___x_777_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_777_, 0, v___x_774_);
lean_ctor_set(v___x_777_, 1, v___x_776_);
return v___x_777_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_decodeKeyval___redArg___lam__0(lean_object* v_iniPos_792_, lean_object* v_k_793_, lean_object* v_i_794_, lean_object* v_a_795_, lean_object* v_x_796_){
_start:
{
uint8_t v___x_797_; 
v___x_797_ = lean_nat_dec_le(v_iniPos_792_, v_i_794_);
if (v___x_797_ == 0)
{
lean_dec(v_k_793_);
return v_a_795_;
}
else
{
lean_object* v_ref_798_; lean_object* v_msg_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_812_; 
v_ref_798_ = lean_ctor_get(v_a_795_, 0);
v_msg_799_ = lean_ctor_get(v_a_795_, 1);
v_isSharedCheck_812_ = !lean_is_exclusive(v_a_795_);
if (v_isSharedCheck_812_ == 0)
{
v___x_801_ = v_a_795_;
v_isShared_802_ = v_isSharedCheck_812_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_msg_799_);
lean_inc(v_ref_798_);
lean_dec(v_a_795_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_812_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_810_; 
v___x_803_ = ((lean_object*)(l_Lake_Toml_decodeKeyval___redArg___lam__0___closed__0));
v___x_804_ = l_Lake_Toml_ppKey(v_k_793_);
v___x_805_ = lean_string_append(v___x_803_, v___x_804_);
lean_dec_ref(v___x_804_);
v___x_806_ = ((lean_object*)(l_Lake_Toml_decodeKeyval___redArg___lam__0___closed__1));
v___x_807_ = lean_string_append(v___x_805_, v___x_806_);
v___x_808_ = lean_string_append(v___x_807_, v_msg_799_);
lean_dec_ref(v_msg_799_);
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 1, v___x_808_);
v___x_810_ = v___x_801_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_ref_798_);
lean_ctor_set(v_reuseFailAlloc_811_, 1, v___x_808_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_decodeKeyval___redArg___lam__0___boxed(lean_object* v_iniPos_813_, lean_object* v_k_814_, lean_object* v_i_815_, lean_object* v_a_816_, lean_object* v_x_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Lake_Toml_decodeKeyval___redArg___lam__0(v_iniPos_813_, v_k_814_, v_i_815_, v_a_816_, v_x_817_);
lean_dec(v_i_815_);
lean_dec(v_iniPos_813_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_decodeKeyval___redArg___lam__1(lean_object* v___f_819_, lean_object* v_es_820_){
_start:
{
lean_object* v___x_821_; size_t v_sz_822_; size_t v___x_823_; lean_object* v___x_824_; 
v___x_821_ = ((lean_object*)(l_Lake_Toml_decodeArray___redArg___closed__9));
v_sz_822_ = lean_array_size(v_es_820_);
v___x_823_ = ((size_t)0ULL);
lean_inc_ref(v_es_820_);
v___x_824_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_821_, v_es_820_, v___f_819_, v_sz_822_, v___x_823_, v_es_820_);
lean_dec_ref(v_es_820_);
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
lean_dec_ref_known(v___x_865_, 1);
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
lean_dec_ref_known(v___x_888_, 2);
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
lean_dec_ref_known(v___x_907_, 2);
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
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decodeD___redArg(lean_object* v_dec_993_, lean_object* v_t_994_, lean_object* v_k_995_, lean_object* v_default_996_, lean_object* v_a_997_){
_start:
{
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = ((lean_object*)(l_Lake_Toml_Table_decodeValue___closed__0));
lean_inc(v_k_995_);
v___x_999_ = l_Lake_Toml_RBDict_findEntry_x3f___redArg(v___x_998_, v_k_995_, v_t_994_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v___x_1000_; 
lean_dec(v_k_995_);
lean_dec_ref(v_dec_993_);
v___x_1000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1000_, 0, v_default_996_);
lean_ctor_set(v___x_1000_, 1, v_a_997_);
return v___x_1000_;
}
else
{
lean_object* v_val_1001_; lean_object* v_snd_1002_; lean_object* v___x_1003_; 
lean_dec(v_default_996_);
v_val_1001_ = lean_ctor_get(v___x_999_, 0);
lean_inc(v_val_1001_);
lean_dec_ref_known(v___x_999_, 1);
v_snd_1002_ = lean_ctor_get(v_val_1001_, 1);
lean_inc(v_snd_1002_);
lean_dec(v_val_1001_);
v___x_1003_ = l_Lake_Toml_decodeKeyval___redArg(v_dec_993_, v_k_995_, v_snd_1002_, v_a_997_);
return v___x_1003_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decodeD(lean_object* v_00_u03b1_1004_, lean_object* v_dec_1005_, lean_object* v_t_1006_, lean_object* v_k_1007_, lean_object* v_default_1008_, lean_object* v_a_1009_){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1010_ = ((lean_object*)(l_Lake_Toml_Table_decodeValue___closed__0));
lean_inc(v_k_1007_);
v___x_1011_ = l_Lake_Toml_RBDict_findEntry_x3f___redArg(v___x_1010_, v_k_1007_, v_t_1006_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_object* v___x_1012_; 
lean_dec(v_k_1007_);
lean_dec_ref(v_dec_1005_);
v___x_1012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1012_, 0, v_default_1008_);
lean_ctor_set(v___x_1012_, 1, v_a_1009_);
return v___x_1012_;
}
else
{
lean_object* v_val_1013_; lean_object* v_snd_1014_; lean_object* v___x_1015_; 
lean_dec(v_default_1008_);
v_val_1013_ = lean_ctor_get(v___x_1011_, 0);
lean_inc(v_val_1013_);
lean_dec_ref_known(v___x_1011_, 1);
v_snd_1014_ = lean_ctor_get(v_val_1013_, 1);
lean_inc(v_snd_1014_);
lean_dec(v_val_1013_);
v___x_1015_ = l_Lake_Toml_decodeKeyval___redArg(v_dec_1005_, v_k_1007_, v_snd_1014_, v_a_1009_);
return v___x_1015_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decodeNameMap___redArg___lam__0(lean_object* v_fst_1016_, lean_object* v_m_1017_, lean_object* v_v_1018_){
_start:
{
lean_object* v___x_1019_; 
v___x_1019_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_1016_, v_v_1018_, v_m_1017_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decodeNameMap___redArg___lam__1(lean_object* v_dec_1020_, lean_object* v_x1_1021_, lean_object* v_x2_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v_fst_1024_; lean_object* v_snd_1025_; lean_object* v___f_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
v_fst_1024_ = lean_ctor_get(v_x2_1022_, 0);
lean_inc(v_fst_1024_);
v_snd_1025_ = lean_ctor_get(v_x2_1022_, 1);
lean_inc(v_snd_1025_);
lean_dec_ref(v_x2_1022_);
v___f_1026_ = lean_alloc_closure((void*)(l_Lake_Toml_Table_decodeNameMap___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1026_, 0, v_fst_1024_);
v___x_1027_ = lean_apply_1(v_dec_1020_, v_snd_1025_);
v___x_1028_ = l_Lake_Toml_mergeErrors___redArg(v_x1_1021_, v___x_1027_, v___f_1026_, v___y_1023_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decodeNameMap___redArg(lean_object* v_dec_1031_, lean_object* v_t_1032_, lean_object* v_a_1033_){
_start:
{
lean_object* v_items_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1052_; 
v_items_1034_ = lean_ctor_get(v_t_1032_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v_t_1032_);
if (v_isSharedCheck_1052_ == 0)
{
lean_object* v_unused_1053_; 
v_unused_1053_ = lean_ctor_get(v_t_1032_, 1);
lean_dec(v_unused_1053_);
v___x_1036_ = v_t_1032_;
v_isShared_1037_ = v_isSharedCheck_1052_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_items_1034_);
lean_dec(v_t_1032_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1052_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; uint8_t v___x_1042_; 
v___x_1038_ = lean_box(1);
v___x_1039_ = lean_unsigned_to_nat(0u);
v___x_1040_ = lean_array_get_size(v_items_1034_);
v___x_1041_ = ((lean_object*)(l_Lake_Toml_decodeArray___redArg___closed__9));
v___x_1042_ = lean_nat_dec_lt(v___x_1039_, v___x_1040_);
if (v___x_1042_ == 0)
{
lean_object* v___x_1044_; 
lean_dec_ref(v_items_1034_);
lean_dec_ref(v_dec_1031_);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 1, v_a_1033_);
lean_ctor_set(v___x_1036_, 0, v___x_1038_);
v___x_1044_ = v___x_1036_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v___x_1038_);
lean_ctor_set(v_reuseFailAlloc_1045_, 1, v_a_1033_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
else
{
lean_object* v___f_1046_; lean_object* v___x_1047_; size_t v___x_1048_; size_t v___x_1049_; lean_object* v___x_145__overap_1050_; lean_object* v___x_1051_; 
lean_del_object(v___x_1036_);
v___f_1046_ = lean_alloc_closure((void*)(l_Lake_Toml_Table_decodeNameMap___redArg___lam__1), 4, 1);
lean_closure_set(v___f_1046_, 0, v_dec_1031_);
v___x_1047_ = ((lean_object*)(l_Lake_Toml_Table_decodeNameMap___redArg___closed__0));
v___x_1048_ = ((size_t)0ULL);
v___x_1049_ = lean_usize_of_nat(v___x_1040_);
v___x_145__overap_1050_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1041_, v___f_1046_, v_items_1034_, v___x_1048_, v___x_1049_, v___x_1047_);
v___x_1051_ = lean_apply_1(v___x_145__overap_1050_, v_a_1033_);
return v___x_1051_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decodeNameMap(lean_object* v_00_u03b1_1054_, lean_object* v_dec_1055_, lean_object* v_t_1056_, lean_object* v_a_1057_){
_start:
{
lean_object* v___x_1058_; 
v___x_1058_ = l_Lake_Toml_Table_decodeNameMap___redArg(v_dec_1055_, v_t_1056_, v_a_1057_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_instDecodeTomlNameMap___redArg___lam__0(lean_object* v_inst_1059_, lean_object* v_x_1060_, lean_object* v___y_1061_){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = l_Lake_Toml_Value_decodeTable(v_x_1060_, v___y_1061_);
if (lean_obj_tag(v___x_1062_) == 0)
{
lean_object* v_a_1063_; lean_object* v_a_1064_; lean_object* v___x_1065_; 
v_a_1063_ = lean_ctor_get(v___x_1062_, 0);
lean_inc(v_a_1063_);
v_a_1064_ = lean_ctor_get(v___x_1062_, 1);
lean_inc(v_a_1064_);
lean_dec_ref_known(v___x_1062_, 2);
v___x_1065_ = l_Lake_Toml_Table_decodeNameMap___redArg(v_inst_1059_, v_a_1063_, v_a_1064_);
return v___x_1065_;
}
else
{
lean_object* v_a_1066_; lean_object* v_a_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1074_; 
lean_dec_ref(v_inst_1059_);
v_a_1066_ = lean_ctor_get(v___x_1062_, 0);
v_a_1067_ = lean_ctor_get(v___x_1062_, 1);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1069_ = v___x_1062_;
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_a_1067_);
lean_inc(v_a_1066_);
lean_dec(v___x_1062_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1072_; 
if (v_isShared_1070_ == 0)
{
v___x_1072_ = v___x_1069_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v_a_1066_);
lean_ctor_set(v_reuseFailAlloc_1073_, 1, v_a_1067_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_instDecodeTomlNameMap___redArg(lean_object* v_inst_1075_){
_start:
{
lean_object* v___f_1076_; 
v___f_1076_ = lean_alloc_closure((void*)(l_Lake_Toml_Table_instDecodeTomlNameMap___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1076_, 0, v_inst_1075_);
return v___f_1076_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_instDecodeTomlNameMap(lean_object* v_00_u03b1_1077_, lean_object* v_inst_1078_){
_start:
{
lean_object* v___f_1079_; 
v___f_1079_ = lean_alloc_closure((void*)(l_Lake_Toml_Table_instDecodeTomlNameMap___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1079_, 0, v_inst_1078_);
return v___f_1079_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_tryDecode___redArg(lean_object* v_inst_1080_, lean_object* v_dec_1081_, lean_object* v_t_1082_, lean_object* v_k_1083_, lean_object* v_ref_1084_, lean_object* v_a_1085_){
_start:
{
lean_object* v___x_1086_; 
lean_inc(v_k_1083_);
v___x_1086_ = l_Lake_Toml_Table_decodeValue(v_t_1082_, v_k_1083_, v_ref_1084_, v_a_1085_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v_a_1087_; lean_object* v_a_1088_; lean_object* v___x_1089_; 
v_a_1087_ = lean_ctor_get(v___x_1086_, 0);
lean_inc(v_a_1087_);
v_a_1088_ = lean_ctor_get(v___x_1086_, 1);
lean_inc(v_a_1088_);
lean_dec_ref_known(v___x_1086_, 2);
v___x_1089_ = l_Lake_Toml_decodeKeyval___redArg(v_dec_1081_, v_k_1083_, v_a_1087_, v_a_1088_);
if (lean_obj_tag(v___x_1089_) == 0)
{
lean_object* v_a_1090_; lean_object* v_a_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1098_; 
lean_dec(v_inst_1080_);
v_a_1090_ = lean_ctor_get(v___x_1089_, 0);
v_a_1091_ = lean_ctor_get(v___x_1089_, 1);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1093_ = v___x_1089_;
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_a_1091_);
lean_inc(v_a_1090_);
lean_dec(v___x_1089_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1096_; 
if (v_isShared_1094_ == 0)
{
v___x_1096_ = v___x_1093_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_a_1090_);
lean_ctor_set(v_reuseFailAlloc_1097_, 1, v_a_1091_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
else
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1106_; 
v_a_1099_ = lean_ctor_get(v___x_1089_, 1);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1106_ == 0)
{
lean_object* v_unused_1107_; 
v_unused_1107_ = lean_ctor_get(v___x_1089_, 0);
lean_dec(v_unused_1107_);
v___x_1101_ = v___x_1089_;
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1089_);
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
lean_ctor_set(v___x_1101_, 0, v_inst_1080_);
v___x_1104_ = v___x_1101_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_inst_1080_);
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
else
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1115_; 
lean_dec(v_k_1083_);
lean_dec_ref(v_dec_1081_);
v_a_1108_ = lean_ctor_get(v___x_1086_, 1);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1115_ == 0)
{
lean_object* v_unused_1116_; 
v_unused_1116_ = lean_ctor_get(v___x_1086_, 0);
lean_dec(v_unused_1116_);
v___x_1110_ = v___x_1086_;
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1086_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1113_; 
if (v_isShared_1111_ == 0)
{
lean_ctor_set_tag(v___x_1110_, 0);
lean_ctor_set(v___x_1110_, 0, v_inst_1080_);
v___x_1113_ = v___x_1110_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_inst_1080_);
lean_ctor_set(v_reuseFailAlloc_1114_, 1, v_a_1108_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_tryDecode(lean_object* v_00_u03b1_1117_, lean_object* v_inst_1118_, lean_object* v_dec_1119_, lean_object* v_t_1120_, lean_object* v_k_1121_, lean_object* v_ref_1122_, lean_object* v_a_1123_){
_start:
{
lean_object* v___x_1124_; 
lean_inc(v_k_1121_);
v___x_1124_ = l_Lake_Toml_Table_decodeValue(v_t_1120_, v_k_1121_, v_ref_1122_, v_a_1123_);
if (lean_obj_tag(v___x_1124_) == 0)
{
lean_object* v_a_1125_; lean_object* v_a_1126_; lean_object* v___x_1127_; 
v_a_1125_ = lean_ctor_get(v___x_1124_, 0);
lean_inc(v_a_1125_);
v_a_1126_ = lean_ctor_get(v___x_1124_, 1);
lean_inc(v_a_1126_);
lean_dec_ref_known(v___x_1124_, 2);
v___x_1127_ = l_Lake_Toml_decodeKeyval___redArg(v_dec_1119_, v_k_1121_, v_a_1125_, v_a_1126_);
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_object* v_a_1128_; lean_object* v_a_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1136_; 
lean_dec(v_inst_1118_);
v_a_1128_ = lean_ctor_get(v___x_1127_, 0);
v_a_1129_ = lean_ctor_get(v___x_1127_, 1);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1131_ = v___x_1127_;
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_a_1129_);
lean_inc(v_a_1128_);
lean_dec(v___x_1127_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1134_; 
if (v_isShared_1132_ == 0)
{
v___x_1134_ = v___x_1131_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_a_1128_);
lean_ctor_set(v_reuseFailAlloc_1135_, 1, v_a_1129_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
}
else
{
lean_object* v_a_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1144_; 
v_a_1137_ = lean_ctor_get(v___x_1127_, 1);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1144_ == 0)
{
lean_object* v_unused_1145_; 
v_unused_1145_ = lean_ctor_get(v___x_1127_, 0);
lean_dec(v_unused_1145_);
v___x_1139_ = v___x_1127_;
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_a_1137_);
lean_dec(v___x_1127_);
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
lean_ctor_set(v___x_1139_, 0, v_inst_1118_);
v___x_1142_ = v___x_1139_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_inst_1118_);
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
else
{
lean_object* v_a_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1153_; 
lean_dec(v_k_1121_);
lean_dec_ref(v_dec_1119_);
v_a_1146_ = lean_ctor_get(v___x_1124_, 1);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1153_ == 0)
{
lean_object* v_unused_1154_; 
v_unused_1154_ = lean_ctor_get(v___x_1124_, 0);
lean_dec(v_unused_1154_);
v___x_1148_ = v___x_1124_;
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_a_1146_);
lean_dec(v___x_1124_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1151_; 
if (v_isShared_1149_ == 0)
{
lean_ctor_set_tag(v___x_1148_, 0);
lean_ctor_set(v___x_1148_, 0, v_inst_1118_);
v___x_1151_ = v___x_1148_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_inst_1118_);
lean_ctor_set(v_reuseFailAlloc_1152_, 1, v_a_1146_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_tryDecode_x3f___redArg(lean_object* v_dec_1155_, lean_object* v_t_1156_, lean_object* v_k_1157_, lean_object* v_a_1158_){
_start:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1159_ = ((lean_object*)(l_Lake_Toml_Table_decodeValue___closed__0));
v___x_1160_ = l_Lake_Toml_RBDict_findEntry_x3f___redArg(v___x_1159_, v_k_1157_, v_t_1156_);
if (lean_obj_tag(v___x_1160_) == 0)
{
lean_object* v___x_1161_; lean_object* v___x_1162_; 
lean_dec_ref(v_dec_1155_);
v___x_1161_ = lean_box(0);
v___x_1162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1161_);
lean_ctor_set(v___x_1162_, 1, v_a_1158_);
return v___x_1162_;
}
else
{
lean_object* v_val_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1191_; 
v_val_1163_ = lean_ctor_get(v___x_1160_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1165_ = v___x_1160_;
v_isShared_1166_ = v_isSharedCheck_1191_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_val_1163_);
lean_dec(v___x_1160_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1191_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v_snd_1167_; lean_object* v___x_1168_; 
v_snd_1167_ = lean_ctor_get(v_val_1163_, 1);
lean_inc(v_snd_1167_);
lean_dec(v_val_1163_);
v___x_1168_ = lean_apply_2(v_dec_1155_, v_snd_1167_, v_a_1158_);
if (lean_obj_tag(v___x_1168_) == 0)
{
lean_object* v_a_1169_; lean_object* v_a_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1180_; 
v_a_1169_ = lean_ctor_get(v___x_1168_, 0);
v_a_1170_ = lean_ctor_get(v___x_1168_, 1);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1172_ = v___x_1168_;
v_isShared_1173_ = v_isSharedCheck_1180_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_a_1170_);
lean_inc(v_a_1169_);
lean_dec(v___x_1168_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1180_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1175_; 
if (v_isShared_1166_ == 0)
{
lean_ctor_set(v___x_1165_, 0, v_a_1169_);
v___x_1175_ = v___x_1165_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_a_1169_);
v___x_1175_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
lean_object* v___x_1177_; 
if (v_isShared_1173_ == 0)
{
lean_ctor_set(v___x_1172_, 0, v___x_1175_);
v___x_1177_ = v___x_1172_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v___x_1175_);
lean_ctor_set(v_reuseFailAlloc_1178_, 1, v_a_1170_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
}
}
else
{
lean_object* v_a_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1189_; 
lean_del_object(v___x_1165_);
v_a_1181_ = lean_ctor_get(v___x_1168_, 1);
v_isSharedCheck_1189_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1189_ == 0)
{
lean_object* v_unused_1190_; 
v_unused_1190_ = lean_ctor_get(v___x_1168_, 0);
lean_dec(v_unused_1190_);
v___x_1183_ = v___x_1168_;
v_isShared_1184_ = v_isSharedCheck_1189_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_a_1181_);
lean_dec(v___x_1168_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1189_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1185_; lean_object* v___x_1187_; 
v___x_1185_ = lean_box(0);
if (v_isShared_1184_ == 0)
{
lean_ctor_set_tag(v___x_1183_, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1185_);
v___x_1187_ = v___x_1183_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v___x_1185_);
lean_ctor_set(v_reuseFailAlloc_1188_, 1, v_a_1181_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_tryDecode_x3f(lean_object* v_00_u03b1_1192_, lean_object* v_dec_1193_, lean_object* v_t_1194_, lean_object* v_k_1195_, lean_object* v_a_1196_){
_start:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1197_ = ((lean_object*)(l_Lake_Toml_Table_decodeValue___closed__0));
v___x_1198_ = l_Lake_Toml_RBDict_findEntry_x3f___redArg(v___x_1197_, v_k_1195_, v_t_1194_);
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_object* v___x_1199_; lean_object* v___x_1200_; 
lean_dec_ref(v_dec_1193_);
v___x_1199_ = lean_box(0);
v___x_1200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1199_);
lean_ctor_set(v___x_1200_, 1, v_a_1196_);
return v___x_1200_;
}
else
{
lean_object* v_val_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1229_; 
v_val_1201_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1203_ = v___x_1198_;
v_isShared_1204_ = v_isSharedCheck_1229_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_val_1201_);
lean_dec(v___x_1198_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1229_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v_snd_1205_; lean_object* v___x_1206_; 
v_snd_1205_ = lean_ctor_get(v_val_1201_, 1);
lean_inc(v_snd_1205_);
lean_dec(v_val_1201_);
v___x_1206_ = lean_apply_2(v_dec_1193_, v_snd_1205_, v_a_1196_);
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_object* v_a_1207_; lean_object* v_a_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1218_; 
v_a_1207_ = lean_ctor_get(v___x_1206_, 0);
v_a_1208_ = lean_ctor_get(v___x_1206_, 1);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1210_ = v___x_1206_;
v_isShared_1211_ = v_isSharedCheck_1218_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_a_1208_);
lean_inc(v_a_1207_);
lean_dec(v___x_1206_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1218_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1213_; 
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 0, v_a_1207_);
v___x_1213_ = v___x_1203_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_a_1207_);
v___x_1213_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
lean_object* v___x_1215_; 
if (v_isShared_1211_ == 0)
{
lean_ctor_set(v___x_1210_, 0, v___x_1213_);
v___x_1215_ = v___x_1210_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v___x_1213_);
lean_ctor_set(v_reuseFailAlloc_1216_, 1, v_a_1208_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
}
else
{
lean_object* v_a_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1227_; 
lean_del_object(v___x_1203_);
v_a_1219_ = lean_ctor_get(v___x_1206_, 1);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1227_ == 0)
{
lean_object* v_unused_1228_; 
v_unused_1228_ = lean_ctor_get(v___x_1206_, 0);
lean_dec(v_unused_1228_);
v___x_1221_ = v___x_1206_;
v_isShared_1222_ = v_isSharedCheck_1227_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_a_1219_);
lean_dec(v___x_1206_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1227_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1223_; lean_object* v___x_1225_; 
v___x_1223_ = lean_box(0);
if (v_isShared_1222_ == 0)
{
lean_ctor_set_tag(v___x_1221_, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1223_);
v___x_1225_ = v___x_1221_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v___x_1223_);
lean_ctor_set(v_reuseFailAlloc_1226_, 1, v_a_1219_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_tryDecodeD___redArg(lean_object* v_dec_1230_, lean_object* v_k_1231_, lean_object* v_default_1232_, lean_object* v_t_1233_, lean_object* v_a_1234_){
_start:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1235_ = ((lean_object*)(l_Lake_Toml_Table_decodeValue___closed__0));
v___x_1236_ = l_Lake_Toml_RBDict_findEntry_x3f___redArg(v___x_1235_, v_k_1231_, v_t_1233_);
if (lean_obj_tag(v___x_1236_) == 0)
{
lean_object* v___x_1237_; 
lean_dec_ref(v_dec_1230_);
v___x_1237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1237_, 0, v_default_1232_);
lean_ctor_set(v___x_1237_, 1, v_a_1234_);
return v___x_1237_;
}
else
{
lean_object* v_val_1238_; lean_object* v_snd_1239_; lean_object* v___x_1240_; 
v_val_1238_ = lean_ctor_get(v___x_1236_, 0);
lean_inc(v_val_1238_);
lean_dec_ref_known(v___x_1236_, 1);
v_snd_1239_ = lean_ctor_get(v_val_1238_, 1);
lean_inc(v_snd_1239_);
lean_dec(v_val_1238_);
v___x_1240_ = lean_apply_2(v_dec_1230_, v_snd_1239_, v_a_1234_);
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_object* v_a_1241_; lean_object* v_a_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1249_; 
lean_dec(v_default_1232_);
v_a_1241_ = lean_ctor_get(v___x_1240_, 0);
v_a_1242_ = lean_ctor_get(v___x_1240_, 1);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1244_ = v___x_1240_;
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_a_1242_);
lean_inc(v_a_1241_);
lean_dec(v___x_1240_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1247_; 
if (v_isShared_1245_ == 0)
{
v___x_1247_ = v___x_1244_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_a_1241_);
lean_ctor_set(v_reuseFailAlloc_1248_, 1, v_a_1242_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
}
else
{
lean_object* v_a_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1257_; 
v_a_1250_ = lean_ctor_get(v___x_1240_, 1);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1257_ == 0)
{
lean_object* v_unused_1258_; 
v_unused_1258_ = lean_ctor_get(v___x_1240_, 0);
lean_dec(v_unused_1258_);
v___x_1252_ = v___x_1240_;
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_a_1250_);
lean_dec(v___x_1240_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1255_; 
if (v_isShared_1253_ == 0)
{
lean_ctor_set_tag(v___x_1252_, 0);
lean_ctor_set(v___x_1252_, 0, v_default_1232_);
v___x_1255_ = v___x_1252_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_default_1232_);
lean_ctor_set(v_reuseFailAlloc_1256_, 1, v_a_1250_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_tryDecodeD(lean_object* v_00_u03b1_1259_, lean_object* v_dec_1260_, lean_object* v_k_1261_, lean_object* v_default_1262_, lean_object* v_t_1263_, lean_object* v_a_1264_){
_start:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1265_ = ((lean_object*)(l_Lake_Toml_Table_decodeValue___closed__0));
v___x_1266_ = l_Lake_Toml_RBDict_findEntry_x3f___redArg(v___x_1265_, v_k_1261_, v_t_1263_);
if (lean_obj_tag(v___x_1266_) == 0)
{
lean_object* v___x_1267_; 
lean_dec_ref(v_dec_1260_);
v___x_1267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1267_, 0, v_default_1262_);
lean_ctor_set(v___x_1267_, 1, v_a_1264_);
return v___x_1267_;
}
else
{
lean_object* v_val_1268_; lean_object* v_snd_1269_; lean_object* v___x_1270_; 
v_val_1268_ = lean_ctor_get(v___x_1266_, 0);
lean_inc(v_val_1268_);
lean_dec_ref_known(v___x_1266_, 1);
v_snd_1269_ = lean_ctor_get(v_val_1268_, 1);
lean_inc(v_snd_1269_);
lean_dec(v_val_1268_);
v___x_1270_ = lean_apply_2(v_dec_1260_, v_snd_1269_, v_a_1264_);
if (lean_obj_tag(v___x_1270_) == 0)
{
lean_object* v_a_1271_; lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1279_; 
lean_dec(v_default_1262_);
v_a_1271_ = lean_ctor_get(v___x_1270_, 0);
v_a_1272_ = lean_ctor_get(v___x_1270_, 1);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1274_ = v___x_1270_;
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_inc(v_a_1271_);
lean_dec(v___x_1270_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1277_; 
if (v_isShared_1275_ == 0)
{
v___x_1277_ = v___x_1274_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_a_1271_);
lean_ctor_set(v_reuseFailAlloc_1278_, 1, v_a_1272_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
}
else
{
lean_object* v_a_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1287_; 
v_a_1280_ = lean_ctor_get(v___x_1270_, 1);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1287_ == 0)
{
lean_object* v_unused_1288_; 
v_unused_1288_ = lean_ctor_get(v___x_1270_, 0);
lean_dec(v_unused_1288_);
v___x_1282_ = v___x_1270_;
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_a_1280_);
lean_dec(v___x_1270_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1285_; 
if (v_isShared_1283_ == 0)
{
lean_ctor_set_tag(v___x_1282_, 0);
lean_ctor_set(v___x_1282_, 0, v_default_1262_);
v___x_1285_ = v___x_1282_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_default_1262_);
lean_ctor_set(v_reuseFailAlloc_1286_, 1, v_a_1280_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
}
}
}
}
lean_object* runtime_initialize_Init_System_FilePath(uint8_t builtin);
lean_object* runtime_initialize_Lake_Toml_Data(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Toml_Decode(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
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
