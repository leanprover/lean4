// Lean compiler output
// Module: Lake.Toml.Encode
// Imports: public import Lake.Util.FilePath public import Lake.Toml.Data.Value
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
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
lean_object* l_Lake_Toml_RBDict_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lake_Toml_Value_table(lean_object*, lean_object*);
lean_object* l_Lake_mkRelPathString(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static const lean_closure_object l_Lake_instToTomlValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lake_instToTomlValue___closed__0 = (const lean_object*)&l_Lake_instToTomlValue___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instToTomlValue = (const lean_object*)&l_Lake_instToTomlValue___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instToTomlString___lam__0(lean_object*);
static const lean_closure_object l_Lake_instToTomlString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instToTomlString___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instToTomlString___closed__0 = (const lean_object*)&l_Lake_instToTomlString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instToTomlString = (const lean_object*)&l_Lake_instToTomlString___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instToTomlFilePath___lam__0(lean_object*);
static const lean_closure_object l_Lake_instToTomlFilePath___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instToTomlFilePath___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instToTomlFilePath___closed__0 = (const lean_object*)&l_Lake_instToTomlFilePath___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instToTomlFilePath = (const lean_object*)&l_Lake_instToTomlFilePath___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instToTomlName___lam__0(lean_object*);
static const lean_closure_object l_Lake_instToTomlName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instToTomlName___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instToTomlName___closed__0 = (const lean_object*)&l_Lake_instToTomlName___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instToTomlName = (const lean_object*)&l_Lake_instToTomlName___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instToTomlInt___lam__0(lean_object*);
static const lean_closure_object l_Lake_instToTomlInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instToTomlInt___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instToTomlInt___closed__0 = (const lean_object*)&l_Lake_instToTomlInt___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instToTomlInt = (const lean_object*)&l_Lake_instToTomlInt___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instToTomlNat___lam__0(lean_object*);
static const lean_closure_object l_Lake_instToTomlNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instToTomlNat___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instToTomlNat___closed__0 = (const lean_object*)&l_Lake_instToTomlNat___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instToTomlNat = (const lean_object*)&l_Lake_instToTomlNat___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instToTomlFloat___lam__0(double);
LEAN_EXPORT lean_object* l_Lake_instToTomlFloat___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_instToTomlFloat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instToTomlFloat___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instToTomlFloat___closed__0 = (const lean_object*)&l_Lake_instToTomlFloat___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instToTomlFloat = (const lean_object*)&l_Lake_instToTomlFloat___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instToTomlBool___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lake_instToTomlBool___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_instToTomlBool___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instToTomlBool___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instToTomlBool___closed__0 = (const lean_object*)&l_Lake_instToTomlBool___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instToTomlBool = (const lean_object*)&l_Lake_instToTomlBool___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instToTomlArray___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instToTomlArray___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instToTomlArray___redArg___lam__1___closed__0 = (const lean_object*)&l_Lake_instToTomlArray___redArg___lam__1___closed__0_value;
static const lean_closure_object l_Lake_instToTomlArray___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instToTomlArray___redArg___lam__1___closed__1 = (const lean_object*)&l_Lake_instToTomlArray___redArg___lam__1___closed__1_value;
static const lean_closure_object l_Lake_instToTomlArray___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instToTomlArray___redArg___lam__1___closed__2 = (const lean_object*)&l_Lake_instToTomlArray___redArg___lam__1___closed__2_value;
static const lean_closure_object l_Lake_instToTomlArray___redArg___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instToTomlArray___redArg___lam__1___closed__3 = (const lean_object*)&l_Lake_instToTomlArray___redArg___lam__1___closed__3_value;
static const lean_closure_object l_Lake_instToTomlArray___redArg___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instToTomlArray___redArg___lam__1___closed__4 = (const lean_object*)&l_Lake_instToTomlArray___redArg___lam__1___closed__4_value;
static const lean_closure_object l_Lake_instToTomlArray___redArg___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instToTomlArray___redArg___lam__1___closed__5 = (const lean_object*)&l_Lake_instToTomlArray___redArg___lam__1___closed__5_value;
static const lean_closure_object l_Lake_instToTomlArray___redArg___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instToTomlArray___redArg___lam__1___closed__6 = (const lean_object*)&l_Lake_instToTomlArray___redArg___lam__1___closed__6_value;
static const lean_ctor_object l_Lake_instToTomlArray___redArg___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instToTomlArray___redArg___lam__1___closed__0_value),((lean_object*)&l_Lake_instToTomlArray___redArg___lam__1___closed__1_value)}};
static const lean_object* l_Lake_instToTomlArray___redArg___lam__1___closed__7 = (const lean_object*)&l_Lake_instToTomlArray___redArg___lam__1___closed__7_value;
static const lean_ctor_object l_Lake_instToTomlArray___redArg___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instToTomlArray___redArg___lam__1___closed__7_value),((lean_object*)&l_Lake_instToTomlArray___redArg___lam__1___closed__2_value),((lean_object*)&l_Lake_instToTomlArray___redArg___lam__1___closed__3_value),((lean_object*)&l_Lake_instToTomlArray___redArg___lam__1___closed__4_value),((lean_object*)&l_Lake_instToTomlArray___redArg___lam__1___closed__5_value)}};
static const lean_object* l_Lake_instToTomlArray___redArg___lam__1___closed__8 = (const lean_object*)&l_Lake_instToTomlArray___redArg___lam__1___closed__8_value;
static const lean_ctor_object l_Lake_instToTomlArray___redArg___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instToTomlArray___redArg___lam__1___closed__8_value),((lean_object*)&l_Lake_instToTomlArray___redArg___lam__1___closed__6_value)}};
static const lean_object* l_Lake_instToTomlArray___redArg___lam__1___closed__9 = (const lean_object*)&l_Lake_instToTomlArray___redArg___lam__1___closed__9_value;
LEAN_EXPORT lean_object* l_Lake_instToTomlArray___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToTomlArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToTomlArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToTomlArrayValue___lam__0(lean_object*);
static const lean_closure_object l_Lake_instToTomlArrayValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instToTomlArrayValue___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instToTomlArrayValue___closed__0 = (const lean_object*)&l_Lake_instToTomlArrayValue___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instToTomlArrayValue = (const lean_object*)&l_Lake_instToTomlArrayValue___closed__0_value;
static const lean_closure_object l_Lake_instToTomlTable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Toml_Value_table, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lake_instToTomlTable___closed__0 = (const lean_object*)&l_Lake_instToTomlTable___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instToTomlTable = (const lean_object*)&l_Lake_instToTomlTable___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fOfToToml___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fOfToToml___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fOfToToml(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_encodeArray_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lake_Toml_encodeArray_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_Toml_encodeArray_x3f___redArg___closed__0 = (const lean_object*)&l_Lake_Toml_encodeArray_x3f___redArg___closed__0_value;
static const lean_ctor_object l_Lake_Toml_encodeArray_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_encodeArray_x3f___redArg___closed__0_value)}};
static const lean_object* l_Lake_Toml_encodeArray_x3f___redArg___closed__1 = (const lean_object*)&l_Lake_Toml_encodeArray_x3f___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Toml_encodeArray_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_encodeArray_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fArray___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fOption___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fOption___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fOption(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fOptionOfToToml___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fOptionOfToToml___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fOptionOfToToml(lean_object*, lean_object*);
static const lean_closure_object l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0 = (const lean_object*)&l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_instSmartInsertOfToToml_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_instSmartInsertTable___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_Toml_instSmartInsertTable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Toml_instSmartInsertTable___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Toml_instSmartInsertTable___closed__0 = (const lean_object*)&l_Lake_Toml_instSmartInsertTable___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Toml_instSmartInsertTable = (const lean_object*)&l_Lake_Toml_instSmartInsertTable___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Toml_instSmartInsertArrayOfToToml___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_instSmartInsertArrayOfToToml___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_instSmartInsertArrayOfToToml(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_instSmartInsertString___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_Toml_instSmartInsertString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Toml_instSmartInsertString___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Toml_instSmartInsertString___closed__0 = (const lean_object*)&l_Lake_Toml_instSmartInsertString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Toml_instSmartInsertString = (const lean_object*)&l_Lake_Toml_instSmartInsertString___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Toml_Table_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Table_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Table_instSmartInsertOptionOfToToml___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Table_instSmartInsertOptionOfToToml___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Table_instSmartInsertOptionOfToToml(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Table_smartInsert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Table_smartInsert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Table_insertD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Table_insertD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToTomlString___lam__0(lean_object* v_s_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_box(0);
v___x_5_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5_, 0, v___x_4_);
lean_ctor_set(v___x_5_, 1, v_s_3_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlFilePath___lam__0(lean_object* v_x_8_){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_9_ = l_Lake_mkRelPathString(v_x_8_);
v___x_10_ = lean_box(0);
v___x_11_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_11_, 0, v___x_10_);
lean_ctor_set(v___x_11_, 1, v___x_9_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlName___lam__0(lean_object* v_x_14_){
_start:
{
uint8_t v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_15_ = 1;
v___x_16_ = l_Lean_Name_toString(v_x_14_, v___x_15_);
v___x_17_ = lean_box(0);
v___x_18_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_18_, 0, v___x_17_);
lean_ctor_set(v___x_18_, 1, v___x_16_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlInt___lam__0(lean_object* v_n_21_){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_22_ = lean_box(0);
v___x_23_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_23_, 0, v___x_22_);
lean_ctor_set(v___x_23_, 1, v_n_21_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlNat___lam__0(lean_object* v_n_26_){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_27_ = lean_box(0);
v___x_28_ = lean_nat_to_int(v_n_26_);
v___x_29_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_29_, 0, v___x_27_);
lean_ctor_set(v___x_29_, 1, v___x_28_);
return v___x_29_;
}
}
lean_object* l_Lake_instToTomlFloat___lam__0(double v_n_32_){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_33_ = lean_box(0);
v___x_34_ = lean_alloc_ctor(2, 1, 8);
lean_ctor_set(v___x_34_, 0, v___x_33_);
lean_ctor_set_float(v___x_34_, sizeof(void*)*1, v_n_32_);
return v___x_34_;
}
}
LEAN_EXPORT void l_Lake_instToTomlFloat___lam__0_0interp(lean_interpreter_value* stack)
{
double v_n_32_ = stack[0].m_float;
lean_object* v_res_35_;
v_res_35_ = l_Lake_instToTomlFloat___lam__0(v_n_32_);
stack->m_obj
 = v_res_35_;
}
LEAN_EXPORT lean_object* l_Lake_instToTomlFloat___lam__0___boxed(lean_object* v_n_36_){
_start:
{
double v_n_boxed_37_; lean_object* v_res_38_; 
v_n_boxed_37_ = lean_unbox_float(v_n_36_);
lean_dec_ref(v_n_36_);
v_res_38_ = l_Lake_instToTomlFloat___lam__0(v_n_boxed_37_);
return v_res_38_;
}
}
lean_object* l_Lake_instToTomlBool___lam__0(uint8_t v_b_41_){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = lean_box(0);
v___x_43_ = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(v___x_43_, 0, v___x_42_);
lean_ctor_set_uint8(v___x_43_, sizeof(void*)*1, v_b_41_);
return v___x_43_;
}
}
LEAN_EXPORT void l_Lake_instToTomlBool___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_b_41_ = stack[0].m_num;
lean_object* v_res_44_;
v_res_44_ = l_Lake_instToTomlBool___lam__0(v_b_41_);
stack->m_obj
 = v_res_44_;
}
LEAN_EXPORT lean_object* l_Lake_instToTomlBool___lam__0___boxed(lean_object* v_b_45_){
_start:
{
uint8_t v_b_boxed_46_; lean_object* v_res_47_; 
v_b_boxed_46_ = lean_unbox(v_b_45_);
v_res_47_ = l_Lake_instToTomlBool___lam__0(v_b_boxed_46_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlArray___redArg___lam__0(lean_object* v_inst_50_, lean_object* v_x_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = lean_apply_1(v_inst_50_, v_x_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlArray___redArg___lam__1(lean_object* v___f_72_, lean_object* v_x_73_){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; size_t v_sz_76_; size_t v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_74_ = lean_box(0);
v___x_75_ = ((lean_object*)(l_Lake_instToTomlArray___redArg___lam__1___closed__9));
v_sz_76_ = lean_array_size(v_x_73_);
v___x_77_ = ((size_t)0ULL);
v___x_78_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_75_, v___f_72_, v_sz_76_, v___x_77_, v_x_73_);
v___x_79_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_79_, 0, v___x_74_);
lean_ctor_set(v___x_79_, 1, v___x_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlArray___redArg(lean_object* v_inst_80_){
_start:
{
lean_object* v___f_81_; lean_object* v___f_82_; 
v___f_81_ = lean_alloc_closure((void*)(l_Lake_instToTomlArray___redArg___lam__0), 2, 1);
lean_closure_set(v___f_81_, 0, v_inst_80_);
v___f_82_ = lean_alloc_closure((void*)(l_Lake_instToTomlArray___redArg___lam__1), 2, 1);
lean_closure_set(v___f_82_, 0, v___f_81_);
return v___f_82_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlArray(lean_object* v_00_u03b1_83_, lean_object* v_inst_84_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = l_Lake_instToTomlArray___redArg(v_inst_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlArrayValue___lam__0(lean_object* v_x_86_){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_87_ = lean_box(0);
v___x_88_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_88_, 0, v___x_87_);
lean_ctor_set(v___x_88_, 1, v_x_86_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fOfToToml___redArg___lam__0(lean_object* v_inst_94_, lean_object* v_v_95_){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_96_ = lean_apply_1(v_inst_94_, v_v_95_);
v___x_97_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fOfToToml___redArg(lean_object* v_inst_98_){
_start:
{
lean_object* v___f_99_; 
v___f_99_ = lean_alloc_closure((void*)(l_Lake_instToToml_x3fOfToToml___redArg___lam__0), 2, 1);
lean_closure_set(v___f_99_, 0, v_inst_98_);
return v___f_99_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fOfToToml(lean_object* v_00_u03b1_100_, lean_object* v_inst_101_){
_start:
{
lean_object* v___f_102_; 
v___f_102_ = lean_alloc_closure((void*)(l_Lake_instToToml_x3fOfToToml___redArg___lam__0), 2, 1);
lean_closure_set(v___f_102_, 0, v_inst_101_);
return v___f_102_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_encodeArray_x3f___redArg___lam__0(lean_object* v_inst_103_, lean_object* v_x1_104_, lean_object* v_x2_105_){
_start:
{
if (lean_obj_tag(v_x1_104_) == 0)
{
lean_dec(v_x2_105_);
lean_dec_ref(v_inst_103_);
return v_x1_104_;
}
else
{
lean_object* v_val_106_; lean_object* v___x_107_; 
v_val_106_ = lean_ctor_get(v_x1_104_, 0);
lean_inc(v_val_106_);
lean_dec_ref_known(v_x1_104_, 1);
v___x_107_ = lean_apply_1(v_inst_103_, v_x2_105_);
if (lean_obj_tag(v___x_107_) == 0)
{
lean_object* v___x_108_; 
lean_dec(v_val_106_);
v___x_108_ = lean_box(0);
return v___x_108_;
}
else
{
lean_object* v_val_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_117_; 
v_val_109_ = lean_ctor_get(v___x_107_, 0);
v_isSharedCheck_117_ = !lean_is_exclusive(v___x_107_);
if (v_isSharedCheck_117_ == 0)
{
v___x_111_ = v___x_107_;
v_isShared_112_ = v_isSharedCheck_117_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_val_109_);
lean_dec(v___x_107_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_117_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_113_; lean_object* v___x_115_; 
v___x_113_ = lean_array_push(v_val_106_, v_val_109_);
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 0, v___x_113_);
v___x_115_ = v___x_111_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v___x_113_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
return v___x_115_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_encodeArray_x3f___redArg(lean_object* v_inst_122_, lean_object* v_as_123_){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; uint8_t v___x_128_; 
v___x_124_ = lean_unsigned_to_nat(0u);
v___x_125_ = ((lean_object*)(l_Lake_Toml_encodeArray_x3f___redArg___closed__1));
v___x_126_ = lean_array_get_size(v_as_123_);
v___x_127_ = ((lean_object*)(l_Lake_instToTomlArray___redArg___lam__1___closed__9));
v___x_128_ = lean_nat_dec_lt(v___x_124_, v___x_126_);
if (v___x_128_ == 0)
{
lean_dec_ref(v_as_123_);
lean_dec_ref(v_inst_122_);
return v___x_125_;
}
else
{
lean_object* v___f_129_; uint8_t v___x_130_; 
v___f_129_ = lean_alloc_closure((void*)(l_Lake_Toml_encodeArray_x3f___redArg___lam__0), 3, 1);
lean_closure_set(v___f_129_, 0, v_inst_122_);
v___x_130_ = lean_nat_dec_le(v___x_126_, v___x_126_);
if (v___x_130_ == 0)
{
if (v___x_128_ == 0)
{
lean_dec_ref(v___f_129_);
lean_dec_ref(v_as_123_);
return v___x_125_;
}
else
{
size_t v___x_131_; size_t v___x_132_; lean_object* v___x_133_; 
v___x_131_ = ((size_t)0ULL);
v___x_132_ = lean_usize_of_nat(v___x_126_);
v___x_133_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_127_, v___f_129_, v_as_123_, v___x_131_, v___x_132_, v___x_125_);
return v___x_133_;
}
}
else
{
size_t v___x_134_; size_t v___x_135_; lean_object* v___x_136_; 
v___x_134_ = ((size_t)0ULL);
v___x_135_ = lean_usize_of_nat(v___x_126_);
v___x_136_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_127_, v___f_129_, v_as_123_, v___x_134_, v___x_135_, v___x_125_);
return v___x_136_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_encodeArray_x3f(lean_object* v_00_u03b1_137_, lean_object* v_inst_138_, lean_object* v_as_139_){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = l_Lake_Toml_encodeArray_x3f___redArg(v_inst_138_, v_as_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fArray___redArg___lam__0(lean_object* v_inst_141_, lean_object* v_as_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = l_Lake_Toml_encodeArray_x3f___redArg(v_inst_141_, v_as_142_);
if (lean_obj_tag(v___x_143_) == 0)
{
lean_object* v___x_144_; 
v___x_144_ = lean_box(0);
return v___x_144_;
}
else
{
lean_object* v_val_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_154_; 
v_val_145_ = lean_ctor_get(v___x_143_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v___x_143_);
if (v_isSharedCheck_154_ == 0)
{
v___x_147_ = v___x_143_;
v_isShared_148_ = v_isSharedCheck_154_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_val_145_);
lean_dec(v___x_143_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_154_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_152_; 
v___x_149_ = lean_box(0);
v___x_150_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_150_, 0, v___x_149_);
lean_ctor_set(v___x_150_, 1, v_val_145_);
if (v_isShared_148_ == 0)
{
lean_ctor_set(v___x_147_, 0, v___x_150_);
v___x_152_ = v___x_147_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v___x_150_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fArray___redArg(lean_object* v_inst_155_){
_start:
{
lean_object* v___f_156_; 
v___f_156_ = lean_alloc_closure((void*)(l_Lake_instToToml_x3fArray___redArg___lam__0), 2, 1);
lean_closure_set(v___f_156_, 0, v_inst_155_);
return v___f_156_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fArray(lean_object* v_00_u03b1_157_, lean_object* v_inst_158_){
_start:
{
lean_object* v___f_159_; 
v___f_159_ = lean_alloc_closure((void*)(l_Lake_instToToml_x3fArray___redArg___lam__0), 2, 1);
lean_closure_set(v___f_159_, 0, v_inst_158_);
return v___f_159_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fOption___redArg___lam__0(lean_object* v_inst_160_, lean_object* v_x_161_){
_start:
{
if (lean_obj_tag(v_x_161_) == 0)
{
lean_object* v___x_162_; 
lean_dec_ref(v_inst_160_);
v___x_162_ = lean_box(0);
return v___x_162_;
}
else
{
lean_object* v_val_163_; lean_object* v___x_164_; 
v_val_163_ = lean_ctor_get(v_x_161_, 0);
lean_inc(v_val_163_);
lean_dec_ref_known(v_x_161_, 1);
v___x_164_ = lean_apply_1(v_inst_160_, v_val_163_);
return v___x_164_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fOption___redArg(lean_object* v_inst_165_){
_start:
{
lean_object* v___f_166_; 
v___f_166_ = lean_alloc_closure((void*)(l_Lake_instToToml_x3fOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_166_, 0, v_inst_165_);
return v___f_166_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fOption(lean_object* v_00_u03b1_167_, lean_object* v_inst_168_){
_start:
{
lean_object* v___f_169_; 
v___f_169_ = lean_alloc_closure((void*)(l_Lake_instToToml_x3fOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_169_, 0, v_inst_168_);
return v___f_169_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fOptionOfToToml___redArg___lam__0(lean_object* v_inst_170_, lean_object* v_x_171_){
_start:
{
if (lean_obj_tag(v_x_171_) == 0)
{
lean_object* v___x_172_; 
lean_dec_ref(v_inst_170_);
v___x_172_ = lean_box(0);
return v___x_172_;
}
else
{
lean_object* v_val_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_181_; 
v_val_173_ = lean_ctor_get(v_x_171_, 0);
v_isSharedCheck_181_ = !lean_is_exclusive(v_x_171_);
if (v_isSharedCheck_181_ == 0)
{
v___x_175_ = v_x_171_;
v_isShared_176_ = v_isSharedCheck_181_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_val_173_);
lean_dec(v_x_171_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_181_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_177_; lean_object* v___x_179_; 
v___x_177_ = lean_apply_1(v_inst_170_, v_val_173_);
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 0, v___x_177_);
v___x_179_ = v___x_175_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v___x_177_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fOptionOfToToml___redArg(lean_object* v_inst_182_){
_start:
{
lean_object* v___f_183_; 
v___f_183_ = lean_alloc_closure((void*)(l_Lake_instToToml_x3fOptionOfToToml___redArg___lam__0), 2, 1);
lean_closure_set(v___f_183_, 0, v_inst_182_);
return v___f_183_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fOptionOfToToml(lean_object* v_00_u03b1_184_, lean_object* v_inst_185_){
_start:
{
lean_object* v___f_186_; 
v___f_186_ = lean_alloc_closure((void*)(l_Lake_instToToml_x3fOptionOfToToml___redArg___lam__0), 2, 1);
lean_closure_set(v___f_186_, 0, v_inst_185_);
return v___f_186_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0(lean_object* v_inst_188_, lean_object* v_k_189_, lean_object* v_v_190_, lean_object* v_t_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = lean_apply_1(v_inst_188_, v_v_190_);
if (lean_obj_tag(v___x_192_) == 1)
{
lean_object* v_val_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v_val_193_ = lean_ctor_get(v___x_192_, 0);
lean_inc(v_val_193_);
lean_dec_ref_known(v___x_192_, 1);
v___x_194_ = ((lean_object*)(l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0));
v___x_195_ = l_Lake_Toml_RBDict_insert___redArg(v___x_194_, v_k_189_, v_val_193_, v_t_191_);
return v___x_195_;
}
else
{
lean_dec(v___x_192_);
lean_dec(v_k_189_);
return v_t_191_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg(lean_object* v_inst_196_){
_start:
{
lean_object* v___f_197_; 
v___f_197_ = lean_alloc_closure((void*)(l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0), 4, 1);
lean_closure_set(v___f_197_, 0, v_inst_196_);
return v___f_197_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instSmartInsertOfToToml_x3f(lean_object* v_00_u03b1_198_, lean_object* v_inst_199_){
_start:
{
lean_object* v___f_200_; 
v___f_200_ = lean_alloc_closure((void*)(l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0), 4, 1);
lean_closure_set(v___f_200_, 0, v_inst_199_);
return v___f_200_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instSmartInsertTable___lam__0(lean_object* v_k_201_, lean_object* v_v_202_, lean_object* v_t_203_){
_start:
{
lean_object* v_items_204_; lean_object* v___x_205_; lean_object* v___x_206_; uint8_t v___x_207_; 
v_items_204_ = lean_ctor_get(v_v_202_, 0);
v___x_205_ = lean_array_get_size(v_items_204_);
v___x_206_ = lean_unsigned_to_nat(0u);
v___x_207_ = lean_nat_dec_eq(v___x_205_, v___x_206_);
if (v___x_207_ == 0)
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_208_ = ((lean_object*)(l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0));
v___x_209_ = lean_box(0);
v___x_210_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
lean_ctor_set(v___x_210_, 1, v_v_202_);
v___x_211_ = l_Lake_Toml_RBDict_insert___redArg(v___x_208_, v_k_201_, v___x_210_, v_t_203_);
return v___x_211_;
}
else
{
lean_dec_ref(v_v_202_);
lean_dec(v_k_201_);
return v_t_203_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instSmartInsertArrayOfToToml___redArg___lam__0(lean_object* v_inst_214_, lean_object* v_k_215_, lean_object* v_v_216_, lean_object* v_t_217_){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; uint8_t v___x_220_; 
v___x_218_ = lean_array_get_size(v_v_216_);
v___x_219_ = lean_unsigned_to_nat(0u);
v___x_220_ = lean_nat_dec_eq(v___x_218_, v___x_219_);
if (v___x_220_ == 0)
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_221_ = ((lean_object*)(l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0));
v___x_222_ = lean_apply_1(v_inst_214_, v_v_216_);
v___x_223_ = l_Lake_Toml_RBDict_insert___redArg(v___x_221_, v_k_215_, v___x_222_, v_t_217_);
return v___x_223_;
}
else
{
lean_dec_ref(v_v_216_);
lean_dec(v_k_215_);
lean_dec_ref(v_inst_214_);
return v_t_217_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instSmartInsertArrayOfToToml___redArg(lean_object* v_inst_224_){
_start:
{
lean_object* v___f_225_; 
v___f_225_ = lean_alloc_closure((void*)(l_Lake_Toml_instSmartInsertArrayOfToToml___redArg___lam__0), 4, 1);
lean_closure_set(v___f_225_, 0, v_inst_224_);
return v___f_225_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instSmartInsertArrayOfToToml(lean_object* v_00_u03b1_226_, lean_object* v_inst_227_){
_start:
{
lean_object* v___f_228_; 
v___f_228_ = lean_alloc_closure((void*)(l_Lake_Toml_instSmartInsertArrayOfToToml___redArg___lam__0), 4, 1);
lean_closure_set(v___f_228_, 0, v_inst_227_);
return v___f_228_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instSmartInsertString___lam__0(lean_object* v_k_229_, lean_object* v_v_230_, lean_object* v_t_231_){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; uint8_t v___x_234_; 
v___x_232_ = lean_string_utf8_byte_size(v_v_230_);
v___x_233_ = lean_unsigned_to_nat(0u);
v___x_234_ = lean_nat_dec_eq(v___x_232_, v___x_233_);
if (v___x_234_ == 0)
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_235_ = ((lean_object*)(l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0));
v___x_236_ = lean_box(0);
v___x_237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
lean_ctor_set(v___x_237_, 1, v_v_230_);
v___x_238_ = l_Lake_Toml_RBDict_insert___redArg(v___x_235_, v_k_229_, v___x_237_, v_t_231_);
return v___x_238_;
}
else
{
lean_dec_ref(v_v_230_);
lean_dec(v_k_229_);
return v_t_231_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_insert___redArg(lean_object* v_enc_241_, lean_object* v_k_242_, lean_object* v_v_243_, lean_object* v_t_244_){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_245_ = ((lean_object*)(l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0));
v___x_246_ = lean_apply_1(v_enc_241_, v_v_243_);
v___x_247_ = l_Lake_Toml_RBDict_insert___redArg(v___x_245_, v_k_242_, v___x_246_, v_t_244_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_insert(lean_object* v_00_u03b1_248_, lean_object* v_enc_249_, lean_object* v_k_250_, lean_object* v_v_251_, lean_object* v_t_252_){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_253_ = ((lean_object*)(l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0));
v___x_254_ = lean_apply_1(v_enc_249_, v_v_251_);
v___x_255_ = l_Lake_Toml_RBDict_insert___redArg(v___x_253_, v_k_250_, v___x_254_, v_t_252_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_instSmartInsertOptionOfToToml___redArg___lam__0(lean_object* v_inst_256_, lean_object* v_k_257_, lean_object* v_v_x3f_258_, lean_object* v_t_259_){
_start:
{
if (lean_obj_tag(v_v_x3f_258_) == 0)
{
lean_dec(v_k_257_);
lean_dec_ref(v_inst_256_);
return v_t_259_;
}
else
{
lean_object* v_val_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v_val_260_ = lean_ctor_get(v_v_x3f_258_, 0);
lean_inc(v_val_260_);
lean_dec_ref_known(v_v_x3f_258_, 1);
v___x_261_ = lean_apply_1(v_inst_256_, v_val_260_);
v___x_262_ = ((lean_object*)(l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0));
v___x_263_ = l_Lake_Toml_RBDict_insert___redArg(v___x_262_, v_k_257_, v___x_261_, v_t_259_);
return v___x_263_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_instSmartInsertOptionOfToToml___redArg(lean_object* v_inst_264_){
_start:
{
lean_object* v___f_265_; 
v___f_265_ = lean_alloc_closure((void*)(l_Lake_Toml_Table_instSmartInsertOptionOfToToml___redArg___lam__0), 4, 1);
lean_closure_set(v___f_265_, 0, v_inst_264_);
return v___f_265_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_instSmartInsertOptionOfToToml(lean_object* v_00_u03b1_266_, lean_object* v_inst_267_){
_start:
{
lean_object* v___f_268_; 
v___f_268_ = lean_alloc_closure((void*)(l_Lake_Toml_Table_instSmartInsertOptionOfToToml___redArg___lam__0), 4, 1);
lean_closure_set(v___f_268_, 0, v_inst_267_);
return v___f_268_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_smartInsert___redArg(lean_object* v_inst_269_, lean_object* v_k_270_, lean_object* v_v_271_, lean_object* v_t_272_){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = lean_apply_3(v_inst_269_, v_k_270_, v_v_271_, v_t_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_smartInsert(lean_object* v_00_u03b1_274_, lean_object* v_inst_275_, lean_object* v_k_276_, lean_object* v_v_277_, lean_object* v_t_278_){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = lean_apply_3(v_inst_275_, v_k_276_, v_v_277_, v_t_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_insertD___redArg(lean_object* v_enc_280_, lean_object* v_inst_281_, lean_object* v_k_282_, lean_object* v_v_283_, lean_object* v_default_284_, lean_object* v_t_285_){
_start:
{
lean_object* v___x_286_; uint8_t v___x_287_; 
lean_inc(v_v_283_);
v___x_286_ = lean_apply_2(v_inst_281_, v_v_283_, v_default_284_);
v___x_287_ = lean_unbox(v___x_286_);
if (v___x_287_ == 0)
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_288_ = ((lean_object*)(l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0));
v___x_289_ = lean_apply_1(v_enc_280_, v_v_283_);
v___x_290_ = l_Lake_Toml_RBDict_insert___redArg(v___x_288_, v_k_282_, v___x_289_, v_t_285_);
return v___x_290_;
}
else
{
lean_dec(v_v_283_);
lean_dec(v_k_282_);
lean_dec_ref(v_enc_280_);
return v_t_285_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_insertD(lean_object* v_00_u03b1_291_, lean_object* v_enc_292_, lean_object* v_inst_293_, lean_object* v_k_294_, lean_object* v_v_295_, lean_object* v_default_296_, lean_object* v_t_297_){
_start:
{
lean_object* v___x_298_; uint8_t v___x_299_; 
lean_inc(v_v_295_);
v___x_298_ = lean_apply_2(v_inst_293_, v_v_295_, v_default_296_);
v___x_299_ = lean_unbox(v___x_298_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_300_ = ((lean_object*)(l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0));
v___x_301_ = lean_apply_1(v_enc_292_, v_v_295_);
v___x_302_ = l_Lake_Toml_RBDict_insert___redArg(v___x_300_, v_k_294_, v___x_301_, v_t_297_);
return v___x_302_;
}
else
{
lean_dec(v_v_295_);
lean_dec(v_k_294_);
lean_dec_ref(v_enc_292_);
return v_t_297_;
}
}
}
lean_object* runtime_initialize_Lake_Util_FilePath(uint8_t builtin);
lean_object* runtime_initialize_Lake_Toml_Data_Value(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Toml_Encode(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lake_Util_FilePath(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Toml_Data_Value(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Toml_Encode(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Util_FilePath(uint8_t builtin);
lean_object* initialize_Lake_Toml_Data_Value(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Toml_Encode(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Util_FilePath(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Toml_Data_Value(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Toml_Encode(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Toml_Encode(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Toml_Encode(builtin);
}
#ifdef __cplusplus
}
#endif
