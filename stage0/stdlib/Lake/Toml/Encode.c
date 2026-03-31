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
LEAN_EXPORT lean_object* l_Lake_instToTomlFloat___lam__0(double v_n_32_){
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
LEAN_EXPORT lean_object* l_Lake_instToTomlFloat___lam__0___boxed(lean_object* v_n_35_){
_start:
{
double v_n_boxed_36_; lean_object* v_res_37_; 
v_n_boxed_36_ = lean_unbox_float(v_n_35_);
lean_dec_ref(v_n_35_);
v_res_37_ = l_Lake_instToTomlFloat___lam__0(v_n_boxed_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlBool___lam__0(uint8_t v_b_40_){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_41_ = lean_box(0);
v___x_42_ = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(v___x_42_, 0, v___x_41_);
lean_ctor_set_uint8(v___x_42_, sizeof(void*)*1, v_b_40_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlBool___lam__0___boxed(lean_object* v_b_43_){
_start:
{
uint8_t v_b_boxed_44_; lean_object* v_res_45_; 
v_b_boxed_44_ = lean_unbox(v_b_43_);
v_res_45_ = l_Lake_instToTomlBool___lam__0(v_b_boxed_44_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlArray___redArg___lam__0(lean_object* v_inst_48_, lean_object* v_x_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = lean_apply_1(v_inst_48_, v_x_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlArray___redArg___lam__1(lean_object* v___f_70_, lean_object* v_x_71_){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; size_t v_sz_74_; size_t v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_72_ = lean_box(0);
v___x_73_ = ((lean_object*)(l_Lake_instToTomlArray___redArg___lam__1___closed__9));
v_sz_74_ = lean_array_size(v_x_71_);
v___x_75_ = ((size_t)0ULL);
v___x_76_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_73_, v___f_70_, v_sz_74_, v___x_75_, v_x_71_);
v___x_77_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_77_, 0, v___x_72_);
lean_ctor_set(v___x_77_, 1, v___x_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlArray___redArg(lean_object* v_inst_78_){
_start:
{
lean_object* v___f_79_; lean_object* v___f_80_; 
v___f_79_ = lean_alloc_closure((void*)(l_Lake_instToTomlArray___redArg___lam__0), 2, 1);
lean_closure_set(v___f_79_, 0, v_inst_78_);
v___f_80_ = lean_alloc_closure((void*)(l_Lake_instToTomlArray___redArg___lam__1), 2, 1);
lean_closure_set(v___f_80_, 0, v___f_79_);
return v___f_80_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlArray(lean_object* v_00_u03b1_81_, lean_object* v_inst_82_){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = l_Lake_instToTomlArray___redArg(v_inst_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlArrayValue___lam__0(lean_object* v_x_84_){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_85_ = lean_box(0);
v___x_86_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_86_, 0, v___x_85_);
lean_ctor_set(v___x_86_, 1, v_x_84_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fOfToToml___redArg___lam__0(lean_object* v_inst_92_, lean_object* v_v_93_){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_94_ = lean_apply_1(v_inst_92_, v_v_93_);
v___x_95_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_95_, 0, v___x_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fOfToToml___redArg(lean_object* v_inst_96_){
_start:
{
lean_object* v___f_97_; 
v___f_97_ = lean_alloc_closure((void*)(l_Lake_instToToml_x3fOfToToml___redArg___lam__0), 2, 1);
lean_closure_set(v___f_97_, 0, v_inst_96_);
return v___f_97_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fOfToToml(lean_object* v_00_u03b1_98_, lean_object* v_inst_99_){
_start:
{
lean_object* v___f_100_; 
v___f_100_ = lean_alloc_closure((void*)(l_Lake_instToToml_x3fOfToToml___redArg___lam__0), 2, 1);
lean_closure_set(v___f_100_, 0, v_inst_99_);
return v___f_100_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_encodeArray_x3f___redArg___lam__0(lean_object* v_inst_101_, lean_object* v_x1_102_, lean_object* v_x2_103_){
_start:
{
if (lean_obj_tag(v_x1_102_) == 0)
{
lean_dec(v_x2_103_);
lean_dec_ref(v_inst_101_);
return v_x1_102_;
}
else
{
lean_object* v_val_104_; lean_object* v___x_105_; 
v_val_104_ = lean_ctor_get(v_x1_102_, 0);
lean_inc(v_val_104_);
lean_dec_ref(v_x1_102_);
v___x_105_ = lean_apply_1(v_inst_101_, v_x2_103_);
if (lean_obj_tag(v___x_105_) == 0)
{
lean_object* v___x_106_; 
lean_dec(v_val_104_);
v___x_106_ = lean_box(0);
return v___x_106_;
}
else
{
lean_object* v_val_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_115_; 
v_val_107_ = lean_ctor_get(v___x_105_, 0);
v_isSharedCheck_115_ = !lean_is_exclusive(v___x_105_);
if (v_isSharedCheck_115_ == 0)
{
v___x_109_ = v___x_105_;
v_isShared_110_ = v_isSharedCheck_115_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_val_107_);
lean_dec(v___x_105_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_115_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_111_; lean_object* v___x_113_; 
v___x_111_ = lean_array_push(v_val_104_, v_val_107_);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 0, v___x_111_);
v___x_113_ = v___x_109_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v___x_111_);
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
}
LEAN_EXPORT lean_object* l_Lake_Toml_encodeArray_x3f___redArg(lean_object* v_inst_120_, lean_object* v_as_121_){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; uint8_t v___x_126_; 
v___x_122_ = lean_unsigned_to_nat(0u);
v___x_123_ = ((lean_object*)(l_Lake_Toml_encodeArray_x3f___redArg___closed__1));
v___x_124_ = lean_array_get_size(v_as_121_);
v___x_125_ = ((lean_object*)(l_Lake_instToTomlArray___redArg___lam__1___closed__9));
v___x_126_ = lean_nat_dec_lt(v___x_122_, v___x_124_);
if (v___x_126_ == 0)
{
lean_dec_ref(v_as_121_);
lean_dec_ref(v_inst_120_);
return v___x_123_;
}
else
{
lean_object* v___f_127_; uint8_t v___x_128_; 
v___f_127_ = lean_alloc_closure((void*)(l_Lake_Toml_encodeArray_x3f___redArg___lam__0), 3, 1);
lean_closure_set(v___f_127_, 0, v_inst_120_);
v___x_128_ = lean_nat_dec_le(v___x_124_, v___x_124_);
if (v___x_128_ == 0)
{
if (v___x_126_ == 0)
{
lean_dec_ref(v___f_127_);
lean_dec_ref(v_as_121_);
return v___x_123_;
}
else
{
size_t v___x_129_; size_t v___x_130_; lean_object* v___x_131_; 
v___x_129_ = ((size_t)0ULL);
v___x_130_ = lean_usize_of_nat(v___x_124_);
v___x_131_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_125_, v___f_127_, v_as_121_, v___x_129_, v___x_130_, v___x_123_);
return v___x_131_;
}
}
else
{
size_t v___x_132_; size_t v___x_133_; lean_object* v___x_134_; 
v___x_132_ = ((size_t)0ULL);
v___x_133_ = lean_usize_of_nat(v___x_124_);
v___x_134_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_125_, v___f_127_, v_as_121_, v___x_132_, v___x_133_, v___x_123_);
return v___x_134_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_encodeArray_x3f(lean_object* v_00_u03b1_135_, lean_object* v_inst_136_, lean_object* v_as_137_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l_Lake_Toml_encodeArray_x3f___redArg(v_inst_136_, v_as_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fArray___redArg___lam__0(lean_object* v_inst_139_, lean_object* v_as_140_){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = l_Lake_Toml_encodeArray_x3f___redArg(v_inst_139_, v_as_140_);
if (lean_obj_tag(v___x_141_) == 0)
{
lean_object* v___x_142_; 
v___x_142_ = lean_box(0);
return v___x_142_;
}
else
{
lean_object* v_val_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_152_; 
v_val_143_ = lean_ctor_get(v___x_141_, 0);
v_isSharedCheck_152_ = !lean_is_exclusive(v___x_141_);
if (v_isSharedCheck_152_ == 0)
{
v___x_145_ = v___x_141_;
v_isShared_146_ = v_isSharedCheck_152_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_val_143_);
lean_dec(v___x_141_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_152_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_150_; 
v___x_147_ = lean_box(0);
v___x_148_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_148_, 0, v___x_147_);
lean_ctor_set(v___x_148_, 1, v_val_143_);
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 0, v___x_148_);
v___x_150_ = v___x_145_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v___x_148_);
v___x_150_ = v_reuseFailAlloc_151_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
return v___x_150_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fArray___redArg(lean_object* v_inst_153_){
_start:
{
lean_object* v___f_154_; 
v___f_154_ = lean_alloc_closure((void*)(l_Lake_instToToml_x3fArray___redArg___lam__0), 2, 1);
lean_closure_set(v___f_154_, 0, v_inst_153_);
return v___f_154_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fArray(lean_object* v_00_u03b1_155_, lean_object* v_inst_156_){
_start:
{
lean_object* v___f_157_; 
v___f_157_ = lean_alloc_closure((void*)(l_Lake_instToToml_x3fArray___redArg___lam__0), 2, 1);
lean_closure_set(v___f_157_, 0, v_inst_156_);
return v___f_157_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fOption___redArg___lam__0(lean_object* v_inst_158_, lean_object* v_x_159_){
_start:
{
if (lean_obj_tag(v_x_159_) == 0)
{
lean_object* v___x_160_; 
lean_dec_ref(v_inst_158_);
v___x_160_ = lean_box(0);
return v___x_160_;
}
else
{
lean_object* v_val_161_; lean_object* v___x_162_; 
v_val_161_ = lean_ctor_get(v_x_159_, 0);
lean_inc(v_val_161_);
lean_dec_ref(v_x_159_);
v___x_162_ = lean_apply_1(v_inst_158_, v_val_161_);
return v___x_162_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fOption___redArg(lean_object* v_inst_163_){
_start:
{
lean_object* v___f_164_; 
v___f_164_ = lean_alloc_closure((void*)(l_Lake_instToToml_x3fOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_164_, 0, v_inst_163_);
return v___f_164_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fOption(lean_object* v_00_u03b1_165_, lean_object* v_inst_166_){
_start:
{
lean_object* v___f_167_; 
v___f_167_ = lean_alloc_closure((void*)(l_Lake_instToToml_x3fOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_167_, 0, v_inst_166_);
return v___f_167_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fOptionOfToToml___redArg___lam__0(lean_object* v_inst_168_, lean_object* v_x_169_){
_start:
{
if (lean_obj_tag(v_x_169_) == 0)
{
lean_object* v___x_170_; 
lean_dec_ref(v_inst_168_);
v___x_170_ = lean_box(0);
return v___x_170_;
}
else
{
lean_object* v_val_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_179_; 
v_val_171_ = lean_ctor_get(v_x_169_, 0);
v_isSharedCheck_179_ = !lean_is_exclusive(v_x_169_);
if (v_isSharedCheck_179_ == 0)
{
v___x_173_ = v_x_169_;
v_isShared_174_ = v_isSharedCheck_179_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_val_171_);
lean_dec(v_x_169_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_179_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_175_; lean_object* v___x_177_; 
v___x_175_ = lean_apply_1(v_inst_168_, v_val_171_);
if (v_isShared_174_ == 0)
{
lean_ctor_set(v___x_173_, 0, v___x_175_);
v___x_177_ = v___x_173_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v___x_175_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
return v___x_177_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fOptionOfToToml___redArg(lean_object* v_inst_180_){
_start:
{
lean_object* v___f_181_; 
v___f_181_ = lean_alloc_closure((void*)(l_Lake_instToToml_x3fOptionOfToToml___redArg___lam__0), 2, 1);
lean_closure_set(v___f_181_, 0, v_inst_180_);
return v___f_181_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fOptionOfToToml(lean_object* v_00_u03b1_182_, lean_object* v_inst_183_){
_start:
{
lean_object* v___f_184_; 
v___f_184_ = lean_alloc_closure((void*)(l_Lake_instToToml_x3fOptionOfToToml___redArg___lam__0), 2, 1);
lean_closure_set(v___f_184_, 0, v_inst_183_);
return v___f_184_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0(lean_object* v_inst_186_, lean_object* v_k_187_, lean_object* v_v_188_, lean_object* v_t_189_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = lean_apply_1(v_inst_186_, v_v_188_);
if (lean_obj_tag(v___x_190_) == 1)
{
lean_object* v_val_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v_val_191_ = lean_ctor_get(v___x_190_, 0);
lean_inc(v_val_191_);
lean_dec_ref(v___x_190_);
v___x_192_ = ((lean_object*)(l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0));
v___x_193_ = l_Lake_Toml_RBDict_insert___redArg(v___x_192_, v_k_187_, v_val_191_, v_t_189_);
return v___x_193_;
}
else
{
lean_dec(v___x_190_);
lean_dec(v_k_187_);
return v_t_189_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg(lean_object* v_inst_194_){
_start:
{
lean_object* v___f_195_; 
v___f_195_ = lean_alloc_closure((void*)(l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0), 4, 1);
lean_closure_set(v___f_195_, 0, v_inst_194_);
return v___f_195_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instSmartInsertOfToToml_x3f(lean_object* v_00_u03b1_196_, lean_object* v_inst_197_){
_start:
{
lean_object* v___f_198_; 
v___f_198_ = lean_alloc_closure((void*)(l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0), 4, 1);
lean_closure_set(v___f_198_, 0, v_inst_197_);
return v___f_198_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instSmartInsertTable___lam__0(lean_object* v_k_199_, lean_object* v_v_200_, lean_object* v_t_201_){
_start:
{
lean_object* v_items_202_; lean_object* v___x_203_; lean_object* v___x_204_; uint8_t v___x_205_; 
v_items_202_ = lean_ctor_get(v_v_200_, 0);
v___x_203_ = lean_array_get_size(v_items_202_);
v___x_204_ = lean_unsigned_to_nat(0u);
v___x_205_ = lean_nat_dec_eq(v___x_203_, v___x_204_);
if (v___x_205_ == 0)
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_206_ = ((lean_object*)(l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0));
v___x_207_ = lean_box(0);
v___x_208_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
lean_ctor_set(v___x_208_, 1, v_v_200_);
v___x_209_ = l_Lake_Toml_RBDict_insert___redArg(v___x_206_, v_k_199_, v___x_208_, v_t_201_);
return v___x_209_;
}
else
{
lean_dec_ref(v_v_200_);
lean_dec(v_k_199_);
return v_t_201_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instSmartInsertArrayOfToToml___redArg___lam__0(lean_object* v_inst_212_, lean_object* v_k_213_, lean_object* v_v_214_, lean_object* v_t_215_){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; uint8_t v___x_218_; 
v___x_216_ = lean_array_get_size(v_v_214_);
v___x_217_ = lean_unsigned_to_nat(0u);
v___x_218_ = lean_nat_dec_eq(v___x_216_, v___x_217_);
if (v___x_218_ == 0)
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_219_ = ((lean_object*)(l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0));
v___x_220_ = lean_apply_1(v_inst_212_, v_v_214_);
v___x_221_ = l_Lake_Toml_RBDict_insert___redArg(v___x_219_, v_k_213_, v___x_220_, v_t_215_);
return v___x_221_;
}
else
{
lean_dec_ref(v_v_214_);
lean_dec(v_k_213_);
lean_dec_ref(v_inst_212_);
return v_t_215_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instSmartInsertArrayOfToToml___redArg(lean_object* v_inst_222_){
_start:
{
lean_object* v___f_223_; 
v___f_223_ = lean_alloc_closure((void*)(l_Lake_Toml_instSmartInsertArrayOfToToml___redArg___lam__0), 4, 1);
lean_closure_set(v___f_223_, 0, v_inst_222_);
return v___f_223_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instSmartInsertArrayOfToToml(lean_object* v_00_u03b1_224_, lean_object* v_inst_225_){
_start:
{
lean_object* v___f_226_; 
v___f_226_ = lean_alloc_closure((void*)(l_Lake_Toml_instSmartInsertArrayOfToToml___redArg___lam__0), 4, 1);
lean_closure_set(v___f_226_, 0, v_inst_225_);
return v___f_226_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instSmartInsertString___lam__0(lean_object* v_k_227_, lean_object* v_v_228_, lean_object* v_t_229_){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; uint8_t v___x_232_; 
v___x_230_ = lean_string_utf8_byte_size(v_v_228_);
v___x_231_ = lean_unsigned_to_nat(0u);
v___x_232_ = lean_nat_dec_eq(v___x_230_, v___x_231_);
if (v___x_232_ == 0)
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_233_ = ((lean_object*)(l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0));
v___x_234_ = lean_box(0);
v___x_235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
lean_ctor_set(v___x_235_, 1, v_v_228_);
v___x_236_ = l_Lake_Toml_RBDict_insert___redArg(v___x_233_, v_k_227_, v___x_235_, v_t_229_);
return v___x_236_;
}
else
{
lean_dec_ref(v_v_228_);
lean_dec(v_k_227_);
return v_t_229_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_insert___redArg(lean_object* v_enc_239_, lean_object* v_k_240_, lean_object* v_v_241_, lean_object* v_t_242_){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_243_ = ((lean_object*)(l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0));
v___x_244_ = lean_apply_1(v_enc_239_, v_v_241_);
v___x_245_ = l_Lake_Toml_RBDict_insert___redArg(v___x_243_, v_k_240_, v___x_244_, v_t_242_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_insert(lean_object* v_00_u03b1_246_, lean_object* v_enc_247_, lean_object* v_k_248_, lean_object* v_v_249_, lean_object* v_t_250_){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_251_ = ((lean_object*)(l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0));
v___x_252_ = lean_apply_1(v_enc_247_, v_v_249_);
v___x_253_ = l_Lake_Toml_RBDict_insert___redArg(v___x_251_, v_k_248_, v___x_252_, v_t_250_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_instSmartInsertOptionOfToToml___redArg___lam__0(lean_object* v_inst_254_, lean_object* v_k_255_, lean_object* v_v_x3f_256_, lean_object* v_t_257_){
_start:
{
if (lean_obj_tag(v_v_x3f_256_) == 0)
{
lean_dec(v_k_255_);
lean_dec_ref(v_inst_254_);
return v_t_257_;
}
else
{
lean_object* v_val_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v_val_258_ = lean_ctor_get(v_v_x3f_256_, 0);
lean_inc(v_val_258_);
lean_dec_ref(v_v_x3f_256_);
v___x_259_ = lean_apply_1(v_inst_254_, v_val_258_);
v___x_260_ = ((lean_object*)(l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0));
v___x_261_ = l_Lake_Toml_RBDict_insert___redArg(v___x_260_, v_k_255_, v___x_259_, v_t_257_);
return v___x_261_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_instSmartInsertOptionOfToToml___redArg(lean_object* v_inst_262_){
_start:
{
lean_object* v___f_263_; 
v___f_263_ = lean_alloc_closure((void*)(l_Lake_Toml_Table_instSmartInsertOptionOfToToml___redArg___lam__0), 4, 1);
lean_closure_set(v___f_263_, 0, v_inst_262_);
return v___f_263_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_instSmartInsertOptionOfToToml(lean_object* v_00_u03b1_264_, lean_object* v_inst_265_){
_start:
{
lean_object* v___f_266_; 
v___f_266_ = lean_alloc_closure((void*)(l_Lake_Toml_Table_instSmartInsertOptionOfToToml___redArg___lam__0), 4, 1);
lean_closure_set(v___f_266_, 0, v_inst_265_);
return v___f_266_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_smartInsert___redArg(lean_object* v_inst_267_, lean_object* v_k_268_, lean_object* v_v_269_, lean_object* v_t_270_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = lean_apply_3(v_inst_267_, v_k_268_, v_v_269_, v_t_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_smartInsert(lean_object* v_00_u03b1_272_, lean_object* v_inst_273_, lean_object* v_k_274_, lean_object* v_v_275_, lean_object* v_t_276_){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = lean_apply_3(v_inst_273_, v_k_274_, v_v_275_, v_t_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_insertD___redArg(lean_object* v_enc_278_, lean_object* v_inst_279_, lean_object* v_k_280_, lean_object* v_v_281_, lean_object* v_default_282_, lean_object* v_t_283_){
_start:
{
lean_object* v___x_284_; uint8_t v___x_285_; 
lean_inc(v_v_281_);
v___x_284_ = lean_apply_2(v_inst_279_, v_v_281_, v_default_282_);
v___x_285_ = lean_unbox(v___x_284_);
if (v___x_285_ == 0)
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_286_ = ((lean_object*)(l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0));
v___x_287_ = lean_apply_1(v_enc_278_, v_v_281_);
v___x_288_ = l_Lake_Toml_RBDict_insert___redArg(v___x_286_, v_k_280_, v___x_287_, v_t_283_);
return v___x_288_;
}
else
{
lean_dec(v_v_281_);
lean_dec(v_k_280_);
lean_dec_ref(v_enc_278_);
return v_t_283_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_insertD(lean_object* v_00_u03b1_289_, lean_object* v_enc_290_, lean_object* v_inst_291_, lean_object* v_k_292_, lean_object* v_v_293_, lean_object* v_default_294_, lean_object* v_t_295_){
_start:
{
lean_object* v___x_296_; uint8_t v___x_297_; 
lean_inc(v_v_293_);
v___x_296_ = lean_apply_2(v_inst_291_, v_v_293_, v_default_294_);
v___x_297_ = lean_unbox(v___x_296_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_298_ = ((lean_object*)(l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0));
v___x_299_ = lean_apply_1(v_enc_290_, v_v_293_);
v___x_300_ = l_Lake_Toml_RBDict_insert___redArg(v___x_298_, v_k_292_, v___x_299_, v_t_295_);
return v___x_300_;
}
else
{
lean_dec(v_v_293_);
lean_dec(v_k_292_);
lean_dec_ref(v_enc_290_);
return v_t_295_;
}
}
}
lean_object* runtime_initialize_Lake_Util_FilePath(uint8_t builtin);
lean_object* runtime_initialize_Lake_Toml_Data_Value(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Toml_Encode(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
