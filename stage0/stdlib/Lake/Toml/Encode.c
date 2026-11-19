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
lean_dec_ref_known(v_x1_102_, 1);
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
lean_object* v___f_127_; size_t v___x_128_; size_t v___x_129_; lean_object* v___x_130_; 
v___f_127_ = lean_alloc_closure((void*)(l_Lake_Toml_encodeArray_x3f___redArg___lam__0), 3, 1);
lean_closure_set(v___f_127_, 0, v_inst_120_);
v___x_128_ = ((size_t)0ULL);
v___x_129_ = lean_usize_of_nat(v___x_124_);
v___x_130_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_125_, v___f_127_, v_as_121_, v___x_128_, v___x_129_, v___x_123_);
return v___x_130_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_encodeArray_x3f(lean_object* v_00_u03b1_131_, lean_object* v_inst_132_, lean_object* v_as_133_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = l_Lake_Toml_encodeArray_x3f___redArg(v_inst_132_, v_as_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fArray___redArg___lam__0(lean_object* v_inst_135_, lean_object* v_as_136_){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = l_Lake_Toml_encodeArray_x3f___redArg(v_inst_135_, v_as_136_);
if (lean_obj_tag(v___x_137_) == 0)
{
lean_object* v___x_138_; 
v___x_138_ = lean_box(0);
return v___x_138_;
}
else
{
lean_object* v_val_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_148_; 
v_val_139_ = lean_ctor_get(v___x_137_, 0);
v_isSharedCheck_148_ = !lean_is_exclusive(v___x_137_);
if (v_isSharedCheck_148_ == 0)
{
v___x_141_ = v___x_137_;
v_isShared_142_ = v_isSharedCheck_148_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_val_139_);
lean_dec(v___x_137_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_148_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_146_; 
v___x_143_ = lean_box(0);
v___x_144_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
lean_ctor_set(v___x_144_, 1, v_val_139_);
if (v_isShared_142_ == 0)
{
lean_ctor_set(v___x_141_, 0, v___x_144_);
v___x_146_ = v___x_141_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v___x_144_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
return v___x_146_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fArray___redArg(lean_object* v_inst_149_){
_start:
{
lean_object* v___f_150_; 
v___f_150_ = lean_alloc_closure((void*)(l_Lake_instToToml_x3fArray___redArg___lam__0), 2, 1);
lean_closure_set(v___f_150_, 0, v_inst_149_);
return v___f_150_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fArray(lean_object* v_00_u03b1_151_, lean_object* v_inst_152_){
_start:
{
lean_object* v___f_153_; 
v___f_153_ = lean_alloc_closure((void*)(l_Lake_instToToml_x3fArray___redArg___lam__0), 2, 1);
lean_closure_set(v___f_153_, 0, v_inst_152_);
return v___f_153_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fOption___redArg___lam__0(lean_object* v_inst_154_, lean_object* v_x_155_){
_start:
{
if (lean_obj_tag(v_x_155_) == 0)
{
lean_object* v___x_156_; 
lean_dec_ref(v_inst_154_);
v___x_156_ = lean_box(0);
return v___x_156_;
}
else
{
lean_object* v_val_157_; lean_object* v___x_158_; 
v_val_157_ = lean_ctor_get(v_x_155_, 0);
lean_inc(v_val_157_);
lean_dec_ref_known(v_x_155_, 1);
v___x_158_ = lean_apply_1(v_inst_154_, v_val_157_);
return v___x_158_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fOption___redArg(lean_object* v_inst_159_){
_start:
{
lean_object* v___f_160_; 
v___f_160_ = lean_alloc_closure((void*)(l_Lake_instToToml_x3fOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_160_, 0, v_inst_159_);
return v___f_160_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fOption(lean_object* v_00_u03b1_161_, lean_object* v_inst_162_){
_start:
{
lean_object* v___f_163_; 
v___f_163_ = lean_alloc_closure((void*)(l_Lake_instToToml_x3fOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_163_, 0, v_inst_162_);
return v___f_163_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fOptionOfToToml___redArg___lam__0(lean_object* v_inst_164_, lean_object* v_x_165_){
_start:
{
if (lean_obj_tag(v_x_165_) == 0)
{
lean_object* v___x_166_; 
lean_dec_ref(v_inst_164_);
v___x_166_ = lean_box(0);
return v___x_166_;
}
else
{
lean_object* v_val_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_175_; 
v_val_167_ = lean_ctor_get(v_x_165_, 0);
v_isSharedCheck_175_ = !lean_is_exclusive(v_x_165_);
if (v_isSharedCheck_175_ == 0)
{
v___x_169_ = v_x_165_;
v_isShared_170_ = v_isSharedCheck_175_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_val_167_);
lean_dec(v_x_165_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_175_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___x_171_; lean_object* v___x_173_; 
v___x_171_ = lean_apply_1(v_inst_164_, v_val_167_);
if (v_isShared_170_ == 0)
{
lean_ctor_set(v___x_169_, 0, v___x_171_);
v___x_173_ = v___x_169_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v___x_171_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fOptionOfToToml___redArg(lean_object* v_inst_176_){
_start:
{
lean_object* v___f_177_; 
v___f_177_ = lean_alloc_closure((void*)(l_Lake_instToToml_x3fOptionOfToToml___redArg___lam__0), 2, 1);
lean_closure_set(v___f_177_, 0, v_inst_176_);
return v___f_177_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fOptionOfToToml(lean_object* v_00_u03b1_178_, lean_object* v_inst_179_){
_start:
{
lean_object* v___f_180_; 
v___f_180_ = lean_alloc_closure((void*)(l_Lake_instToToml_x3fOptionOfToToml___redArg___lam__0), 2, 1);
lean_closure_set(v___f_180_, 0, v_inst_179_);
return v___f_180_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0(lean_object* v_inst_182_, lean_object* v_k_183_, lean_object* v_v_184_, lean_object* v_t_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = lean_apply_1(v_inst_182_, v_v_184_);
if (lean_obj_tag(v___x_186_) == 1)
{
lean_object* v_val_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v_val_187_ = lean_ctor_get(v___x_186_, 0);
lean_inc(v_val_187_);
lean_dec_ref_known(v___x_186_, 1);
v___x_188_ = ((lean_object*)(l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0));
v___x_189_ = l_Lake_Toml_RBDict_insert___redArg(v___x_188_, v_k_183_, v_val_187_, v_t_185_);
return v___x_189_;
}
else
{
lean_dec(v___x_186_);
lean_dec(v_k_183_);
return v_t_185_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg(lean_object* v_inst_190_){
_start:
{
lean_object* v___f_191_; 
v___f_191_ = lean_alloc_closure((void*)(l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0), 4, 1);
lean_closure_set(v___f_191_, 0, v_inst_190_);
return v___f_191_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instSmartInsertOfToToml_x3f(lean_object* v_00_u03b1_192_, lean_object* v_inst_193_){
_start:
{
lean_object* v___f_194_; 
v___f_194_ = lean_alloc_closure((void*)(l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0), 4, 1);
lean_closure_set(v___f_194_, 0, v_inst_193_);
return v___f_194_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instSmartInsertTable___lam__0(lean_object* v_k_195_, lean_object* v_v_196_, lean_object* v_t_197_){
_start:
{
lean_object* v_items_198_; lean_object* v___x_199_; lean_object* v___x_200_; uint8_t v___x_201_; 
v_items_198_ = lean_ctor_get(v_v_196_, 0);
v___x_199_ = lean_array_get_size(v_items_198_);
v___x_200_ = lean_unsigned_to_nat(0u);
v___x_201_ = lean_nat_dec_eq(v___x_199_, v___x_200_);
if (v___x_201_ == 0)
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_202_ = ((lean_object*)(l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0));
v___x_203_ = lean_box(0);
v___x_204_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
lean_ctor_set(v___x_204_, 1, v_v_196_);
v___x_205_ = l_Lake_Toml_RBDict_insert___redArg(v___x_202_, v_k_195_, v___x_204_, v_t_197_);
return v___x_205_;
}
else
{
lean_dec_ref(v_v_196_);
lean_dec(v_k_195_);
return v_t_197_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instSmartInsertArrayOfToToml___redArg___lam__0(lean_object* v_inst_208_, lean_object* v_k_209_, lean_object* v_v_210_, lean_object* v_t_211_){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; uint8_t v___x_214_; 
v___x_212_ = lean_array_get_size(v_v_210_);
v___x_213_ = lean_unsigned_to_nat(0u);
v___x_214_ = lean_nat_dec_eq(v___x_212_, v___x_213_);
if (v___x_214_ == 0)
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_215_ = ((lean_object*)(l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0));
v___x_216_ = lean_apply_1(v_inst_208_, v_v_210_);
v___x_217_ = l_Lake_Toml_RBDict_insert___redArg(v___x_215_, v_k_209_, v___x_216_, v_t_211_);
return v___x_217_;
}
else
{
lean_dec_ref(v_v_210_);
lean_dec(v_k_209_);
lean_dec_ref(v_inst_208_);
return v_t_211_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instSmartInsertArrayOfToToml___redArg(lean_object* v_inst_218_){
_start:
{
lean_object* v___f_219_; 
v___f_219_ = lean_alloc_closure((void*)(l_Lake_Toml_instSmartInsertArrayOfToToml___redArg___lam__0), 4, 1);
lean_closure_set(v___f_219_, 0, v_inst_218_);
return v___f_219_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instSmartInsertArrayOfToToml(lean_object* v_00_u03b1_220_, lean_object* v_inst_221_){
_start:
{
lean_object* v___f_222_; 
v___f_222_ = lean_alloc_closure((void*)(l_Lake_Toml_instSmartInsertArrayOfToToml___redArg___lam__0), 4, 1);
lean_closure_set(v___f_222_, 0, v_inst_221_);
return v___f_222_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instSmartInsertString___lam__0(lean_object* v_k_223_, lean_object* v_v_224_, lean_object* v_t_225_){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; uint8_t v___x_228_; 
v___x_226_ = lean_string_utf8_byte_size(v_v_224_);
v___x_227_ = lean_unsigned_to_nat(0u);
v___x_228_ = lean_nat_dec_eq(v___x_226_, v___x_227_);
if (v___x_228_ == 0)
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_229_ = ((lean_object*)(l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0));
v___x_230_ = lean_box(0);
v___x_231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
lean_ctor_set(v___x_231_, 1, v_v_224_);
v___x_232_ = l_Lake_Toml_RBDict_insert___redArg(v___x_229_, v_k_223_, v___x_231_, v_t_225_);
return v___x_232_;
}
else
{
lean_dec_ref(v_v_224_);
lean_dec(v_k_223_);
return v_t_225_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_insert___redArg(lean_object* v_enc_235_, lean_object* v_k_236_, lean_object* v_v_237_, lean_object* v_t_238_){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_239_ = ((lean_object*)(l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0));
v___x_240_ = lean_apply_1(v_enc_235_, v_v_237_);
v___x_241_ = l_Lake_Toml_RBDict_insert___redArg(v___x_239_, v_k_236_, v___x_240_, v_t_238_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_insert(lean_object* v_00_u03b1_242_, lean_object* v_enc_243_, lean_object* v_k_244_, lean_object* v_v_245_, lean_object* v_t_246_){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_247_ = ((lean_object*)(l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0));
v___x_248_ = lean_apply_1(v_enc_243_, v_v_245_);
v___x_249_ = l_Lake_Toml_RBDict_insert___redArg(v___x_247_, v_k_244_, v___x_248_, v_t_246_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_instSmartInsertOptionOfToToml___redArg___lam__0(lean_object* v_inst_250_, lean_object* v_k_251_, lean_object* v_v_x3f_252_, lean_object* v_t_253_){
_start:
{
if (lean_obj_tag(v_v_x3f_252_) == 0)
{
lean_dec(v_k_251_);
lean_dec_ref(v_inst_250_);
return v_t_253_;
}
else
{
lean_object* v_val_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v_val_254_ = lean_ctor_get(v_v_x3f_252_, 0);
lean_inc(v_val_254_);
lean_dec_ref_known(v_v_x3f_252_, 1);
v___x_255_ = lean_apply_1(v_inst_250_, v_val_254_);
v___x_256_ = ((lean_object*)(l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0));
v___x_257_ = l_Lake_Toml_RBDict_insert___redArg(v___x_256_, v_k_251_, v___x_255_, v_t_253_);
return v___x_257_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_instSmartInsertOptionOfToToml___redArg(lean_object* v_inst_258_){
_start:
{
lean_object* v___f_259_; 
v___f_259_ = lean_alloc_closure((void*)(l_Lake_Toml_Table_instSmartInsertOptionOfToToml___redArg___lam__0), 4, 1);
lean_closure_set(v___f_259_, 0, v_inst_258_);
return v___f_259_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_instSmartInsertOptionOfToToml(lean_object* v_00_u03b1_260_, lean_object* v_inst_261_){
_start:
{
lean_object* v___f_262_; 
v___f_262_ = lean_alloc_closure((void*)(l_Lake_Toml_Table_instSmartInsertOptionOfToToml___redArg___lam__0), 4, 1);
lean_closure_set(v___f_262_, 0, v_inst_261_);
return v___f_262_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_smartInsert___redArg(lean_object* v_inst_263_, lean_object* v_k_264_, lean_object* v_v_265_, lean_object* v_t_266_){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = lean_apply_3(v_inst_263_, v_k_264_, v_v_265_, v_t_266_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_smartInsert(lean_object* v_00_u03b1_268_, lean_object* v_inst_269_, lean_object* v_k_270_, lean_object* v_v_271_, lean_object* v_t_272_){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = lean_apply_3(v_inst_269_, v_k_270_, v_v_271_, v_t_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_insertD___redArg(lean_object* v_enc_274_, lean_object* v_inst_275_, lean_object* v_k_276_, lean_object* v_v_277_, lean_object* v_default_278_, lean_object* v_t_279_){
_start:
{
lean_object* v___x_280_; uint8_t v___x_281_; 
lean_inc(v_v_277_);
v___x_280_ = lean_apply_2(v_inst_275_, v_v_277_, v_default_278_);
v___x_281_ = lean_unbox(v___x_280_);
if (v___x_281_ == 0)
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_282_ = ((lean_object*)(l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0));
v___x_283_ = lean_apply_1(v_enc_274_, v_v_277_);
v___x_284_ = l_Lake_Toml_RBDict_insert___redArg(v___x_282_, v_k_276_, v___x_283_, v_t_279_);
return v___x_284_;
}
else
{
lean_dec(v_v_277_);
lean_dec(v_k_276_);
lean_dec_ref(v_enc_274_);
return v_t_279_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_insertD(lean_object* v_00_u03b1_285_, lean_object* v_enc_286_, lean_object* v_inst_287_, lean_object* v_k_288_, lean_object* v_v_289_, lean_object* v_default_290_, lean_object* v_t_291_){
_start:
{
lean_object* v___x_292_; uint8_t v___x_293_; 
lean_inc(v_v_289_);
v___x_292_ = lean_apply_2(v_inst_287_, v_v_289_, v_default_290_);
v___x_293_ = lean_unbox(v___x_292_);
if (v___x_293_ == 0)
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_294_ = ((lean_object*)(l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0));
v___x_295_ = lean_apply_1(v_enc_286_, v_v_289_);
v___x_296_ = l_Lake_Toml_RBDict_insert___redArg(v___x_294_, v_k_288_, v___x_295_, v_t_291_);
return v___x_296_;
}
else
{
lean_dec(v_v_289_);
lean_dec(v_k_288_);
lean_dec_ref(v_enc_286_);
return v_t_291_;
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
