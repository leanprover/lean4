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
lean_object* l_id___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instToTomlValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lake_instToTomlValue___closed__0 = (const lean_object*)&l_Lake_instToTomlValue___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instToTomlValue = (const lean_object*)&l_Lake_instToTomlValue___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instToTomlString___lam__0(lean_object*);
static const lean_closure_object l_Lake_instToTomlString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instToTomlString___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instToTomlString___closed__0 = (const lean_object*)&l_Lake_instToTomlString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instToTomlString = (const lean_object*)&l_Lake_instToTomlString___closed__0_value;
lean_object* l_Lake_mkRelPathString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToTomlFilePath___lam__0(lean_object*);
static const lean_closure_object l_Lake_instToTomlFilePath___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instToTomlFilePath___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instToTomlFilePath___closed__0 = (const lean_object*)&l_Lake_instToTomlFilePath___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instToTomlFilePath = (const lean_object*)&l_Lake_instToTomlFilePath___closed__0_value;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_instToTomlName___lam__0(lean_object*);
static const lean_closure_object l_Lake_instToTomlName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instToTomlName___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instToTomlName___closed__0 = (const lean_object*)&l_Lake_instToTomlName___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instToTomlName = (const lean_object*)&l_Lake_instToTomlName___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instToTomlInt___lam__0(lean_object*);
static const lean_closure_object l_Lake_instToTomlInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instToTomlInt___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instToTomlInt___closed__0 = (const lean_object*)&l_Lake_instToTomlInt___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instToTomlInt = (const lean_object*)&l_Lake_instToTomlInt___closed__0_value;
lean_object* lean_nat_to_int(lean_object*);
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
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_instToTomlArray___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instToTomlArray___redArg___lam__1___closed__0 = (const lean_object*)&l_Lake_instToTomlArray___redArg___lam__1___closed__0_value;
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_instToTomlArray___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instToTomlArray___redArg___lam__1___closed__1 = (const lean_object*)&l_Lake_instToTomlArray___redArg___lam__1___closed__1_value;
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instToTomlArray___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instToTomlArray___redArg___lam__1___closed__2 = (const lean_object*)&l_Lake_instToTomlArray___redArg___lam__1___closed__2_value;
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_instToTomlArray___redArg___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instToTomlArray___redArg___lam__1___closed__3 = (const lean_object*)&l_Lake_instToTomlArray___redArg___lam__1___closed__3_value;
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_instToTomlArray___redArg___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instToTomlArray___redArg___lam__1___closed__4 = (const lean_object*)&l_Lake_instToTomlArray___redArg___lam__1___closed__4_value;
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_instToTomlArray___redArg___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instToTomlArray___redArg___lam__1___closed__5 = (const lean_object*)&l_Lake_instToTomlArray___redArg___lam__1___closed__5_value;
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_instToTomlArray___redArg___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instToTomlArray___redArg___lam__1___closed__6 = (const lean_object*)&l_Lake_instToTomlArray___redArg___lam__1___closed__6_value;
static const lean_ctor_object l_Lake_instToTomlArray___redArg___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instToTomlArray___redArg___lam__1___closed__0_value),((lean_object*)&l_Lake_instToTomlArray___redArg___lam__1___closed__1_value)}};
static const lean_object* l_Lake_instToTomlArray___redArg___lam__1___closed__7 = (const lean_object*)&l_Lake_instToTomlArray___redArg___lam__1___closed__7_value;
static const lean_ctor_object l_Lake_instToTomlArray___redArg___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instToTomlArray___redArg___lam__1___closed__7_value),((lean_object*)&l_Lake_instToTomlArray___redArg___lam__1___closed__2_value),((lean_object*)&l_Lake_instToTomlArray___redArg___lam__1___closed__3_value),((lean_object*)&l_Lake_instToTomlArray___redArg___lam__1___closed__4_value),((lean_object*)&l_Lake_instToTomlArray___redArg___lam__1___closed__5_value)}};
static const lean_object* l_Lake_instToTomlArray___redArg___lam__1___closed__8 = (const lean_object*)&l_Lake_instToTomlArray___redArg___lam__1___closed__8_value;
static const lean_ctor_object l_Lake_instToTomlArray___redArg___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instToTomlArray___redArg___lam__1___closed__8_value),((lean_object*)&l_Lake_instToTomlArray___redArg___lam__1___closed__6_value)}};
static const lean_object* l_Lake_instToTomlArray___redArg___lam__1___closed__9 = (const lean_object*)&l_Lake_instToTomlArray___redArg___lam__1___closed__9_value;
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToTomlArray___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToTomlArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToTomlArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToTomlArrayValue___lam__0(lean_object*);
static const lean_closure_object l_Lake_instToTomlArrayValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instToTomlArrayValue___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instToTomlArrayValue___closed__0 = (const lean_object*)&l_Lake_instToTomlArrayValue___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instToTomlArrayValue = (const lean_object*)&l_Lake_instToTomlArrayValue___closed__0_value;
lean_object* l_Lake_Toml_Value_table(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instToTomlTable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Toml_Value_table, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lake_instToTomlTable___closed__0 = (const lean_object*)&l_Lake_instToTomlTable___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instToTomlTable = (const lean_object*)&l_Lake_instToTomlTable___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fOfToToml___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fOfToToml___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fOfToToml(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_encodeArray_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lake_Toml_encodeArray_x3f___redArg___closed__0;
static lean_object* l_Lake_Toml_encodeArray_x3f___redArg___closed__1;
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
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
lean_object* l_Lean_Name_quickCmp___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_quickCmp___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0 = (const lean_object*)&l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0_value;
lean_object* l_Lake_Toml_RBDict_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_instSmartInsertOfToToml_x3f(lean_object*, lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_instSmartInsertTable___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_Toml_instSmartInsertTable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Toml_instSmartInsertTable___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Toml_instSmartInsertTable___closed__0 = (const lean_object*)&l_Lake_Toml_instSmartInsertTable___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Toml_instSmartInsertTable = (const lean_object*)&l_Lake_Toml_instSmartInsertTable___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Toml_instSmartInsertArrayOfToToml___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_instSmartInsertArrayOfToToml___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_instSmartInsertArrayOfToToml(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_instToTomlString___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlFilePath___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lake_mkRelPathString(x_1);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlName___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = 1;
x_3 = l_Lean_Name_toString(x_1, x_2);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlInt___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlNat___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = lean_nat_to_int(x_1);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlFloat___lam__0(double x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(2, 1, 8);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_float(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlFloat___lam__0___boxed(lean_object* x_1) {
_start:
{
double x_2; lean_object* x_3; 
x_2 = lean_unbox_float(x_1);
lean_dec_ref(x_1);
x_3 = l_Lake_instToTomlFloat___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlBool___lam__0(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlBool___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lake_instToTomlBool___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlArray___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlArray___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_box(0);
x_4 = ((lean_object*)(l_Lake_instToTomlArray___redArg___lam__1___closed__9));
x_5 = lean_array_size(x_2);
x_6 = 0;
x_7 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_4, x_1, x_5, x_6, x_2);
x_8 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlArray___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_closure((void*)(l_Lake_instToTomlArray___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_alloc_closure((void*)(l_Lake_instToTomlArray___redArg___lam__1), 2, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlArray(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_instToTomlArray___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlArrayValue___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fOfToToml___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_apply_1(x_1, x_2);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fOfToToml___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_instToToml_x3fOfToToml___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fOfToToml(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_instToToml_x3fOfToToml___redArg___lam__0), 2, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_encodeArray_x3f___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_3);
lean_dec_ref(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lean_apply_1(x_1, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
lean_dec(x_4);
x_6 = lean_box(0);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_array_push(x_4, x_8);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_array_push(x_4, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
}
}
static lean_object* _init_l_Lake_Toml_encodeArray_x3f___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_encodeArray_x3f___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_encodeArray_x3f___redArg___closed__0;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_encodeArray_x3f___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lake_Toml_encodeArray_x3f___redArg___closed__1;
x_5 = lean_array_get_size(x_2);
x_6 = ((lean_object*)(l_Lake_instToTomlArray___redArg___lam__1___closed__9));
x_7 = lean_nat_dec_lt(x_3, x_5);
if (x_7 == 0)
{
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_4;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_alloc_closure((void*)(l_Lake_Toml_encodeArray_x3f___redArg___lam__0), 3, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = lean_nat_dec_le(x_5, x_5);
if (x_9 == 0)
{
if (x_7 == 0)
{
lean_dec_ref(x_8);
lean_dec_ref(x_2);
return x_4;
}
else
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = 0;
x_11 = lean_usize_of_nat(x_5);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_6, x_8, x_2, x_10, x_11, x_4);
return x_12;
}
}
else
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = 0;
x_14 = lean_usize_of_nat(x_5);
x_15 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_6, x_8, x_2, x_13, x_14, x_4);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_encodeArray_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Toml_encodeArray_x3f___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fArray___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Toml_encodeArray_x3f___redArg(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fArray___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_instToToml_x3fArray___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fArray(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_instToToml_x3fArray___redArg___lam__0), 2, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fOption___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fOption___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_instToToml_x3fOption___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fOption(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_instToToml_x3fOption___redArg___lam__0), 2, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fOptionOfToToml___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
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
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_apply_1(x_1, x_5);
lean_ctor_set(x_2, 0, x_6);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_apply_1(x_1, x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fOptionOfToToml___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_instToToml_x3fOptionOfToToml___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fOptionOfToToml(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_instToToml_x3fOptionOfToToml___redArg___lam__0), 2, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_1(x_1, x_3);
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = ((lean_object*)(l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0));
x_8 = l_Lake_Toml_RBDict_insert___redArg(x_7, x_2, x_6, x_4);
return x_8;
}
else
{
lean_dec(x_5);
lean_dec(x_2);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0), 4, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instSmartInsertOfToToml_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0), 4, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instSmartInsertTable___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Array_isEmpty___redArg(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = ((lean_object*)(l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0));
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_2);
x_9 = l_Lake_Toml_RBDict_insert___redArg(x_6, x_1, x_8, x_3);
return x_9;
}
else
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instSmartInsertArrayOfToToml___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Array_isEmpty___redArg(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = ((lean_object*)(l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0));
x_7 = lean_apply_1(x_1, x_3);
x_8 = l_Lake_Toml_RBDict_insert___redArg(x_6, x_2, x_7, x_4);
return x_8;
}
else
{
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instSmartInsertArrayOfToToml___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_Toml_instSmartInsertArrayOfToToml___redArg___lam__0), 4, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instSmartInsertArrayOfToToml(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_Toml_instSmartInsertArrayOfToToml___redArg___lam__0), 4, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instSmartInsertString___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_string_utf8_byte_size(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = ((lean_object*)(l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0));
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_2);
x_10 = l_Lake_Toml_RBDict_insert___redArg(x_7, x_1, x_9, x_3);
return x_10;
}
else
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_insert___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = ((lean_object*)(l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0));
x_6 = lean_apply_1(x_1, x_3);
x_7 = l_Lake_Toml_RBDict_insert___redArg(x_5, x_2, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_insert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = ((lean_object*)(l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0));
x_7 = lean_apply_1(x_2, x_4);
x_8 = l_Lake_Toml_RBDict_insert___redArg(x_6, x_3, x_7, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_instSmartInsertOptionOfToToml___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = lean_apply_1(x_1, x_5);
x_7 = ((lean_object*)(l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0));
x_8 = l_Lake_Toml_RBDict_insert___redArg(x_7, x_2, x_6, x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_instSmartInsertOptionOfToToml___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_Toml_Table_instSmartInsertOptionOfToToml___redArg___lam__0), 4, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_instSmartInsertOptionOfToToml(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_Toml_Table_instSmartInsertOptionOfToToml___redArg___lam__0), 4, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_smartInsert___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_3(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_smartInsert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_3(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_insertD___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
lean_inc(x_4);
x_7 = lean_apply_2(x_2, x_4, x_5);
x_8 = lean_unbox(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = ((lean_object*)(l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0));
x_10 = lean_apply_1(x_1, x_4);
x_11 = l_Lake_Toml_RBDict_insert___redArg(x_9, x_3, x_10, x_6);
return x_11;
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_insertD(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
lean_inc(x_5);
x_8 = lean_apply_2(x_3, x_5, x_6);
x_9 = lean_unbox(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = ((lean_object*)(l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0));
x_11 = lean_apply_1(x_2, x_5);
x_12 = l_Lake_Toml_RBDict_insert___redArg(x_10, x_4, x_11, x_7);
return x_12;
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
return x_7;
}
}
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
l_Lake_Toml_encodeArray_x3f___redArg___closed__0 = _init_l_Lake_Toml_encodeArray_x3f___redArg___closed__0();
lean_mark_persistent(l_Lake_Toml_encodeArray_x3f___redArg___closed__0);
l_Lake_Toml_encodeArray_x3f___redArg___closed__1 = _init_l_Lake_Toml_encodeArray_x3f___redArg___closed__1();
lean_mark_persistent(l_Lake_Toml_encodeArray_x3f___redArg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
