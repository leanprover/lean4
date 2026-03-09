// Lean compiler output
// Module: Lake.CLI.Translate.Toml
// Imports: public import Lake.Toml.Encode public import Lake.Config.Package meta import Lake.Config.LeanLibConfig meta import Lake.Config.LeanExeConfig meta import Lake.Config.InputFileConfig meta import Lake.Config.PackageConfig
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
lean_object* l_System_FilePath_normalize(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_CLI_Translate_Toml_0__Lake_instBEqFilePath__lake___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_instBEqFilePath__lake___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_CLI_Translate_Toml_0__Lake_instBEqFilePath__lake___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_CLI_Translate_Toml_0__Lake_instBEqFilePath__lake___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_instBEqFilePath__lake___closed__0 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_instBEqFilePath__lake___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_instBEqFilePath__lake = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_instBEqFilePath__lake___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_instEncodeFieldOfToToml___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_instEncodeFieldOfToToml___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_instEncodeFieldOfToToml(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_instEncodeFieldOfToToml___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_Toml_Table_insertField___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_Toml_Table_insertField(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_Toml_Table_insertField___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfSmartInsertOfConfigField___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfSmartInsertOfConfigField___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfSmartInsertOfConfigField(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0_value;
lean_object* l_Lake_Toml_RBDict_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_StdVer_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToTomlLeanVer___lam__0(lean_object*);
static const lean_closure_object l_Lake_instToTomlLeanVer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instToTomlLeanVer___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instToTomlLeanVer___closed__0 = (const lean_object*)&l_Lake_instToTomlLeanVer___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instToTomlLeanVer = (const lean_object*)&l_Lake_instToTomlLeanVer___closed__0_value;
lean_object* l_Lake_BuildType_toString(uint8_t);
LEAN_EXPORT lean_object* l_Lake_instToTomlBuildType___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lake_instToTomlBuildType___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_instToTomlBuildType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instToTomlBuildType___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instToTomlBuildType___closed__0 = (const lean_object*)&l_Lake_instToTomlBuildType___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instToTomlBuildType = (const lean_object*)&l_Lake_instToTomlBuildType___closed__0_value;
lean_object* l_Lake_Glob_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToTomlGlob___lam__0(lean_object*);
static const lean_closure_object l_Lake_instToTomlGlob___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instToTomlGlob___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instToTomlGlob___closed__0 = (const lean_object*)&l_Lake_instToTomlGlob___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instToTomlGlob = (const lean_object*)&l_Lake_instToTomlGlob___closed__0_value;
lean_object* l_Lake_Backend_toString(uint8_t);
LEAN_EXPORT lean_object* l_Lake_instToTomlBackend___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lake_instToTomlBackend___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_instToTomlBackend___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instToTomlBackend___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instToTomlBackend___closed__0 = (const lean_object*)&l_Lake_instToTomlBackend___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instToTomlBackend = (const lean_object*)&l_Lake_instToTomlBackend___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instSmartInsertBackend___lam__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instSmartInsertBackend___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_instSmartInsertBackend___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instSmartInsertBackend___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instSmartInsertBackend___closed__0 = (const lean_object*)&l_Lake_instSmartInsertBackend___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instSmartInsertBackend = (const lean_object*)&l_Lake_instSmartInsertBackend___closed__0_value;
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_encodeLeanOptionValue(lean_object*);
static const lean_closure_object l_Lake_instToTomlLeanOptionValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Toml_encodeLeanOptionValue, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instToTomlLeanOptionValue___closed__0 = (const lean_object*)&l_Lake_instToTomlLeanOptionValue___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instToTomlLeanOptionValue = (const lean_object*)&l_Lake_instToTomlLeanOptionValue___closed__0_value;
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_encodeLeanOptions_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_encodeLeanOptions_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Toml_RBDict_empty(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_Toml_encodeLeanOptions___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_encodeLeanOptions___closed__0;
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_encodeLeanOptions(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_encodeLeanOptions___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToTomlArrayLeanOption___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToTomlArrayLeanOption___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_instToTomlArrayLeanOption___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instToTomlArrayLeanOption___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instToTomlArrayLeanOption___closed__0 = (const lean_object*)&l_Lake_instToTomlArrayLeanOption___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instToTomlArrayLeanOption = (const lean_object*)&l_Lake_instToTomlArrayLeanOption___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_encodeSingleton_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_encodeSingleton_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Pattern_toToml_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "preset"};
static const lean_object* l_Lake_Pattern_toToml_x3f___redArg___closed__0 = (const lean_object*)&l_Lake_Pattern_toToml_x3f___redArg___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lake_Pattern_toToml_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Pattern_toToml_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(167, 141, 167, 139, 231, 252, 123, 41)}};
static const lean_object* l_Lake_Pattern_toToml_x3f___redArg___closed__1 = (const lean_object*)&l_Lake_Pattern_toToml_x3f___redArg___closed__1_value;
static const lean_string_object l_Lake_PatternDescr_toToml_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "not"};
static const lean_object* l_Lake_PatternDescr_toToml_x3f___redArg___closed__0 = (const lean_object*)&l_Lake_PatternDescr_toToml_x3f___redArg___closed__0_value;
static const lean_ctor_object l_Lake_PatternDescr_toToml_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PatternDescr_toToml_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(165, 88, 163, 238, 255, 136, 155, 96)}};
static const lean_object* l_Lake_PatternDescr_toToml_x3f___redArg___closed__1 = (const lean_object*)&l_Lake_PatternDescr_toToml_x3f___redArg___closed__1_value;
static const lean_string_object l_Lake_PatternDescr_toToml_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "all"};
static const lean_object* l_Lake_PatternDescr_toToml_x3f___redArg___closed__2 = (const lean_object*)&l_Lake_PatternDescr_toToml_x3f___redArg___closed__2_value;
static const lean_ctor_object l_Lake_PatternDescr_toToml_x3f___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PatternDescr_toToml_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(135, 186, 94, 176, 136, 38, 52, 11)}};
static const lean_object* l_Lake_PatternDescr_toToml_x3f___redArg___closed__3 = (const lean_object*)&l_Lake_PatternDescr_toToml_x3f___redArg___closed__3_value;
static const lean_string_object l_Lake_PatternDescr_toToml_x3f___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "any"};
static const lean_object* l_Lake_PatternDescr_toToml_x3f___redArg___closed__4 = (const lean_object*)&l_Lake_PatternDescr_toToml_x3f___redArg___closed__4_value;
static const lean_ctor_object l_Lake_PatternDescr_toToml_x3f___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PatternDescr_toToml_x3f___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(83, 73, 105, 67, 238, 102, 92, 211)}};
static const lean_object* l_Lake_PatternDescr_toToml_x3f___redArg___closed__5 = (const lean_object*)&l_Lake_PatternDescr_toToml_x3f___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Lake_Pattern_toToml_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Pattern_toToml_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lake_Toml_encodeArray_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PatternDescr_toToml_x3f___redArg(lean_object*, lean_object*);
static const lean_string_object l_Lake_Pattern_toToml_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "default"};
static const lean_object* l_Lake_Pattern_toToml_x3f___redArg___closed__2 = (const lean_object*)&l_Lake_Pattern_toToml_x3f___redArg___closed__2_value;
static const lean_string_object l_Lake_Pattern_toToml_x3f___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "star"};
static const lean_object* l_Lake_Pattern_toToml_x3f___redArg___closed__3 = (const lean_object*)&l_Lake_Pattern_toToml_x3f___redArg___closed__3_value;
static const lean_string_object l_Lake_Pattern_toToml_x3f___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* l_Lake_Pattern_toToml_x3f___redArg___closed__4 = (const lean_object*)&l_Lake_Pattern_toToml_x3f___redArg___closed__4_value;
static const lean_ctor_object l_Lake_Pattern_toToml_x3f___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Pattern_toToml_x3f___redArg___closed__4_value)}};
static const lean_object* l_Lake_Pattern_toToml_x3f___redArg___closed__5 = (const lean_object*)&l_Lake_Pattern_toToml_x3f___redArg___closed__5_value;
static const lean_ctor_object l_Lake_Pattern_toToml_x3f___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Pattern_toToml_x3f___redArg___closed__5_value)}};
static const lean_object* l_Lake_Pattern_toToml_x3f___redArg___closed__6 = (const lean_object*)&l_Lake_Pattern_toToml_x3f___redArg___closed__6_value;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_PatternDescr_toToml_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fPattern___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fPattern(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fPatternDescr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fPatternDescr(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_StrPatDescr_toToml_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_StrPatDescr_toToml_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_StrPatDescr_toToml___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "startsWith"};
static const lean_object* l_Lake_StrPatDescr_toToml___closed__0 = (const lean_object*)&l_Lake_StrPatDescr_toToml___closed__0_value;
static const lean_ctor_object l_Lake_StrPatDescr_toToml___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_StrPatDescr_toToml___closed__0_value),LEAN_SCALAR_PTR_LITERAL(115, 155, 141, 25, 60, 237, 71, 255)}};
static const lean_object* l_Lake_StrPatDescr_toToml___closed__1 = (const lean_object*)&l_Lake_StrPatDescr_toToml___closed__1_value;
static const lean_string_object l_Lake_StrPatDescr_toToml___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "endsWith"};
static const lean_object* l_Lake_StrPatDescr_toToml___closed__2 = (const lean_object*)&l_Lake_StrPatDescr_toToml___closed__2_value;
static const lean_ctor_object l_Lake_StrPatDescr_toToml___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_StrPatDescr_toToml___closed__2_value),LEAN_SCALAR_PTR_LITERAL(148, 44, 139, 66, 217, 150, 241, 237)}};
static const lean_object* l_Lake_StrPatDescr_toToml___closed__3 = (const lean_object*)&l_Lake_StrPatDescr_toToml___closed__3_value;
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_toToml(lean_object*);
static const lean_closure_object l___private_Lake_CLI_Translate_Toml_0__Lake_instToTomlStrPatDescr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_StrPatDescr_toToml, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_instToTomlStrPatDescr___closed__0 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_instToTomlStrPatDescr___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_instToTomlStrPatDescr = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_instToTomlStrPatDescr___closed__0_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l_Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00Lake_PathPatDescr_toToml_x3f_spec__0_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00Lake_PathPatDescr_toToml_x3f_spec__0_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00Lake_PathPatDescr_toToml_x3f_spec__0_spec__0_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00Lake_PathPatDescr_toToml_x3f_spec__0_spec__0_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00Lake_PathPatDescr_toToml_x3f_spec__0_spec__0_spec__1___redArg___closed__0_value)}};
static const lean_object* l_Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00Lake_PathPatDescr_toToml_x3f_spec__0_spec__0_spec__1___redArg___closed__1 = (const lean_object*)&l_Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00Lake_PathPatDescr_toToml_x3f_spec__0_spec__0_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Pattern_toToml_x3f___at___00Lake_PathPatDescr_toToml_x3f_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00Lake_PathPatDescr_toToml_x3f_spec__0_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00Lake_PathPatDescr_toToml_x3f_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00Lake_PathPatDescr_toToml_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00Lake_PathPatDescr_toToml_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00Lake_PathPatDescr_toToml_x3f_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_PathPatDescr_toToml_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "path"};
static const lean_object* l_Lake_PathPatDescr_toToml_x3f___closed__0 = (const lean_object*)&l_Lake_PathPatDescr_toToml_x3f___closed__0_value;
static const lean_ctor_object l_Lake_PathPatDescr_toToml_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PathPatDescr_toToml_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 173, 251, 55, 140, 124, 51, 22)}};
static const lean_object* l_Lake_PathPatDescr_toToml_x3f___closed__1 = (const lean_object*)&l_Lake_PathPatDescr_toToml_x3f___closed__1_value;
static const lean_string_object l_Lake_PathPatDescr_toToml_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "extension"};
static const lean_object* l_Lake_PathPatDescr_toToml_x3f___closed__2 = (const lean_object*)&l_Lake_PathPatDescr_toToml_x3f___closed__2_value;
static const lean_ctor_object l_Lake_PathPatDescr_toToml_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PathPatDescr_toToml_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(132, 249, 60, 22, 4, 245, 93, 7)}};
static const lean_object* l_Lake_PathPatDescr_toToml_x3f___closed__3 = (const lean_object*)&l_Lake_PathPatDescr_toToml_x3f___closed__3_value;
static const lean_string_object l_Lake_PathPatDescr_toToml_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "fileName"};
static const lean_object* l_Lake_PathPatDescr_toToml_x3f___closed__4 = (const lean_object*)&l_Lake_PathPatDescr_toToml_x3f___closed__4_value;
static const lean_ctor_object l_Lake_PathPatDescr_toToml_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PathPatDescr_toToml_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(67, 201, 140, 230, 1, 55, 95, 217)}};
static const lean_object* l_Lake_PathPatDescr_toToml_x3f___closed__5 = (const lean_object*)&l_Lake_PathPatDescr_toToml_x3f___closed__5_value;
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_toToml_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Pattern_toToml_x3f___at___00Lake_PathPatDescr_toToml_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00Lake_PathPatDescr_toToml_x3f_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00Lake_PathPatDescr_toToml_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00Lake_PathPatDescr_toToml_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00Lake_PathPatDescr_toToml_x3f_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00Lake_PathPatDescr_toToml_x3f_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_CLI_Translate_Toml_0__Lake_instToToml_x3fPathPatDescr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PathPatDescr_toToml_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_instToToml_x3fPathPatDescr___closed__0 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_instToToml_x3fPathPatDescr___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_instToToml_x3fPathPatDescr = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_instToToml_x3fPathPatDescr___closed__0_value;
lean_object* l_Lake_Name_eraseHead(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_encodeFacets_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_encodeFacets_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_encodeFacets(lean_object*);
static const lean_closure_object l___private_Lake_CLI_Translate_Toml_0__Lake_instEncodeFieldLeanLibConfigMkStr1ArrayName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_encodeFacets, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_instEncodeFieldLeanLibConfigMkStr1ArrayName___closed__0 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_instEncodeFieldLeanLibConfigMkStr1ArrayName___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_instEncodeFieldLeanLibConfigMkStr1ArrayName(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_instEncodeFieldLeanLibConfigMkStr1ArrayName___boxed(lean_object*);
lean_object* l_Lake_BuildKey_toString(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_instToTomlBuildKey___lam__0(lean_object*);
static const lean_closure_object l___private_Lake_CLI_Translate_Toml_0__Lake_instToTomlBuildKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_CLI_Translate_Toml_0__Lake_instToTomlBuildKey___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_instToTomlBuildKey___closed__0 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_instToTomlBuildKey___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_instToTomlBuildKey = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_instToTomlBuildKey___closed__0_value;
lean_object* l_Lake_PartialBuildKey_toString(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_instToTomlPartialBuildKey___lam__0(lean_object*);
static const lean_closure_object l___private_Lake_CLI_Translate_Toml_0__Lake_instToTomlPartialBuildKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_CLI_Translate_Toml_0__Lake_instToTomlPartialBuildKey___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_instToTomlPartialBuildKey___closed__0 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_instToTomlPartialBuildKey___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_instToTomlPartialBuildKey = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_instToTomlPartialBuildKey___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_instToTomlTarget(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lake_Dependency_toToml_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lake_Dependency_toToml___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "options"};
static const lean_object* l_Lake_Dependency_toToml___closed__0 = (const lean_object*)&l_Lake_Dependency_toToml___closed__0_value;
static const lean_ctor_object l_Lake_Dependency_toToml___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Dependency_toToml___closed__0_value),LEAN_SCALAR_PTR_LITERAL(15, 45, 121, 141, 112, 165, 100, 9)}};
static const lean_object* l_Lake_Dependency_toToml___closed__1 = (const lean_object*)&l_Lake_Dependency_toToml___closed__1_value;
static const lean_string_object l_Lake_Dependency_toToml___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "subDir"};
static const lean_object* l_Lake_Dependency_toToml___closed__2 = (const lean_object*)&l_Lake_Dependency_toToml___closed__2_value;
static const lean_ctor_object l_Lake_Dependency_toToml___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Dependency_toToml___closed__2_value),LEAN_SCALAR_PTR_LITERAL(91, 164, 30, 214, 89, 255, 168, 103)}};
static const lean_object* l_Lake_Dependency_toToml___closed__3 = (const lean_object*)&l_Lake_Dependency_toToml___closed__3_value;
static const lean_string_object l_Lake_Dependency_toToml___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "git"};
static const lean_object* l_Lake_Dependency_toToml___closed__4 = (const lean_object*)&l_Lake_Dependency_toToml___closed__4_value;
static const lean_ctor_object l_Lake_Dependency_toToml___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Dependency_toToml___closed__4_value),LEAN_SCALAR_PTR_LITERAL(135, 54, 39, 136, 227, 117, 1, 165)}};
static const lean_object* l_Lake_Dependency_toToml___closed__5 = (const lean_object*)&l_Lake_Dependency_toToml___closed__5_value;
static const lean_string_object l_Lake_Dependency_toToml___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rev"};
static const lean_object* l_Lake_Dependency_toToml___closed__6 = (const lean_object*)&l_Lake_Dependency_toToml___closed__6_value;
static const lean_ctor_object l_Lake_Dependency_toToml___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Dependency_toToml___closed__6_value),LEAN_SCALAR_PTR_LITERAL(215, 226, 195, 78, 237, 95, 37, 186)}};
static const lean_object* l_Lake_Dependency_toToml___closed__7 = (const lean_object*)&l_Lake_Dependency_toToml___closed__7_value;
static const lean_string_object l_Lake_Dependency_toToml___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "version"};
static const lean_object* l_Lake_Dependency_toToml___closed__8 = (const lean_object*)&l_Lake_Dependency_toToml___closed__8_value;
static const lean_ctor_object l_Lake_Dependency_toToml___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Dependency_toToml___closed__8_value),LEAN_SCALAR_PTR_LITERAL(167, 68, 50, 73, 160, 48, 142, 108)}};
static const lean_object* l_Lake_Dependency_toToml___closed__9 = (const lean_object*)&l_Lake_Dependency_toToml___closed__9_value;
static const lean_string_object l_Lake_Dependency_toToml___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_Dependency_toToml___closed__10 = (const lean_object*)&l_Lake_Dependency_toToml___closed__10_value;
static const lean_string_object l_Lake_Dependency_toToml___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l_Lake_Dependency_toToml___closed__11 = (const lean_object*)&l_Lake_Dependency_toToml___closed__11_value;
static const lean_ctor_object l_Lake_Dependency_toToml___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Dependency_toToml___closed__11_value),LEAN_SCALAR_PTR_LITERAL(84, 246, 234, 130, 97, 205, 144, 82)}};
static const lean_object* l_Lake_Dependency_toToml___closed__12 = (const lean_object*)&l_Lake_Dependency_toToml___closed__12_value;
static const lean_string_object l_Lake_Dependency_toToml___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "scope"};
static const lean_object* l_Lake_Dependency_toToml___closed__13 = (const lean_object*)&l_Lake_Dependency_toToml___closed__13_value;
static const lean_ctor_object l_Lake_Dependency_toToml___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Dependency_toToml___closed__13_value),LEAN_SCALAR_PTR_LITERAL(219, 110, 100, 210, 231, 203, 62, 196)}};
static const lean_object* l_Lake_Dependency_toToml___closed__14 = (const lean_object*)&l_Lake_Dependency_toToml___closed__14_value;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lake_mkRelPathString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Dependency_toToml(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lake_Dependency_toToml_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToTomlDependency___lam__0(lean_object*);
static const lean_closure_object l_Lake_instToTomlDependency___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instToTomlDependency___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instToTomlDependency___closed__0 = (const lean_object*)&l_Lake_instToTomlDependency___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instToTomlDependency = (const lean_object*)&l_Lake_instToTomlDependency___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "x_"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__0___closed__0 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__0___closed__0_value;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__0 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__1 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__1_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__2 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__2_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "pipeProj"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__3 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__3_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__4_value_aux_0),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__4_value_aux_1),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__4_value_aux_2),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(104, 78, 204, 170, 128, 130, 207, 24)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__4 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__4_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "|>."};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__5 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__5_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "insertField"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__6 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__6_value;
lean_object* l_String_toRawSubstring_x27(lean_object*);
static lean_once_cell_t l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__7;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(84, 245, 151, 73, 184, 76, 130, 225)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__8 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__8_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__9 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__9_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__10 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__10_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "cfg"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__11 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__11_value;
static lean_once_cell_t l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__12;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__11_value),LEAN_SCALAR_PTR_LITERAL(193, 249, 49, 54, 148, 135, 57, 21)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__13 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__13_value;
uint8_t l_Array_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instQuoteNameMkStr1___private__1(lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___lam__0, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__0 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__0_value;
lean_object* l_EStateM_instMonad___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___lam__1, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__1 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__1_value;
lean_object* l_EStateM_instMonad___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___lam__2, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__2 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__2_value;
lean_object* l_EStateM_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_map, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__3 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__3_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__3_value),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__0_value)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__4 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__4_value;
lean_object* l_EStateM_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_pure, .m_arity = 5, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__5 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__5_value;
lean_object* l_EStateM_seqRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_seqRight, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__6 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__6_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__4_value),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__5_value),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__1_value),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__2_value),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__6_value)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__7 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__7_value;
lean_object* l_EStateM_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_bind, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__8 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__8_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__7_value),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__8_value)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__9 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__9_value;
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
static lean_once_cell_t l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__10;
static const lean_closure_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__11 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__11_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "_root_"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__12 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__12_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__12_value),LEAN_SCALAR_PTR_LITERAL(184, 175, 53, 50, 212, 152, 178, 8)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__13 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__13_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "toToml"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__14 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__14_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__15 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__15_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__16 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__16_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__17_value_aux_0),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__17_value_aux_1),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__15_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__17_value_aux_2),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__16_value),LEAN_SCALAR_PTR_LITERAL(157, 246, 223, 221, 242, 35, 238, 117)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__17 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__17_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__18 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__18_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__19_value_aux_0),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__19_value_aux_1),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__15_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__19_value_aux_2),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__18_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__19 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__19_value;
lean_object* l_Array_mkArray0(lean_object*);
static lean_once_cell_t l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__20;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__21 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__21_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__22_value_aux_0),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__22_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__22_value_aux_1),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__15_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__22_value_aux_2),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__21_value),LEAN_SCALAR_PTR_LITERAL(248, 187, 217, 228, 39, 184, 218, 135)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__22 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__22_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "def"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__23 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__23_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__24 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__24_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__25_value_aux_0),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__25_value_aux_1),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__15_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__25_value_aux_2),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__24_value),LEAN_SCALAR_PTR_LITERAL(243, 92, 136, 33, 216, 98, 92, 25)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__25 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__25_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "optDeclSig"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__26 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__26_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__27_value_aux_0),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__27_value_aux_1),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__15_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__27_value_aux_2),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__26_value),LEAN_SCALAR_PTR_LITERAL(26, 9, 103, 232, 183, 57, 246, 75)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__27 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__27_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "explicitBinder"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__28 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__28_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__29_value_aux_0),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__29_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__29_value_aux_1),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__29_value_aux_2),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__28_value),LEAN_SCALAR_PTR_LITERAL(49, 119, 193, 23, 170, 93, 183, 238)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__29 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__29_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__30 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__30_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__31 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__31_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__32 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__32_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "t"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__33 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__33_value;
static lean_once_cell_t l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__34;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__33_value),LEAN_SCALAR_PTR_LITERAL(123, 228, 43, 115, 146, 126, 91, 53)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__35 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__35_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Table"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__36 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__36_value;
static lean_once_cell_t l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__37;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__36_value),LEAN_SCALAR_PTR_LITERAL(168, 47, 222, 89, 104, 208, 170, 129)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__38 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__38_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__39 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__39_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Toml"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__40 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__40_value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__39_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__41_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__41_value_aux_0),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__40_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__41_value_aux_1),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__36_value),LEAN_SCALAR_PTR_LITERAL(229, 29, 249, 170, 130, 248, 139, 186)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__41 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__41_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__41_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__42 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__42_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__41_value)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__43 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__43_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__43_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__44 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__44_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__42_value),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__44_value)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__45 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__45_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "binderDefault"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__46 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__46_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__47_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__47_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__47_value_aux_0),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__47_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__47_value_aux_1),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__47_value_aux_2),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__46_value),LEAN_SCALAR_PTR_LITERAL(35, 119, 214, 97, 198, 223, 242, 31)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__47 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__47_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__48 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__48_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "choice"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__49 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__49_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__49_value),LEAN_SCALAR_PTR_LITERAL(59, 66, 148, 42, 181, 100, 85, 166)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__50 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__50_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "term{}"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__51 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__51_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__51_value),LEAN_SCALAR_PTR_LITERAL(44, 141, 217, 101, 193, 131, 35, 71)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__52 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__52_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__53 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__53_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__54 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__54_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "structInst"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__55 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__55_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__56_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__56_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__56_value_aux_0),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__56_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__56_value_aux_1),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__56_value_aux_2),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__55_value),LEAN_SCALAR_PTR_LITERAL(50, 43, 73, 62, 118, 124, 31, 28)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__56 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__56_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "structInstFields"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__57 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__57_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__58_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__58_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__58_value_aux_0),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__58_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__58_value_aux_1),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__58_value_aux_2),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__57_value),LEAN_SCALAR_PTR_LITERAL(0, 82, 141, 43, 62, 171, 163, 69)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__58 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__58_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "optEllipsis"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__59 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__59_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__60_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__60_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__60_value_aux_0),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__60_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__60_value_aux_1),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__60_value_aux_2),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__59_value),LEAN_SCALAR_PTR_LITERAL(13, 1, 242, 203, 207, 188, 181, 160)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__60 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__60_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__61 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__61_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__62_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__62_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__62_value_aux_0),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__62_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__62_value_aux_1),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__15_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__62_value_aux_2),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__61_value),LEAN_SCALAR_PTR_LITERAL(228, 117, 47, 248, 145, 185, 135, 188)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__62 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__62_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__63 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__63_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__64 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__64_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__65_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__65_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__65_value_aux_0),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__65_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__65_value_aux_1),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__63_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__65_value_aux_2),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__64_value),LEAN_SCALAR_PTR_LITERAL(245, 187, 99, 45, 217, 244, 244, 120)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__65 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__65_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instToToml"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__66 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__66_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instance"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__67 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__67_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__68_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__68_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__68_value_aux_0),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__68_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__68_value_aux_1),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__15_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__68_value_aux_2),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__67_value),LEAN_SCALAR_PTR_LITERAL(37, 156, 84, 218, 244, 57, 142, 153)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__68 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__68_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__69 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__69_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__70_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__70_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__70_value_aux_0),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__70_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__70_value_aux_1),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__70_value_aux_2),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__69_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__70 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__70_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "declSig"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__71 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__71_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__72_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__72_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__72_value_aux_0),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__72_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__72_value_aux_1),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__15_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__72_value_aux_2),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__71_value),LEAN_SCALAR_PTR_LITERAL(22, 101, 130, 251, 183, 19, 113, 82)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__72 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__72_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__73 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__73_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__74_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__74_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__74_value_aux_0),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__74_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__74_value_aux_1),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__74_value_aux_2),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__73_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__74 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__74_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__75 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__75_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__76_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__76_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__76_value_aux_0),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__76_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__76_value_aux_1),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__76_value_aux_2),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__75_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__76 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__76_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ToToml"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__77 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__77_value;
static lean_once_cell_t l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__78_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__78;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__77_value),LEAN_SCALAR_PTR_LITERAL(30, 168, 224, 195, 232, 17, 16, 176)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__79 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__79_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__80_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__39_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__80_value_aux_0),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__77_value),LEAN_SCALAR_PTR_LITERAL(218, 201, 86, 217, 220, 224, 122, 28)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__80 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__80_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__80_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__81 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__81_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__80_value)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__82 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__82_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__83_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__82_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__83 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__83_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__81_value),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__83_value)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__84 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__84_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "anonymousCtor"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__85 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__85_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__86_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__86_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__86_value_aux_0),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__86_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__86_value_aux_1),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__86_value_aux_2),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__85_value),LEAN_SCALAR_PTR_LITERAL(56, 53, 154, 97, 179, 232, 94, 186)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__86 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__86_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__87_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟨"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__87 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__87_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__88_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__88 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__88_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__89_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__89_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__89_value_aux_0),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__89_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__89_value_aux_1),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__89_value_aux_2),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__88_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__89 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__89_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__90_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__90 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__90_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__91_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__91_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__91_value_aux_0),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__91_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__91_value_aux_1),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__91_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__91_value_aux_2),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__90_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__91 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__91_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__92_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__92 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__92_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__93_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__92_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__93 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__93_value;
static lean_once_cell_t l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__94_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__94;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__95_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__39_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__95 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__95_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__96_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__95_value)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__96 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__96_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__97_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__39_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__97_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__97_value_aux_0),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__40_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__97 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__97_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__98_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__97_value)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__98 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__98_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__99_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "System"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__99 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__99_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__100_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__99_value),LEAN_SCALAR_PTR_LITERAL(244, 7, 92, 194, 164, 177, 167, 52)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__100 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__100_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__101_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__100_value)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__101 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__101_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__102_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__102 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__102_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__103_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__102_value)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__103 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__103_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__104_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__103_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__104 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__104_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__105_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__101_value),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__104_value)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__105 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__105_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__106_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__98_value),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__105_value)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__106 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__106_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__107_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__96_value),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__106_value)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__107 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__107_value;
static lean_once_cell_t l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__108_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__108;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__109_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__14_value),LEAN_SCALAR_PTR_LITERAL(53, 116, 122, 14, 110, 186, 168, 118)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__109 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__109_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__110_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__39_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__110_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__110_value_aux_0),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__77_value),LEAN_SCALAR_PTR_LITERAL(218, 201, 86, 217, 220, 224, 122, 28)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__110_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__110_value_aux_1),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__14_value),LEAN_SCALAR_PTR_LITERAL(64, 104, 190, 240, 103, 2, 5, 112)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__110 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__110_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__111_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__110_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__111 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__111_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__112_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__111_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__112 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__112_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__113_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "proj"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__113 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__113_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__114_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__114_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__114_value_aux_0),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__114_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__114_value_aux_1),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__114_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__114_value_aux_2),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__113_value),LEAN_SCALAR_PTR_LITERAL(103, 149, 207, 196, 17, 4, 77, 74)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__114 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__114_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__115_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cdot"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__115 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__115_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__116_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__116_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__116_value_aux_0),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__116_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__116_value_aux_1),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__116_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__116_value_aux_2),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__115_value),LEAN_SCALAR_PTR_LITERAL(215, 94, 65, 66, 49, 100, 151, 85)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__116 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__116_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__117_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 1, .m_data = "·"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__117 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__117_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__118_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__118 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__118_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__119_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟩"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__119 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__119_value;
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__120_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__120 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__120_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__121_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "t.insert"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__121 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__121_value;
static lean_once_cell_t l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__122_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__122;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__123_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "insert"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__123 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__123_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__124_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__33_value),LEAN_SCALAR_PTR_LITERAL(123, 228, 43, 115, 146, 126, 91, 53)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__124_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__124_value_aux_0),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__123_value),LEAN_SCALAR_PTR_LITERAL(77, 96, 213, 186, 229, 16, 115, 135)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__124 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__124_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__125_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "quotedName"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__125 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__125_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__126_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__126_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__126_value_aux_0),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__126_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__126_value_aux_1),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__126_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__126_value_aux_2),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__125_value),LEAN_SCALAR_PTR_LITERAL(217, 120, 158, 75, 195, 162, 2, 130)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__126 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__126_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__127_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "`name"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__127 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__127_value;
extern lean_object* l_Lean_Macro_instMonadRefMacroM;
lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkCApp(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFromRef___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__0 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__0_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__1 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__1_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__1_value),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__39_value),LEAN_SCALAR_PTR_LITERAL(91, 223, 152, 205, 91, 21, 95, 180)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__2 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__2_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "CLI"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__3 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__3_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__2_value),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__3_value),LEAN_SCALAR_PTR_LITERAL(160, 181, 39, 219, 11, 255, 82, 15)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__4 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__4_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Translate"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__5 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__5_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__4_value),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__5_value),LEAN_SCALAR_PTR_LITERAL(35, 54, 7, 49, 122, 225, 157, 140)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__6 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__6_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__6_value),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__40_value),LEAN_SCALAR_PTR_LITERAL(142, 174, 23, 138, 222, 251, 221, 20)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__7 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__7_value;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(183, 245, 41, 53, 224, 188, 72, 55)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__8 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__8_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__8_value),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__39_value),LEAN_SCALAR_PTR_LITERAL(107, 221, 204, 96, 70, 223, 87, 187)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__9 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__9_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "commandGen_toml_encoders%"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__10 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__10_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__9_value),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__10_value),LEAN_SCALAR_PTR_LITERAL(36, 134, 90, 69, 211, 19, 129, 164)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__11 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__11_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "gen_toml_encoders%"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__12 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__12_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__12_value)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__13 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__13_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__11_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__13_value)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__14 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__14_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__14_value;
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__2(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_LeanConfig_instConfigInfo;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_LeanExeConfig_instConfigInfo;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_PackageConfig_instConfigInfo;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_InputDirConfig_instConfigInfo;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_InputFileConfig_instConfigInfo;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_WorkspaceConfig_instConfigInfo;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_LeanLibConfig_instConfigInfo;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__0 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "LeanConfig"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__1 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__1_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__39_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__2_value_aux_0),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(187, 169, 219, 111, 225, 149, 195, 177)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__2 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__2_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "LeanLibConfig"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__3 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__3_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__39_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__4_value_aux_0),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(198, 170, 90, 64, 42, 217, 142, 231)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__4 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__4_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "nativeFacets"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__5 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__5_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(130, 15, 19, 239, 40, 85, 158, 29)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__6 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__6_value;
static const lean_array_object l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__6_value)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__7 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__7_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "LeanExeConfig"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__8 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__8_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__39_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__9_value_aux_0),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(156, 243, 7, 226, 235, 231, 86, 77)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__9 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__9_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "InputFileConfig"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__10 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__10_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__39_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__11_value_aux_0),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(191, 174, 82, 61, 179, 144, 212, 192)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__11 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__11_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "InputDirConfig"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__12 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__12_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__39_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__13_value_aux_0),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(27, 156, 246, 157, 165, 57, 171, 220)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__13 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__13_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "WorkspaceConfig"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__14 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__14_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__39_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__15_value_aux_0),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(79, 221, 203, 100, 117, 196, 4, 153)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__15 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__15_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "PackageConfig"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__16 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__16_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__39_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__17_value_aux_0),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(14, 50, 33, 106, 4, 142, 225, 217)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__17 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__17_value;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "plugins"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__0 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__0_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 100, 103, 72, 156, 88, 10, 236)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__1 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__1_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "dynlibs"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__2 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__2_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__2_value),LEAN_SCALAR_PTR_LITERAL(213, 126, 44, 113, 100, 173, 176, 199)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__3 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__3_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "platformIndependent"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__4 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__4_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__4_value),LEAN_SCALAR_PTR_LITERAL(51, 35, 219, 1, 108, 129, 116, 147)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__5 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__5_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "backend"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__6 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__6_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__6_value),LEAN_SCALAR_PTR_LITERAL(40, 75, 156, 92, 110, 161, 40, 36)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__7 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__7_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "weakLinkArgs"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__8 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__8_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__8_value),LEAN_SCALAR_PTR_LITERAL(187, 9, 155, 166, 154, 189, 94, 67)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__9 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__9_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "moreLinkArgs"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__10 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__10_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__10_value),LEAN_SCALAR_PTR_LITERAL(14, 165, 131, 17, 225, 82, 140, 145)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__11 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__11_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "moreLinkLibs"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__12 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__12_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__12_value),LEAN_SCALAR_PTR_LITERAL(111, 122, 160, 205, 53, 195, 181, 180)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__13 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__13_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "moreLinkObjs"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__14 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__14_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__14_value),LEAN_SCALAR_PTR_LITERAL(232, 242, 55, 26, 170, 174, 241, 71)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__15 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__15_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "weakLeancArgs"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__16 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__16_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__16_value),LEAN_SCALAR_PTR_LITERAL(103, 110, 140, 220, 181, 192, 131, 104)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__17 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__17_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "moreServerOptions"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__18 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__18_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__18_value),LEAN_SCALAR_PTR_LITERAL(206, 114, 170, 237, 212, 72, 1, 170)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__19 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__19_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "moreLeancArgs"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__20 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__20_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__20_value),LEAN_SCALAR_PTR_LITERAL(35, 65, 185, 53, 108, 178, 133, 37)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__21 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__21_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "weakLeanArgs"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__22 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__22_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__22_value),LEAN_SCALAR_PTR_LITERAL(12, 17, 230, 153, 39, 202, 125, 90)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__23 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__23_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "moreLeanArgs"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__24 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__24_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__24_value),LEAN_SCALAR_PTR_LITERAL(110, 73, 169, 213, 6, 174, 187, 7)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__25 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__25_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "leanOptions"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__26 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__26_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__26_value),LEAN_SCALAR_PTR_LITERAL(20, 201, 223, 70, 146, 84, 32, 214)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__27 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__27_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "buildType"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__28 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__28_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__28_value),LEAN_SCALAR_PTR_LITERAL(210, 227, 67, 96, 129, 21, 223, 119)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__29 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__29_value;
extern lean_object* l_Lake_LeanConfig_buildType___proj;
extern lean_object* l_Lake_LeanConfig_plugins___proj;
extern lean_object* l_Lake_LeanConfig_dynlibs___proj;
extern lean_object* l_Lake_LeanConfig_platformIndependent___proj;
extern lean_object* l_Lake_LeanConfig_backend___proj;
uint8_t l_Lake_instDecidableEqBackend(uint8_t, uint8_t);
extern lean_object* l_Lake_LeanConfig_weakLinkArgs___proj;
extern lean_object* l_Lake_LeanConfig_moreLinkArgs___proj;
extern lean_object* l_Lake_LeanConfig_moreLinkLibs___proj;
extern lean_object* l_Lake_LeanConfig_moreLinkObjs___proj;
extern lean_object* l_Lake_LeanConfig_weakLeancArgs___proj;
extern lean_object* l_Lake_LeanConfig_moreServerOptions___proj;
extern lean_object* l_Lake_LeanConfig_moreLeancArgs___proj;
extern lean_object* l_Lake_LeanConfig_weakLeanArgs___proj;
extern lean_object* l_Lake_LeanConfig_moreLeanArgs___proj;
extern lean_object* l_Lake_LeanConfig_leanOptions___proj;
uint8_t l_Lake_instDecidableEqBuildType(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_instToToml___lam__0(lean_object*);
static const lean_closure_object l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_instToToml___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_instToToml___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_instToToml___closed__0 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_instToToml___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_instToToml = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_instToToml___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_instDecidableEqGlob_decEq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "allowImportAll"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__0 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__0_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 199, 75, 91, 118, 43, 12, 210)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__1 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__1_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "defaultFacets"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__2 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__2_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__2_value),LEAN_SCALAR_PTR_LITERAL(74, 73, 74, 204, 169, 19, 96, 134)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__3 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__3_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "precompileModules"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__4 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__4_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__4_value),LEAN_SCALAR_PTR_LITERAL(210, 72, 98, 56, 225, 29, 247, 45)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__5 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__5_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "extraDepTargets"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__6 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__6_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__6_value),LEAN_SCALAR_PTR_LITERAL(232, 29, 68, 154, 160, 50, 56, 5)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__7 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__7_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "needs"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__8 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__8_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__8_value),LEAN_SCALAR_PTR_LITERAL(215, 219, 176, 39, 126, 76, 70, 199)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__9 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__9_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "libPrefixOnWindows"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__10 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__10_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__10_value),LEAN_SCALAR_PTR_LITERAL(26, 75, 58, 45, 181, 132, 175, 34)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__11 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__11_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "libName"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__12 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__12_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__12_value),LEAN_SCALAR_PTR_LITERAL(19, 171, 234, 84, 17, 149, 3, 152)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__13 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__13_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "globs"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__14 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__14_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__14_value),LEAN_SCALAR_PTR_LITERAL(2, 64, 222, 202, 250, 190, 94, 19)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__15 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__15_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "roots"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__16 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__16_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__16_value),LEAN_SCALAR_PTR_LITERAL(160, 214, 73, 39, 112, 55, 103, 176)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__17 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__17_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "srcDir"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__18 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__18_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__18_value),LEAN_SCALAR_PTR_LITERAL(82, 241, 97, 48, 55, 77, 36, 145)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__19 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__19_value;
lean_object* l_Lake_LeanLibConfig_srcDir___proj(lean_object*);
lean_object* l_Lake_LeanLibConfig_toLeanConfig___proj(lean_object*);
lean_object* l_Lake_LeanLibConfig_allowImportAll___proj(lean_object*);
lean_object* l_Lake_LeanLibConfig_defaultFacets___proj(lean_object*);
lean_object* l_Lake_LeanLibConfig_precompileModules___proj(lean_object*);
lean_object* l_Lake_LeanLibConfig_extraDepTargets___proj(lean_object*);
lean_object* l_Lake_LeanLibConfig_needs___proj(lean_object*);
lean_object* l_Lake_LeanLibConfig_libPrefixOnWindows___proj(lean_object*);
lean_object* l_Lake_LeanLibConfig_libName___proj(lean_object*);
lean_object* l_Lake_LeanLibConfig_globs___proj(lean_object*);
lean_object* l_Lake_LeanLibConfig_roots___proj(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_instToToml___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_instToToml(lean_object*);
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_LeanExeConfig_toToml___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "supportInterpreter"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanExeConfig_toToml___closed__0 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanExeConfig_toToml___closed__0_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_LeanExeConfig_toToml___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanExeConfig_toToml___closed__0_value),LEAN_SCALAR_PTR_LITERAL(255, 128, 143, 77, 165, 186, 154, 46)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanExeConfig_toToml___closed__1 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanExeConfig_toToml___closed__1_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_LeanExeConfig_toToml___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "exeName"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanExeConfig_toToml___closed__2 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanExeConfig_toToml___closed__2_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_LeanExeConfig_toToml___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanExeConfig_toToml___closed__2_value),LEAN_SCALAR_PTR_LITERAL(143, 84, 120, 178, 127, 24, 112, 7)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanExeConfig_toToml___closed__3 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanExeConfig_toToml___closed__3_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_LeanExeConfig_toToml___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "root"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanExeConfig_toToml___closed__4 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanExeConfig_toToml___closed__4_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_LeanExeConfig_toToml___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanExeConfig_toToml___closed__4_value),LEAN_SCALAR_PTR_LITERAL(214, 106, 196, 92, 110, 240, 161, 193)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanExeConfig_toToml___closed__5 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_LeanExeConfig_toToml___closed__5_value;
lean_object* l_Lake_LeanExeConfig_srcDir___proj(lean_object*);
lean_object* l_Lake_LeanExeConfig_toLeanConfig___proj(lean_object*);
lean_object* l_Lake_LeanExeConfig_supportInterpreter___proj(lean_object*);
lean_object* l_Lake_LeanExeConfig_extraDepTargets___proj(lean_object*);
lean_object* l_Lake_LeanExeConfig_needs___proj(lean_object*);
lean_object* l_Lake_LeanExeConfig_exeName___proj(lean_object*);
lean_object* l_Lake_LeanExeConfig_root___proj(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanExeConfig_toToml(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanExeConfig_instToToml___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanExeConfig_instToToml(lean_object*);
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_InputFileConfig_toToml___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "text"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_InputFileConfig_toToml___closed__0 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_InputFileConfig_toToml___closed__0_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_InputFileConfig_toToml___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_InputFileConfig_toToml___closed__0_value),LEAN_SCALAR_PTR_LITERAL(26, 32, 191, 158, 22, 157, 236, 165)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_InputFileConfig_toToml___closed__1 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_InputFileConfig_toToml___closed__1_value;
lean_object* l_Lake_InputFileConfig_path___proj(lean_object*);
lean_object* l_Lake_InputFileConfig_text___proj(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_InputFileConfig_toToml(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_InputFileConfig_instToToml___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_InputFileConfig_instToToml(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Pattern_toToml_x3f___at___00__private_Lake_CLI_Translate_Toml_0__Lake_InputDirConfig_toToml_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00__private_Lake_CLI_Translate_Toml_0__Lake_InputDirConfig_toToml_spec__0_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00__private_Lake_CLI_Translate_Toml_0__Lake_InputDirConfig_toToml_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00__private_Lake_CLI_Translate_Toml_0__Lake_InputDirConfig_toToml_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00__private_Lake_CLI_Translate_Toml_0__Lake_InputDirConfig_toToml_spec__0_spec__0_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00__private_Lake_CLI_Translate_Toml_0__Lake_InputDirConfig_toToml_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_InputDirConfig_toToml___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "filter"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_InputDirConfig_toToml___closed__0 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_InputDirConfig_toToml___closed__0_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_InputDirConfig_toToml___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_InputDirConfig_toToml___closed__0_value),LEAN_SCALAR_PTR_LITERAL(164, 153, 84, 166, 255, 252, 251, 161)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_InputDirConfig_toToml___closed__1 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_InputDirConfig_toToml___closed__1_value;
lean_object* l_Lake_InputDirConfig_path___proj(lean_object*);
lean_object* l_Lake_InputDirConfig_filter___proj(lean_object*);
lean_object* l_Lake_InputDirConfig_text___proj(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_InputDirConfig_toToml(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Pattern_toToml_x3f___at___00__private_Lake_CLI_Translate_Toml_0__Lake_InputDirConfig_toToml_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00__private_Lake_CLI_Translate_Toml_0__Lake_InputDirConfig_toToml_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00__private_Lake_CLI_Translate_Toml_0__Lake_InputDirConfig_toToml_spec__0_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00__private_Lake_CLI_Translate_Toml_0__Lake_InputDirConfig_toToml_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00__private_Lake_CLI_Translate_Toml_0__Lake_InputDirConfig_toToml_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00__private_Lake_CLI_Translate_Toml_0__Lake_InputDirConfig_toToml_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_InputDirConfig_instToToml___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_InputDirConfig_instToToml(lean_object*);
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_WorkspaceConfig_toToml___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "packagesDir"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_WorkspaceConfig_toToml___closed__0 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_WorkspaceConfig_toToml___closed__0_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_WorkspaceConfig_toToml___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_WorkspaceConfig_toToml___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 147, 205, 88, 160, 133, 8, 11)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_WorkspaceConfig_toToml___closed__1 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_WorkspaceConfig_toToml___closed__1_value;
extern lean_object* l_Lake_WorkspaceConfig_packagesDir___proj;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_WorkspaceConfig_toToml(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_WorkspaceConfig_instToToml___lam__0(lean_object*);
static const lean_closure_object l___private_Lake_CLI_Translate_Toml_0__Lake_WorkspaceConfig_instToToml___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_CLI_Translate_Toml_0__Lake_WorkspaceConfig_instToToml___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_WorkspaceConfig_instToToml___closed__0 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_WorkspaceConfig_instToToml___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_WorkspaceConfig_instToToml = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_WorkspaceConfig_instToToml___closed__0_value;
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "restoreAllArtifacts\?"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__0 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__0_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 1, 41, 192, 97, 8, 217, 82)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__1 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__1_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "enableArtifactCache\?"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__2 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__2_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__2_value),LEAN_SCALAR_PTR_LITERAL(190, 150, 150, 100, 20, 242, 199, 174)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__3 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__3_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reservoir"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__4 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__4_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__4_value),LEAN_SCALAR_PTR_LITERAL(98, 62, 227, 196, 233, 158, 105, 168)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__5 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__5_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "readmeFile"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__6 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__6_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__6_value),LEAN_SCALAR_PTR_LITERAL(86, 68, 195, 254, 204, 64, 41, 249)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__7 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__7_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "licenseFiles"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__8 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__8_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__8_value),LEAN_SCALAR_PTR_LITERAL(115, 188, 70, 201, 62, 96, 76, 55)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__9 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__9_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "license"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__10 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__10_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__10_value),LEAN_SCALAR_PTR_LITERAL(149, 142, 81, 8, 241, 47, 83, 51)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__11 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__11_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "homepage"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__12 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__12_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__12_value),LEAN_SCALAR_PTR_LITERAL(73, 148, 206, 183, 90, 222, 74, 16)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__13 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__13_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "keywords"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__14 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__14_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__14_value),LEAN_SCALAR_PTR_LITERAL(84, 45, 198, 62, 56, 187, 72, 125)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__15 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__15_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "description"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__16 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__16_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__16_value),LEAN_SCALAR_PTR_LITERAL(85, 116, 204, 74, 85, 134, 17, 161)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__17 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__17_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "versionTags"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__18 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__18_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__18_value),LEAN_SCALAR_PTR_LITERAL(76, 44, 235, 102, 59, 70, 79, 98)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__19 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__19_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "lintDriverArgs"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__20 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__20_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__20_value),LEAN_SCALAR_PTR_LITERAL(102, 206, 227, 73, 236, 117, 156, 150)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__21 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__21_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "lintDriver"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__22 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__22_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__22_value),LEAN_SCALAR_PTR_LITERAL(164, 80, 113, 139, 118, 238, 67, 240)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__23 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__23_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "testDriverArgs"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__24 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__24_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__24_value),LEAN_SCALAR_PTR_LITERAL(40, 188, 168, 214, 71, 6, 72, 93)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__25 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__25_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "testDriver"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__26 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__26_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__26_value),LEAN_SCALAR_PTR_LITERAL(187, 40, 173, 233, 223, 78, 220, 191)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__27 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__27_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "preferReleaseBuild"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__28 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__28_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__28_value),LEAN_SCALAR_PTR_LITERAL(75, 209, 233, 233, 163, 174, 95, 235)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__29 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__29_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "buildArchive"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__30 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__30_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__30_value),LEAN_SCALAR_PTR_LITERAL(13, 161, 176, 165, 88, 62, 216, 20)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__31 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__31_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "releaseRepo"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__32 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__32_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__32_value),LEAN_SCALAR_PTR_LITERAL(200, 115, 184, 27, 119, 80, 150, 143)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__33 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__33_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "irDir"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__34 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__34_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__34_value),LEAN_SCALAR_PTR_LITERAL(103, 157, 139, 154, 172, 117, 115, 135)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__35 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__35_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "binDir"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__36 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__36_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__36_value),LEAN_SCALAR_PTR_LITERAL(76, 64, 142, 71, 135, 199, 112, 75)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__37 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__37_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "nativeLibDir"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__38 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__38_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__38_value),LEAN_SCALAR_PTR_LITERAL(82, 8, 215, 104, 60, 212, 87, 97)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__39 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__39_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "leanLibDir"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__40 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__40_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__40_value),LEAN_SCALAR_PTR_LITERAL(1, 89, 218, 214, 52, 197, 188, 252)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__41 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__41_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "buildDir"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__42 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__42_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__42_value),LEAN_SCALAR_PTR_LITERAL(249, 192, 208, 78, 51, 18, 78, 228)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__43 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__43_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "moreGlobalServerArgs"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__44 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__44_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__44_value),LEAN_SCALAR_PTR_LITERAL(217, 219, 52, 240, 88, 87, 45, 147)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__45 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__45_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "manifestFile"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__46 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__46_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__46_value),LEAN_SCALAR_PTR_LITERAL(119, 77, 202, 12, 106, 133, 208, 66)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__47 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__47_value;
static const lean_string_object l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "bootstrap"};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__48 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__48_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__48_value),LEAN_SCALAR_PTR_LITERAL(166, 243, 17, 14, 190, 232, 38, 153)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__49 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__49_value;
lean_object* l_Lake_PackageConfig_bootstrap___proj(lean_object*, lean_object*);
lean_object* l_Lake_PackageConfig_toLeanConfig___proj(lean_object*, lean_object*);
lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj(lean_object*, lean_object*);
lean_object* l_Lake_PackageConfig_allowImportAll___proj(lean_object*, lean_object*);
lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj(lean_object*, lean_object*);
lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj(lean_object*, lean_object*);
lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj(lean_object*, lean_object*);
lean_object* l_Lake_PackageConfig_reservoir___proj(lean_object*, lean_object*);
lean_object* l_Lake_PackageConfig_readmeFile___proj(lean_object*, lean_object*);
lean_object* l_Lake_PackageConfig_licenseFiles___proj(lean_object*, lean_object*);
lean_object* l_Lake_PackageConfig_license___proj(lean_object*, lean_object*);
lean_object* l_Lake_PackageConfig_homepage___proj(lean_object*, lean_object*);
lean_object* l_Lake_PackageConfig_keywords___proj(lean_object*, lean_object*);
lean_object* l_Lake_PackageConfig_description___proj(lean_object*, lean_object*);
lean_object* l_Lake_PackageConfig_versionTags___proj(lean_object*, lean_object*);
lean_object* l_Lake_PackageConfig_version___proj(lean_object*, lean_object*);
uint8_t l_Lake_instDecidableEqStdVer_decEq(lean_object*, lean_object*);
lean_object* l_Lake_PackageConfig_lintDriverArgs___proj(lean_object*, lean_object*);
lean_object* l_Lake_PackageConfig_lintDriver___proj(lean_object*, lean_object*);
lean_object* l_Lake_PackageConfig_testDriverArgs___proj(lean_object*, lean_object*);
lean_object* l_Lake_PackageConfig_testDriver___proj(lean_object*, lean_object*);
lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj(lean_object*, lean_object*);
lean_object* l_Lake_PackageConfig_buildArchive___proj(lean_object*, lean_object*);
lean_object* l_Lake_PackageConfig_releaseRepo___proj(lean_object*, lean_object*);
lean_object* l_Lake_PackageConfig_irDir___proj(lean_object*, lean_object*);
lean_object* l_Lake_PackageConfig_binDir___proj(lean_object*, lean_object*);
lean_object* l_Lake_PackageConfig_nativeLibDir___proj(lean_object*, lean_object*);
lean_object* l_Lake_PackageConfig_leanLibDir___proj(lean_object*, lean_object*);
lean_object* l_Lake_PackageConfig_buildDir___proj(lean_object*, lean_object*);
lean_object* l_Lake_PackageConfig_srcDir___proj(lean_object*, lean_object*);
lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj(lean_object*, lean_object*);
lean_object* l_Lake_PackageConfig_precompileModules___proj(lean_object*, lean_object*);
lean_object* l_Lake_PackageConfig_extraDepTargets___proj(lean_object*, lean_object*);
lean_object* l_Lake_PackageConfig_manifestFile___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_instToToml___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_instToToml___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_instToToml(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_Package_mkTomlTargets___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_Package_mkTomlTargets___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_CLI_Translate_Toml_0__Lake_Package_mkTomlTargets___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_Package_mkTomlTargets___closed__0 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_Package_mkTomlTargets___closed__0_value;
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_CLI_Translate_Toml_0__Lake_Package_mkTomlTargets___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_Package_mkTomlTargets___closed__1 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_Package_mkTomlTargets___closed__1_value;
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_CLI_Translate_Toml_0__Lake_Package_mkTomlTargets___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_Package_mkTomlTargets___closed__2 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_Package_mkTomlTargets___closed__2_value;
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_CLI_Translate_Toml_0__Lake_Package_mkTomlTargets___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_Package_mkTomlTargets___closed__3 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_Package_mkTomlTargets___closed__3_value;
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_CLI_Translate_Toml_0__Lake_Package_mkTomlTargets___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_Package_mkTomlTargets___closed__4 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_Package_mkTomlTargets___closed__4_value;
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_CLI_Translate_Toml_0__Lake_Package_mkTomlTargets___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_Package_mkTomlTargets___closed__5 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_Package_mkTomlTargets___closed__5_value;
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_CLI_Translate_Toml_0__Lake_Package_mkTomlTargets___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_Package_mkTomlTargets___closed__6 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_Package_mkTomlTargets___closed__6_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_Package_mkTomlTargets___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_Package_mkTomlTargets___closed__0_value),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_Package_mkTomlTargets___closed__1_value)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_Package_mkTomlTargets___closed__7 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_Package_mkTomlTargets___closed__7_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_Package_mkTomlTargets___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_Package_mkTomlTargets___closed__7_value),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_Package_mkTomlTargets___closed__2_value),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_Package_mkTomlTargets___closed__3_value),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_Package_mkTomlTargets___closed__4_value),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_Package_mkTomlTargets___closed__5_value)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_Package_mkTomlTargets___closed__8 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_Package_mkTomlTargets___closed__8_value;
static const lean_ctor_object l___private_Lake_CLI_Translate_Toml_0__Lake_Package_mkTomlTargets___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_Package_mkTomlTargets___closed__8_value),((lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_Package_mkTomlTargets___closed__6_value)}};
static const lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_Package_mkTomlTargets___closed__9 = (const lean_object*)&l___private_Lake_CLI_Translate_Toml_0__Lake_Package_mkTomlTargets___closed__9_value;
lean_object* l_Array_filterMapM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_Package_mkTomlTargets(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
extern lean_object* l_Lake_InputDir_keyword;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__0___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__2_spec__3(lean_object*, size_t, size_t, lean_object*);
extern lean_object* l_Lake_InputFile_keyword;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__4_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "lean_lib"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__4_spec__7___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__4_spec__7___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__4_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__4_spec__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 123, 8, 14, 20, 41, 164, 170)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__4_spec__7___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__4_spec__7___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__4_spec__7(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_mkTomlConfig_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_mkTomlConfig_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_mkTomlConfig_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_mkTomlConfig_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__3_spec__5(lean_object*, size_t, size_t, lean_object*);
extern lean_object* l_Lake_LeanExe_keyword;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__3___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Package_mkTomlConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "require"};
static const lean_object* l_Lake_Package_mkTomlConfig___closed__0 = (const lean_object*)&l_Lake_Package_mkTomlConfig___closed__0_value;
static const lean_ctor_object l_Lake_Package_mkTomlConfig___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Package_mkTomlConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 47, 13, 250, 185, 150, 86, 12)}};
static const lean_object* l_Lake_Package_mkTomlConfig___closed__1 = (const lean_object*)&l_Lake_Package_mkTomlConfig___closed__1_value;
static const lean_string_object l_Lake_Package_mkTomlConfig___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "defaultTargets"};
static const lean_object* l_Lake_Package_mkTomlConfig___closed__2 = (const lean_object*)&l_Lake_Package_mkTomlConfig___closed__2_value;
static const lean_ctor_object l_Lake_Package_mkTomlConfig___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Package_mkTomlConfig___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 201, 186, 107, 100, 91, 39, 20)}};
static const lean_object* l_Lake_Package_mkTomlConfig___closed__3 = (const lean_object*)&l_Lake_Package_mkTomlConfig___closed__3_value;
extern lean_object* l_Lake_LeanLib_keyword;
LEAN_EXPORT lean_object* l_Lake_Package_mkTomlConfig(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_CLI_Translate_Toml_0__Lake_instBEqFilePath__lake___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_System_FilePath_normalize(x_1);
x_4 = l_System_FilePath_normalize(x_2);
x_5 = lean_string_dec_eq(x_3, x_4);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_instBEqFilePath__lake___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lake_CLI_Translate_Toml_0__Lake_instBEqFilePath__lake___lam__0(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_instEncodeFieldOfToToml___redArg(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_instEncodeFieldOfToToml___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_CLI_Translate_Toml_0__Lake_instEncodeFieldOfToToml___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_instEncodeFieldOfToToml(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc_ref(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_instEncodeFieldOfToToml___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_CLI_Translate_Toml_0__Lake_instEncodeFieldOfToToml(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_Toml_Table_insertField___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_Toml_Table_insertField(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_2(x_4, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_Toml_Table_insertField___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lake_CLI_Translate_Toml_0__Lake_Toml_Table_insertField(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfSmartInsertOfConfigField___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_apply_1(x_6, x_4);
x_8 = lean_apply_3(x_2, x_3, x_7, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfSmartInsertOfConfigField___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfSmartInsertOfConfigField___redArg___lam__0), 5, 3);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfSmartInsertOfConfigField(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfSmartInsertOfConfigField___redArg___lam__0), 5, 3);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_4);
lean_closure_set(x_6, 2, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
lean_dec_ref(x_1);
lean_inc(x_5);
x_9 = lean_apply_1(x_7, x_5);
x_10 = lean_apply_1(x_8, x_5);
lean_inc(x_9);
x_11 = lean_apply_2(x_2, x_9, x_10);
x_12 = lean_unbox(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_14 = lean_apply_1(x_3, x_9);
x_15 = l_Lake_Toml_RBDict_insert___redArg(x_13, x_4, x_14, x_6);
return x_15;
}
else
{
lean_dec(x_9);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0), 6, 4);
lean_closure_set(x_5, 0, x_4);
lean_closure_set(x_5, 1, x_3);
lean_closure_set(x_5, 2, x_2);
lean_closure_set(x_5, 3, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0), 6, 4);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_5);
lean_closure_set(x_7, 2, x_4);
lean_closure_set(x_7, 3, x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlLeanVer___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lake_StdVer_toString(x_1);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlBuildType___lam__0(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lake_BuildType_toString(x_1);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlBuildType___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lake_instToTomlBuildType___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlGlob___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lake_Glob_toString(x_1);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlBackend___lam__0(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lake_Backend_toString(x_1);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlBackend___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lake_instToTomlBackend___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instSmartInsertBackend___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (x_2 == 2)
{
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_Lake_Backend_toString(x_2);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
x_7 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_8 = l_Lake_Toml_RBDict_insert___redArg(x_7, x_1, x_6, x_3);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instSmartInsertBackend___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
x_5 = l_Lake_instSmartInsertBackend___lam__0(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_encodeLeanOptionValue(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
lean_dec_ref(x_1);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
case 1:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get_uint8(x_1, 0);
lean_dec_ref(x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_5);
return x_7;
}
default: 
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_box(0);
x_10 = lean_nat_to_int(x_8);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_encodeLeanOptions_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_6 = lean_array_uget_borrowed(x_1, x_2);
x_7 = lean_ctor_get(x_6, 0);
x_8 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_8);
x_9 = l_Lake_Toml_encodeLeanOptionValue(x_8);
x_10 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
lean_inc(x_7);
x_11 = l_Lake_Toml_RBDict_insert___redArg(x_10, x_7, x_9, x_4);
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
x_4 = x_11;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_encodeLeanOptions_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_encodeLeanOptions_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
static lean_object* _init_l_Lake_Toml_encodeLeanOptions___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_2 = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_encodeLeanOptions(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_obj_once(&l_Lake_Toml_encodeLeanOptions___closed__0, &l_Lake_Toml_encodeLeanOptions___closed__0_once, _init_l_Lake_Toml_encodeLeanOptions___closed__0);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
return x_2;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_4, x_4);
if (x_6 == 0)
{
if (x_5 == 0)
{
return x_2;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_encodeLeanOptions_spec__0(x_1, x_7, x_8, x_2);
return x_9;
}
}
else
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = 0;
x_11 = lean_usize_of_nat(x_4);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_encodeLeanOptions_spec__0(x_1, x_10, x_11, x_2);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_encodeLeanOptions___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Toml_encodeLeanOptions(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlArrayLeanOption___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = l_Lake_Toml_encodeLeanOptions(x_1);
x_4 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlArrayLeanOption___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instToTomlArrayLeanOption___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_encodeSingleton_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_17; 
x_5 = lean_ctor_get(x_4, 0);
x_17 = !lean_is_exclusive(x_4);
if (x_17 == 0)
{
x_6 = x_4;
x_7 = x_17;
goto block_16;
}
else
{
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_box(0);
x_9 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_10 = lean_obj_once(&l_Lake_Toml_encodeLeanOptions___closed__0, &l_Lake_Toml_encodeLeanOptions___closed__0_once, _init_l_Lake_Toml_encodeLeanOptions___closed__0);
x_11 = l_Lake_Toml_RBDict_insert___redArg(x_9, x_2, x_5, x_10);
x_12 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
if (x_7 == 0)
{
lean_ctor_set(x_6, 0, x_12);
x_13 = x_6;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_encodeSingleton_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_1(x_2, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_dec(x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_18; 
x_6 = lean_ctor_get(x_5, 0);
x_18 = !lean_is_exclusive(x_5);
if (x_18 == 0)
{
x_7 = x_5;
x_8 = x_18;
goto block_17;
}
else
{
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_box(0);
x_10 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_11 = lean_obj_once(&l_Lake_Toml_encodeLeanOptions___closed__0, &l_Lake_Toml_encodeLeanOptions___closed__0_once, _init_l_Lake_Toml_encodeLeanOptions___closed__0);
x_12 = l_Lake_Toml_RBDict_insert___redArg(x_10, x_3, x_6, x_11);
x_13 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_13);
x_14 = x_7;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_13);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_toToml_x3f___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc_ref(x_1);
x_3 = lean_alloc_closure((void*)(l_Lake_Pattern_toToml_x3f), 4, 3);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, lean_box(0));
lean_closure_set(x_3, 2, x_1);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_4; lean_object* x_5; 
lean_dec_ref(x_3);
x_4 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_2);
x_5 = l_Lake_Pattern_toToml_x3f___redArg(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_19; 
x_6 = lean_ctor_get(x_5, 0);
x_19 = !lean_is_exclusive(x_5);
if (x_19 == 0)
{
x_7 = x_5;
x_8 = x_19;
goto block_18;
}
else
{
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = ((lean_object*)(l_Lake_PatternDescr_toToml_x3f___redArg___closed__1));
x_10 = lean_box(0);
x_11 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_12 = lean_obj_once(&l_Lake_Toml_encodeLeanOptions___closed__0, &l_Lake_Toml_encodeLeanOptions___closed__0_once, _init_l_Lake_Toml_encodeLeanOptions___closed__0);
x_13 = l_Lake_Toml_RBDict_insert___redArg(x_11, x_9, x_6, x_12);
x_14 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_14);
x_15 = x_7;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_14);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
}
case 1:
{
lean_object* x_20; lean_object* x_21; 
lean_dec_ref(x_1);
x_20 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_20);
lean_dec_ref(x_2);
x_21 = l_Lake_Toml_encodeArray_x3f___redArg(x_3, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_box(0);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_37; 
x_23 = lean_ctor_get(x_21, 0);
x_37 = !lean_is_exclusive(x_21);
if (x_37 == 0)
{
x_24 = x_21;
x_25 = x_37;
goto block_36;
}
else
{
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_box(0);
x_25 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_26 = ((lean_object*)(l_Lake_PatternDescr_toToml_x3f___redArg___closed__3));
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_23);
x_29 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_30 = lean_obj_once(&l_Lake_Toml_encodeLeanOptions___closed__0, &l_Lake_Toml_encodeLeanOptions___closed__0_once, _init_l_Lake_Toml_encodeLeanOptions___closed__0);
x_31 = l_Lake_Toml_RBDict_insert___redArg(x_29, x_26, x_28, x_30);
x_32 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_31);
if (x_25 == 0)
{
lean_ctor_set(x_24, 0, x_32);
x_33 = x_24;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_32);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
}
}
case 2:
{
lean_object* x_38; lean_object* x_39; 
lean_dec_ref(x_1);
x_38 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_38);
lean_dec_ref(x_2);
x_39 = l_Lake_Toml_encodeArray_x3f___redArg(x_3, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = lean_box(0);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_55; 
x_41 = lean_ctor_get(x_39, 0);
x_55 = !lean_is_exclusive(x_39);
if (x_55 == 0)
{
x_42 = x_39;
x_43 = x_55;
goto block_54;
}
else
{
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_box(0);
x_43 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_44 = ((lean_object*)(l_Lake_PatternDescr_toToml_x3f___redArg___closed__5));
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_41);
x_47 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_48 = lean_obj_once(&l_Lake_Toml_encodeLeanOptions___closed__0, &l_Lake_Toml_encodeLeanOptions___closed__0_once, _init_l_Lake_Toml_encodeLeanOptions___closed__0);
x_49 = l_Lake_Toml_RBDict_insert___redArg(x_47, x_44, x_46, x_48);
x_50 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_50, 0, x_45);
lean_ctor_set(x_50, 1, x_49);
if (x_43 == 0)
{
lean_ctor_set(x_42, 0, x_50);
x_51 = x_42;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_50);
x_51 = x_53;
goto block_52;
}
block_52:
{
return x_51;
}
}
}
}
default: 
{
lean_object* x_56; lean_object* x_57; 
lean_dec_ref(x_3);
x_56 = lean_ctor_get(x_2, 0);
lean_inc(x_56);
lean_dec_ref(x_2);
x_57 = lean_apply_1(x_1, x_56);
return x_57;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_toToml_x3f___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
lean_dec_ref(x_2);
switch (lean_obj_tag(x_3)) {
case 0:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_16; 
lean_dec_ref(x_1);
x_16 = lean_box(0);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_4, 0);
lean_inc(x_17);
lean_dec_ref(x_4);
x_18 = l_Lake_PatternDescr_toToml_x3f___redArg(x_1, x_17);
return x_18;
}
}
case 1:
{
lean_object* x_19; 
lean_dec(x_4);
lean_dec_ref(x_1);
x_19 = lean_ctor_get(x_3, 0);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_3, 1);
x_21 = ((lean_object*)(l_Lake_Pattern_toToml_x3f___redArg___closed__2));
x_22 = lean_string_dec_eq(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = ((lean_object*)(l_Lake_Pattern_toToml_x3f___redArg___closed__3));
x_24 = lean_string_dec_eq(x_20, x_23);
if (x_24 == 0)
{
goto block_15;
}
else
{
lean_object* x_25; 
lean_dec_ref(x_3);
x_25 = ((lean_object*)(l_Lake_Pattern_toToml_x3f___redArg___closed__6));
return x_25;
}
}
else
{
lean_object* x_26; 
lean_dec_ref(x_3);
x_26 = lean_box(0);
return x_26;
}
}
else
{
goto block_15;
}
}
default: 
{
lean_dec(x_4);
lean_dec_ref(x_1);
goto block_15;
}
}
block_15:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_5 = lean_box(0);
x_6 = ((lean_object*)(l_Lake_Pattern_toToml_x3f___redArg___closed__1));
x_7 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_8 = lean_obj_once(&l_Lake_Toml_encodeLeanOptions___closed__0, &l_Lake_Toml_encodeLeanOptions___closed__0_once, _init_l_Lake_Toml_encodeLeanOptions___closed__0);
x_9 = 1;
x_10 = l_Lean_Name_toString(x_3, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lake_Toml_RBDict_insert___redArg(x_7, x_6, x_11, x_8);
x_13 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_toToml_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Pattern_toToml_x3f___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_toToml_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_PatternDescr_toToml_x3f___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fPattern___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_Pattern_toToml_x3f), 4, 3);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, lean_box(0));
lean_closure_set(x_2, 2, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fPattern(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lake_Pattern_toToml_x3f), 4, 3);
lean_closure_set(x_4, 0, lean_box(0));
lean_closure_set(x_4, 1, lean_box(0));
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fPatternDescr___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_PatternDescr_toToml_x3f), 4, 3);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, lean_box(0));
lean_closure_set(x_2, 2, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instToToml_x3fPatternDescr(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lake_PatternDescr_toToml_x3f), 4, 3);
lean_closure_set(x_4, 0, lean_box(0));
lean_closure_set(x_4, 1, lean_box(0));
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_StrPatDescr_toToml_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_7, x_2, x_9);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_StrPatDescr_toToml_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_StrPatDescr_toToml_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_toToml(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; size_t x_4; size_t x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
lean_dec_ref(x_1);
x_3 = lean_box(0);
x_4 = lean_array_size(x_2);
x_5 = 0;
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_StrPatDescr_toToml_spec__0(x_4, x_5, x_2);
x_7 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_8);
lean_dec_ref(x_1);
x_9 = lean_box(0);
x_10 = ((lean_object*)(l_Lake_StrPatDescr_toToml___closed__1));
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_8);
x_12 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_13 = lean_obj_once(&l_Lake_Toml_encodeLeanOptions___closed__0, &l_Lake_Toml_encodeLeanOptions___closed__0_once, _init_l_Lake_Toml_encodeLeanOptions___closed__0);
x_14 = l_Lake_Toml_RBDict_insert___redArg(x_12, x_10, x_11, x_13);
x_15 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
default: 
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_16);
lean_dec_ref(x_1);
x_17 = lean_box(0);
x_18 = ((lean_object*)(l_Lake_StrPatDescr_toToml___closed__3));
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_16);
x_20 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_21 = lean_obj_once(&l_Lake_Toml_encodeLeanOptions___closed__0, &l_Lake_Toml_encodeLeanOptions___closed__0_once, _init_l_Lake_Toml_encodeLeanOptions___closed__0);
x_22 = l_Lake_Toml_RBDict_insert___redArg(x_20, x_18, x_19, x_21);
x_23 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00Lake_PathPatDescr_toToml_x3f_spec__0_spec__0___redArg(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
lean_dec_ref(x_1);
x_3 = l_Lake_Pattern_toToml_x3f___at___00Lake_PathPatDescr_toToml_x3f_spec__0___redArg(x_2);
if (lean_obj_tag(x_3) == 0)
{
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_17; 
x_4 = lean_ctor_get(x_3, 0);
x_17 = !lean_is_exclusive(x_3);
if (x_17 == 0)
{
x_5 = x_3;
x_6 = x_17;
goto block_16;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = ((lean_object*)(l_Lake_PatternDescr_toToml_x3f___redArg___closed__1));
x_8 = lean_box(0);
x_9 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_10 = lean_obj_once(&l_Lake_Toml_encodeLeanOptions___closed__0, &l_Lake_Toml_encodeLeanOptions___closed__0_once, _init_l_Lake_Toml_encodeLeanOptions___closed__0);
x_11 = l_Lake_Toml_RBDict_insert___redArg(x_9, x_7, x_4, x_10);
x_12 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
if (x_6 == 0)
{
lean_ctor_set(x_5, 0, x_12);
x_13 = x_5;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
}
case 1:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_18);
lean_dec_ref(x_1);
x_19 = l_Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00Lake_PathPatDescr_toToml_x3f_spec__0_spec__0_spec__1___redArg(x_18);
lean_dec_ref(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_box(0);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_35; 
x_21 = lean_ctor_get(x_19, 0);
x_35 = !lean_is_exclusive(x_19);
if (x_35 == 0)
{
x_22 = x_19;
x_23 = x_35;
goto block_34;
}
else
{
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_box(0);
x_23 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = ((lean_object*)(l_Lake_PatternDescr_toToml_x3f___redArg___closed__3));
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_21);
x_27 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_28 = lean_obj_once(&l_Lake_Toml_encodeLeanOptions___closed__0, &l_Lake_Toml_encodeLeanOptions___closed__0_once, _init_l_Lake_Toml_encodeLeanOptions___closed__0);
x_29 = l_Lake_Toml_RBDict_insert___redArg(x_27, x_24, x_26, x_28);
x_30 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_29);
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_30);
x_31 = x_22;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_30);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
}
}
case 2:
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_36);
lean_dec_ref(x_1);
x_37 = l_Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00Lake_PathPatDescr_toToml_x3f_spec__0_spec__0_spec__1___redArg(x_36);
lean_dec_ref(x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_box(0);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_53; 
x_39 = lean_ctor_get(x_37, 0);
x_53 = !lean_is_exclusive(x_37);
if (x_53 == 0)
{
x_40 = x_37;
x_41 = x_53;
goto block_52;
}
else
{
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_box(0);
x_41 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_42 = ((lean_object*)(l_Lake_PatternDescr_toToml_x3f___redArg___closed__5));
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_39);
x_45 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_46 = lean_obj_once(&l_Lake_Toml_encodeLeanOptions___closed__0, &l_Lake_Toml_encodeLeanOptions___closed__0_once, _init_l_Lake_Toml_encodeLeanOptions___closed__0);
x_47 = l_Lake_Toml_RBDict_insert___redArg(x_45, x_42, x_44, x_46);
x_48 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_48, 0, x_43);
lean_ctor_set(x_48, 1, x_47);
if (x_41 == 0)
{
lean_ctor_set(x_40, 0, x_48);
x_49 = x_40;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_48);
x_49 = x_51;
goto block_50;
}
block_50:
{
return x_49;
}
}
}
}
default: 
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_62; 
x_54 = lean_ctor_get(x_1, 0);
x_62 = !lean_is_exclusive(x_1);
if (x_62 == 0)
{
x_55 = x_1;
x_56 = x_62;
goto block_61;
}
else
{
lean_inc(x_54);
lean_dec(x_1);
x_55 = lean_box(0);
x_56 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_57; lean_object* x_58; 
x_57 = l_Lake_StrPatDescr_toToml(x_54);
if (x_56 == 0)
{
lean_ctor_set_tag(x_55, 1);
lean_ctor_set(x_55, 0, x_57);
x_58 = x_55;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_57);
x_58 = x_60;
goto block_59;
}
block_59:
{
return x_58;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_toToml_x3f___at___00Lake_PathPatDescr_toToml_x3f_spec__0___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
lean_dec_ref(x_1);
switch (lean_obj_tag(x_2)) {
case 0:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_15; 
x_15 = lean_box(0);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
lean_dec_ref(x_3);
x_17 = l_Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00Lake_PathPatDescr_toToml_x3f_spec__0_spec__0___redArg(x_16);
return x_17;
}
}
case 1:
{
lean_object* x_18; 
lean_dec(x_3);
x_18 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_2, 1);
x_20 = ((lean_object*)(l_Lake_Pattern_toToml_x3f___redArg___closed__2));
x_21 = lean_string_dec_eq(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = ((lean_object*)(l_Lake_Pattern_toToml_x3f___redArg___closed__3));
x_23 = lean_string_dec_eq(x_19, x_22);
if (x_23 == 0)
{
goto block_14;
}
else
{
lean_object* x_24; 
lean_dec_ref(x_2);
x_24 = ((lean_object*)(l_Lake_Pattern_toToml_x3f___redArg___closed__6));
return x_24;
}
}
else
{
lean_object* x_25; 
lean_dec_ref(x_2);
x_25 = lean_box(0);
return x_25;
}
}
else
{
goto block_14;
}
}
default: 
{
lean_dec(x_3);
goto block_14;
}
}
block_14:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = lean_box(0);
x_5 = ((lean_object*)(l_Lake_Pattern_toToml_x3f___redArg___closed__1));
x_6 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_7 = lean_obj_once(&l_Lake_Toml_encodeLeanOptions___closed__0, &l_Lake_Toml_encodeLeanOptions___closed__0_once, _init_l_Lake_Toml_encodeLeanOptions___closed__0);
x_8 = 1;
x_9 = l_Lean_Name_toString(x_2, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lake_Toml_RBDict_insert___redArg(x_6, x_5, x_10, x_7);
x_12 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00Lake_PathPatDescr_toToml_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
if (lean_obj_tag(x_4) == 0)
{
x_5 = x_4;
goto block_9;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec_ref(x_4);
x_12 = lean_array_uget_borrowed(x_1, x_2);
lean_inc(x_12);
x_13 = l_Lake_Pattern_toToml_x3f___at___00Lake_PathPatDescr_toToml_x3f_spec__0___redArg(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
lean_dec(x_11);
x_14 = lean_box(0);
x_5 = x_14;
goto block_9;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_23; 
x_15 = lean_ctor_get(x_13, 0);
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
x_16 = x_13;
x_17 = x_23;
goto block_22;
}
else
{
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_array_push(x_11, x_15);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_18);
x_19 = x_16;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
x_5 = x_19;
goto block_9;
}
}
}
}
}
else
{
return x_4;
}
block_9:
{
size_t x_6; size_t x_7; 
x_6 = 1;
x_7 = lean_usize_add(x_2, x_6);
x_2 = x_7;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00Lake_PathPatDescr_toToml_x3f_spec__0_spec__0_spec__1___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = ((lean_object*)(l_Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00Lake_PathPatDescr_toToml_x3f_spec__0_spec__0_spec__1___redArg___closed__1));
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
if (x_5 == 0)
{
return x_3;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_4, x_4);
if (x_6 == 0)
{
if (x_5 == 0)
{
return x_3;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00Lake_PathPatDescr_toToml_x3f_spec__0_spec__0_spec__1_spec__2___redArg(x_1, x_7, x_8, x_3);
return x_9;
}
}
else
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = 0;
x_11 = lean_usize_of_nat(x_4);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00Lake_PathPatDescr_toToml_x3f_spec__0_spec__0_spec__1_spec__2___redArg(x_1, x_10, x_11, x_3);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00Lake_PathPatDescr_toToml_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00Lake_PathPatDescr_toToml_x3f_spec__0_spec__0_spec__1___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00Lake_PathPatDescr_toToml_x3f_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00Lake_PathPatDescr_toToml_x3f_spec__0_spec__0_spec__1_spec__2___redArg(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_toToml_x3f(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
lean_dec_ref(x_1);
x_3 = l_Lake_Pattern_toToml_x3f___at___00Lake_PathPatDescr_toToml_x3f_spec__0___redArg(x_2);
if (lean_obj_tag(x_3) == 0)
{
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_17; 
x_4 = lean_ctor_get(x_3, 0);
x_17 = !lean_is_exclusive(x_3);
if (x_17 == 0)
{
x_5 = x_3;
x_6 = x_17;
goto block_16;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = ((lean_object*)(l_Lake_PathPatDescr_toToml_x3f___closed__1));
x_8 = lean_box(0);
x_9 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_10 = lean_obj_once(&l_Lake_Toml_encodeLeanOptions___closed__0, &l_Lake_Toml_encodeLeanOptions___closed__0_once, _init_l_Lake_Toml_encodeLeanOptions___closed__0);
x_11 = l_Lake_Toml_RBDict_insert___redArg(x_9, x_7, x_4, x_10);
x_12 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
if (x_6 == 0)
{
lean_ctor_set(x_5, 0, x_12);
x_13 = x_5;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
}
case 1:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_18);
lean_dec_ref(x_1);
x_19 = l_Lake_Pattern_toToml_x3f___at___00Lake_PathPatDescr_toToml_x3f_spec__0___redArg(x_18);
if (lean_obj_tag(x_19) == 0)
{
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_33; 
x_20 = lean_ctor_get(x_19, 0);
x_33 = !lean_is_exclusive(x_19);
if (x_33 == 0)
{
x_21 = x_19;
x_22 = x_33;
goto block_32;
}
else
{
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = ((lean_object*)(l_Lake_PathPatDescr_toToml_x3f___closed__3));
x_24 = lean_box(0);
x_25 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_26 = lean_obj_once(&l_Lake_Toml_encodeLeanOptions___closed__0, &l_Lake_Toml_encodeLeanOptions___closed__0_once, _init_l_Lake_Toml_encodeLeanOptions___closed__0);
x_27 = l_Lake_Toml_RBDict_insert___redArg(x_25, x_23, x_20, x_26);
x_28 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_27);
if (x_22 == 0)
{
lean_ctor_set(x_21, 0, x_28);
x_29 = x_21;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_28);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
default: 
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_34);
lean_dec_ref(x_1);
x_35 = l_Lake_Pattern_toToml_x3f___at___00Lake_PathPatDescr_toToml_x3f_spec__0___redArg(x_34);
if (lean_obj_tag(x_35) == 0)
{
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_49; 
x_36 = lean_ctor_get(x_35, 0);
x_49 = !lean_is_exclusive(x_35);
if (x_49 == 0)
{
x_37 = x_35;
x_38 = x_49;
goto block_48;
}
else
{
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_box(0);
x_38 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_39 = ((lean_object*)(l_Lake_PathPatDescr_toToml_x3f___closed__5));
x_40 = lean_box(0);
x_41 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_42 = lean_obj_once(&l_Lake_Toml_encodeLeanOptions___closed__0, &l_Lake_Toml_encodeLeanOptions___closed__0_once, _init_l_Lake_Toml_encodeLeanOptions___closed__0);
x_43 = l_Lake_Toml_RBDict_insert___redArg(x_41, x_39, x_36, x_42);
x_44 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_44, 0, x_40);
lean_ctor_set(x_44, 1, x_43);
if (x_38 == 0)
{
lean_ctor_set(x_37, 0, x_44);
x_45 = x_37;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_44);
x_45 = x_47;
goto block_46;
}
block_46:
{
return x_45;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_toToml_x3f___at___00Lake_PathPatDescr_toToml_x3f_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Pattern_toToml_x3f___at___00Lake_PathPatDescr_toToml_x3f_spec__0___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00Lake_PathPatDescr_toToml_x3f_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00Lake_PathPatDescr_toToml_x3f_spec__0_spec__0___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00Lake_PathPatDescr_toToml_x3f_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00Lake_PathPatDescr_toToml_x3f_spec__0_spec__0_spec__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00Lake_PathPatDescr_toToml_x3f_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00Lake_PathPatDescr_toToml_x3f_spec__0_spec__0_spec__1(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00Lake_PathPatDescr_toToml_x3f_spec__0_spec__0_spec__1_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00Lake_PathPatDescr_toToml_x3f_spec__0_spec__0_spec__1_spec__2___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00Lake_PathPatDescr_toToml_x3f_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00Lake_PathPatDescr_toToml_x3f_spec__0_spec__0_spec__1_spec__2(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_encodeFacets_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lake_Name_eraseHead(x_5);
x_9 = l_Lean_Name_toString(x_8, x_4);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_14 = lean_array_uset(x_7, x_2, x_11);
x_2 = x_13;
x_3 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_encodeFacets_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_encodeFacets_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_encodeFacets(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_array_size(x_1);
x_3 = 0;
x_4 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_encodeFacets_spec__0(x_2, x_3, x_1);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_instEncodeFieldLeanLibConfigMkStr1ArrayName(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instEncodeFieldLeanLibConfigMkStr1ArrayName___closed__0));
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_instEncodeFieldLeanLibConfigMkStr1ArrayName___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_CLI_Translate_Toml_0__Lake_instEncodeFieldLeanLibConfigMkStr1ArrayName(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_instToTomlBuildKey___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lake_BuildKey_toString(x_1);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_instToTomlPartialBuildKey___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lake_PartialBuildKey_toString(x_1);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_instToTomlTarget(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instToTomlPartialBuildKey___closed__0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lake_Dependency_toToml_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 3);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 4);
lean_inc(x_6);
lean_dec_ref(x_2);
x_7 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lake_Dependency_toToml_spec__0_spec__0(x_1, x_5);
x_8 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
x_11 = l_Lake_Toml_RBDict_insert___redArg(x_8, x_3, x_10, x_7);
x_1 = x_11;
x_2 = x_6;
goto _start;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_toToml(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_31; lean_object* x_54; lean_object* x_55; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 4);
lean_inc(x_7);
lean_dec_ref(x_1);
x_54 = ((lean_object*)(l_Lake_Dependency_toToml___closed__9));
x_62 = ((lean_object*)(l_Lake_Dependency_toToml___closed__10));
x_63 = ((lean_object*)(l_Lake_Dependency_toToml___closed__12));
x_64 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_65 = 1;
x_66 = l_Lean_Name_toString(x_3, x_65);
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
x_69 = l_Lake_Toml_RBDict_insert___redArg(x_64, x_63, x_68, x_2);
x_70 = lean_string_dec_eq(x_4, x_62);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = ((lean_object*)(l_Lake_Dependency_toToml___closed__14));
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_67);
lean_ctor_set(x_72, 1, x_4);
x_73 = l_Lake_Toml_RBDict_insert___redArg(x_64, x_71, x_72, x_69);
x_55 = x_73;
goto block_61;
}
else
{
lean_dec_ref(x_4);
x_55 = x_69;
goto block_61;
}
block_20:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_10 = lean_obj_once(&l_Lake_Toml_encodeLeanOptions___closed__0, &l_Lake_Toml_encodeLeanOptions___closed__0_once, _init_l_Lake_Toml_encodeLeanOptions___closed__0);
x_11 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lake_Dependency_toToml_spec__0_spec__0(x_10, x_7);
x_12 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_12);
x_13 = lean_array_get_size(x_12);
lean_dec_ref(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = ((lean_object*)(l_Lake_Dependency_toToml___closed__1));
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_11);
x_19 = l_Lake_Toml_RBDict_insert___redArg(x_9, x_16, x_18, x_8);
return x_19;
}
else
{
lean_dec_ref(x_11);
return x_8;
}
}
block_30:
{
if (lean_obj_tag(x_22) == 0)
{
lean_dec(x_21);
x_8 = x_23;
goto block_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec_ref(x_22);
x_25 = l_Lake_mkRelPathString(x_24);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_29 = l_Lake_Toml_RBDict_insert___redArg(x_28, x_21, x_27, x_23);
x_8 = x_29;
goto block_20;
}
}
block_53:
{
if (lean_obj_tag(x_6) == 1)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_6, 0);
lean_inc(x_32);
lean_dec_ref(x_6);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc_ref(x_33);
lean_dec_ref(x_32);
x_34 = ((lean_object*)(l_Lake_PathPatDescr_toToml_x3f___closed__1));
x_35 = l_Lake_mkRelPathString(x_33);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_39 = l_Lake_Toml_RBDict_insert___redArg(x_38, x_34, x_37, x_31);
x_8 = x_39;
goto block_20;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_40 = lean_ctor_get(x_32, 0);
lean_inc_ref(x_40);
x_41 = lean_ctor_get(x_32, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_32, 2);
lean_inc(x_42);
lean_dec_ref(x_32);
x_43 = ((lean_object*)(l_Lake_Dependency_toToml___closed__3));
x_44 = ((lean_object*)(l_Lake_Dependency_toToml___closed__5));
x_45 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_40);
x_48 = l_Lake_Toml_RBDict_insert___redArg(x_45, x_44, x_47, x_31);
if (lean_obj_tag(x_41) == 0)
{
x_21 = x_43;
x_22 = x_42;
x_23 = x_48;
goto block_30;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_41, 0);
lean_inc(x_49);
lean_dec_ref(x_41);
x_50 = ((lean_object*)(l_Lake_Dependency_toToml___closed__7));
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_46);
lean_ctor_set(x_51, 1, x_49);
x_52 = l_Lake_Toml_RBDict_insert___redArg(x_45, x_50, x_51, x_48);
x_21 = x_43;
x_22 = x_42;
x_23 = x_52;
goto block_30;
}
}
}
else
{
lean_dec(x_6);
x_8 = x_31;
goto block_20;
}
}
block_61:
{
if (lean_obj_tag(x_5) == 0)
{
x_31 = x_55;
goto block_53;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_5, 0);
lean_inc(x_56);
lean_dec_ref(x_5);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
x_59 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_60 = l_Lake_Toml_RBDict_insert___redArg(x_59, x_54, x_58, x_55);
x_31 = x_60;
goto block_53;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lake_Dependency_toToml_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lake_Dependency_toToml_spec__0_spec__0(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTomlDependency___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_box(0);
x_3 = lean_obj_once(&l_Lake_Toml_encodeLeanOptions___closed__0, &l_Lake_Toml_encodeLeanOptions___closed__0_once, _init_l_Lake_Toml_encodeLeanOptions___closed__0);
x_4 = l_Lake_Dependency_toToml(x_1, x_3);
x_5 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__0___closed__0));
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_1, x_5);
x_7 = l_Nat_reprFast(x_6);
x_8 = lean_string_append(x_4, x_7);
lean_dec_ref(x_7);
x_9 = lean_box(0);
x_10 = l_Lean_Name_str___override(x_9, x_8);
x_11 = lean_mk_syntax_ident(x_10);
x_12 = lean_array_push(x_3, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__0(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__6));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__11));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec_ref(x_4);
lean_inc(x_9);
x_10 = l_Array_contains___redArg(x_1, x_2, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 5);
lean_inc(x_13);
lean_dec_ref(x_5);
x_14 = l_Lean_SourceInfo_fromRef(x_13, x_10);
lean_dec(x_13);
x_15 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__4));
x_16 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__5));
lean_inc(x_14);
x_17 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__7, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__7_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__7);
x_19 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__8));
lean_inc(x_12);
lean_inc(x_11);
x_20 = l_Lean_addMacroScope(x_11, x_19, x_12);
x_21 = lean_box(0);
lean_inc(x_14);
x_22 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_20);
lean_ctor_set(x_22, 3, x_21);
x_23 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__10));
x_24 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__12, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__12_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__12);
x_25 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__13));
x_26 = l_Lean_addMacroScope(x_11, x_25, x_12);
lean_inc(x_14);
x_27 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_27, 0, x_14);
lean_ctor_set(x_27, 1, x_24);
lean_ctor_set(x_27, 2, x_26);
lean_ctor_set(x_27, 3, x_21);
x_28 = l_Lean_instQuoteNameMkStr1___private__1(x_9);
lean_inc(x_14);
x_29 = l_Lean_Syntax_node2(x_14, x_23, x_27, x_28);
x_30 = l_Lean_Syntax_node4(x_14, x_15, x_3, x_17, x_22, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_6);
return x_31;
}
else
{
lean_object* x_32; 
lean_dec(x_9);
lean_dec_ref(x_5);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_3);
lean_ctor_set(x_32, 1, x_6);
return x_32;
}
}
}
}
static lean_object* _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__9));
x_2 = l_ReaderT_instMonad___redArg(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__20(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Array_mkArray0(lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__34(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__33));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__37(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__36));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__78(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__77));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__94(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lake_Dependency_toToml___closed__10));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__108(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__14));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__122(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__121));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_274; 
x_7 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__10, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__10_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__10);
x_8 = l_Lean_Macro_instMonadRefMacroM;
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 2);
x_274 = !lean_is_exclusive(x_3);
if (x_274 == 0)
{
lean_object* x_275; 
x_275 = lean_ctor_get(x_3, 1);
lean_dec(x_275);
x_11 = x_3;
x_12 = x_274;
goto block_273;
}
else
{
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_11 = lean_box(0);
x_12 = x_274;
goto block_273;
}
block_273:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_236; uint8_t x_237; 
x_13 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__11));
x_217 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__120));
x_218 = lean_alloc_closure((void*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1), 6, 2);
lean_closure_set(x_218, 0, x_217);
lean_closure_set(x_218, 1, x_4);
x_236 = lean_unsigned_to_nat(0u);
x_237 = lean_nat_dec_eq(x_10, x_236);
if (x_237 == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_238 = lean_ctor_get(x_5, 1);
x_239 = lean_ctor_get(x_5, 2);
x_240 = lean_ctor_get(x_5, 5);
x_241 = l_Lean_SourceInfo_fromRef(x_240, x_237);
x_242 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__76));
x_243 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__122, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__122_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__122);
x_244 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__124));
lean_inc(x_239);
lean_inc(x_238);
x_245 = l_Lean_addMacroScope(x_238, x_244, x_239);
x_246 = lean_box(0);
lean_inc(x_241);
x_247 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_247, 0, x_241);
lean_ctor_set(x_247, 1, x_243);
lean_ctor_set(x_247, 2, x_245);
lean_ctor_set(x_247, 3, x_246);
x_248 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__10));
x_249 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__126));
x_250 = ((lean_object*)(l_Lake_Dependency_toToml___closed__12));
x_251 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__127));
lean_inc(x_241);
x_252 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_252, 0, x_241);
lean_ctor_set(x_252, 1, x_251);
lean_inc(x_241);
x_253 = l_Lean_Syntax_node1(x_241, x_250, x_252);
lean_inc(x_241);
x_254 = l_Lean_Syntax_node1(x_241, x_249, x_253);
x_255 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__0___closed__0));
lean_inc(x_10);
x_256 = l_Nat_reprFast(x_10);
x_257 = lean_string_append(x_255, x_256);
lean_dec_ref(x_256);
x_258 = lean_box(0);
x_259 = l_Lean_Name_str___override(x_258, x_257);
x_260 = lean_mk_syntax_ident(x_259);
lean_inc(x_241);
x_261 = l_Lean_Syntax_node2(x_241, x_248, x_254, x_260);
x_262 = l_Lean_Syntax_node2(x_241, x_242, x_247, x_261);
x_219 = x_262;
x_220 = x_5;
x_221 = x_6;
goto block_235;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_263 = lean_ctor_get(x_5, 1);
x_264 = lean_ctor_get(x_5, 2);
x_265 = lean_ctor_get(x_5, 5);
x_266 = 0;
x_267 = l_Lean_SourceInfo_fromRef(x_265, x_266);
x_268 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__34, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__34_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__34);
x_269 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__35));
lean_inc(x_264);
lean_inc(x_263);
x_270 = l_Lean_addMacroScope(x_263, x_269, x_264);
x_271 = lean_box(0);
x_272 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_272, 0, x_267);
lean_ctor_set(x_272, 1, x_268);
lean_ctor_set(x_272, 2, x_270);
lean_ctor_set(x_272, 3, x_271);
x_219 = x_272;
x_220 = x_5;
x_221 = x_6;
goto block_235;
}
block_199:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
lean_inc(x_15);
x_20 = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop(lean_box(0), x_15, x_13, x_15, lean_box(0), x_16);
lean_dec(x_15);
lean_inc(x_2);
x_21 = l_Lean_Syntax_mkCApp(x_2, x_20);
x_22 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__13));
x_23 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__14));
lean_inc(x_2);
x_24 = l_Lean_Name_str___override(x_2, x_23);
x_25 = l_Lean_Name_append(x_22, x_24);
x_26 = 0;
x_27 = l_Lean_mkIdentFromRef___redArg(x_7, x_8, x_25, x_26);
lean_inc_ref(x_14);
x_28 = lean_apply_2(x_27, x_14, x_19);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec_ref(x_28);
x_31 = lean_ctor_get(x_14, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_14, 2);
lean_inc(x_32);
x_33 = lean_ctor_get(x_14, 5);
x_34 = l_Lean_SourceInfo_fromRef(x_33, x_26);
x_35 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__17));
x_36 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__19));
x_37 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__10));
x_38 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__20, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__20_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__20);
lean_inc(x_34);
if (x_12 == 0)
{
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 2, x_38);
lean_ctor_set(x_11, 1, x_37);
lean_ctor_set(x_11, 0, x_34);
x_39 = x_11;
goto block_188;
}
else
{
lean_object* x_189; 
x_189 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_189, 0, x_34);
lean_ctor_set(x_189, 1, x_37);
lean_ctor_set(x_189, 2, x_38);
x_39 = x_189;
goto block_188;
}
block_188:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_inc_ref_n(x_39, 7);
lean_inc(x_34);
x_40 = l_Lean_Syntax_node7(x_34, x_36, x_39, x_39, x_39, x_39, x_39, x_39, x_39);
x_41 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__22));
x_42 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__23));
lean_inc(x_34);
x_43 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_43, 0, x_34);
lean_ctor_set(x_43, 1, x_42);
x_44 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__25));
x_45 = lean_mk_empty_array_with_capacity(x_17);
x_46 = lean_box(2);
x_47 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_37);
lean_ctor_set(x_47, 2, x_45);
x_48 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__27));
x_49 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__29));
x_50 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__30));
lean_inc(x_34);
x_51 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_51, 0, x_34);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__12, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__12_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__12);
x_53 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__13));
lean_inc(x_32);
lean_inc(x_31);
x_54 = l_Lean_addMacroScope(x_31, x_53, x_32);
x_55 = lean_box(0);
lean_inc(x_34);
x_56 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_56, 0, x_34);
lean_ctor_set(x_56, 1, x_52);
lean_ctor_set(x_56, 2, x_54);
lean_ctor_set(x_56, 3, x_55);
lean_inc(x_34);
x_57 = l_Lean_Syntax_node1(x_34, x_37, x_56);
x_58 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__31));
lean_inc(x_34);
x_59 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_59, 0, x_34);
lean_ctor_set(x_59, 1, x_58);
lean_inc(x_21);
lean_inc_ref(x_59);
lean_inc(x_34);
x_60 = l_Lean_Syntax_node2(x_34, x_37, x_59, x_21);
x_61 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__32));
lean_inc(x_34);
x_62 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_62, 0, x_34);
lean_ctor_set(x_62, 1, x_61);
lean_inc_ref(x_62);
lean_inc_ref(x_39);
lean_inc_ref(x_51);
lean_inc(x_34);
x_63 = l_Lean_Syntax_node5(x_34, x_49, x_51, x_57, x_60, x_39, x_62);
x_64 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__34, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__34_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__34);
x_65 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__35));
lean_inc(x_32);
lean_inc(x_31);
x_66 = l_Lean_addMacroScope(x_31, x_65, x_32);
lean_inc(x_34);
x_67 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_67, 0, x_34);
lean_ctor_set(x_67, 1, x_64);
lean_ctor_set(x_67, 2, x_66);
lean_ctor_set(x_67, 3, x_55);
lean_inc(x_34);
x_68 = l_Lean_Syntax_node1(x_34, x_37, x_67);
x_69 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__37, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__37_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__37);
x_70 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__38));
lean_inc(x_32);
lean_inc(x_31);
x_71 = l_Lean_addMacroScope(x_31, x_70, x_32);
x_72 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__45));
lean_inc(x_34);
x_73 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_73, 0, x_34);
lean_ctor_set(x_73, 1, x_69);
lean_ctor_set(x_73, 2, x_71);
lean_ctor_set(x_73, 3, x_72);
lean_inc_ref(x_59);
lean_inc(x_34);
x_74 = l_Lean_Syntax_node2(x_34, x_37, x_59, x_73);
x_75 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__47));
x_76 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__48));
lean_inc(x_34);
x_77 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_77, 0, x_34);
lean_ctor_set(x_77, 1, x_76);
x_78 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__50));
x_79 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__52));
x_80 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__53));
lean_inc(x_34);
x_81 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_81, 0, x_34);
lean_ctor_set(x_81, 1, x_80);
x_82 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__54));
lean_inc(x_34);
x_83 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_83, 0, x_34);
lean_ctor_set(x_83, 1, x_82);
lean_inc_ref(x_83);
lean_inc_ref(x_81);
lean_inc(x_34);
x_84 = l_Lean_Syntax_node2(x_34, x_79, x_81, x_83);
x_85 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__56));
x_86 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__58));
lean_inc_ref(x_39);
lean_inc(x_34);
x_87 = l_Lean_Syntax_node1(x_34, x_86, x_39);
x_88 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__60));
lean_inc_ref(x_39);
lean_inc(x_34);
x_89 = l_Lean_Syntax_node1(x_34, x_88, x_39);
lean_inc_ref_n(x_39, 2);
lean_inc(x_34);
x_90 = l_Lean_Syntax_node6(x_34, x_85, x_81, x_39, x_87, x_89, x_39, x_83);
lean_inc(x_34);
x_91 = l_Lean_Syntax_node2(x_34, x_78, x_84, x_90);
lean_inc_ref(x_77);
lean_inc(x_34);
x_92 = l_Lean_Syntax_node2(x_34, x_75, x_77, x_91);
lean_inc(x_34);
x_93 = l_Lean_Syntax_node1(x_34, x_37, x_92);
lean_inc_ref(x_62);
lean_inc_ref(x_51);
lean_inc(x_34);
x_94 = l_Lean_Syntax_node5(x_34, x_49, x_51, x_68, x_74, x_93, x_62);
lean_inc(x_34);
x_95 = l_Lean_Syntax_node2(x_34, x_37, x_63, x_94);
lean_inc_ref(x_39);
lean_inc(x_34);
x_96 = l_Lean_Syntax_node2(x_34, x_48, x_95, x_39);
x_97 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__62));
x_98 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__65));
lean_inc_ref_n(x_39, 2);
lean_inc(x_34);
x_99 = l_Lean_Syntax_node2(x_34, x_98, x_39, x_39);
x_100 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__66));
x_101 = l_Lean_Name_str___override(x_2, x_100);
x_102 = l_Lean_Name_append(x_22, x_101);
x_103 = l_Lean_mkIdentFromRef___redArg(x_7, x_8, x_102, x_26);
x_104 = lean_apply_2(x_103, x_14, x_30);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; uint8_t x_178; 
x_105 = lean_ctor_get(x_104, 0);
x_106 = lean_ctor_get(x_104, 1);
x_178 = !lean_is_exclusive(x_104);
if (x_178 == 0)
{
x_107 = x_104;
x_108 = x_178;
goto block_177;
}
else
{
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_104);
x_107 = lean_box(0);
x_108 = x_178;
goto block_177;
}
block_177:
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_inc_ref(x_39);
lean_inc(x_99);
lean_inc_ref(x_77);
lean_inc(x_34);
x_109 = l_Lean_Syntax_node4(x_34, x_97, x_77, x_18, x_99, x_39);
x_110 = lean_unsigned_to_nat(2u);
x_111 = lean_mk_empty_array_with_capacity(x_110);
x_112 = lean_array_push(x_111, x_29);
x_113 = lean_array_push(x_112, x_47);
x_114 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_114, 0, x_46);
lean_ctor_set(x_114, 1, x_44);
lean_ctor_set(x_114, 2, x_113);
lean_inc_ref(x_39);
lean_inc(x_34);
x_115 = l_Lean_Syntax_node5(x_34, x_41, x_43, x_114, x_96, x_109, x_39);
lean_inc(x_40);
lean_inc(x_34);
x_116 = l_Lean_Syntax_node2(x_34, x_35, x_40, x_115);
x_117 = lean_array_push(x_1, x_116);
x_118 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__67));
x_119 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__68));
x_120 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__70));
lean_inc_ref(x_39);
lean_inc(x_34);
x_121 = l_Lean_Syntax_node1(x_34, x_120, x_39);
lean_inc(x_34);
x_122 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_122, 0, x_34);
lean_ctor_set(x_122, 1, x_118);
lean_inc_ref(x_39);
lean_inc(x_34);
x_123 = l_Lean_Syntax_node2(x_34, x_44, x_105, x_39);
lean_inc(x_34);
x_124 = l_Lean_Syntax_node1(x_34, x_37, x_123);
x_125 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__72));
x_126 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__74));
x_127 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__76));
x_128 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__78, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__78_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__78);
x_129 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__79));
lean_inc(x_32);
lean_inc(x_31);
x_130 = l_Lean_addMacroScope(x_31, x_129, x_32);
x_131 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__84));
lean_inc(x_34);
x_132 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_132, 0, x_34);
lean_ctor_set(x_132, 1, x_128);
lean_ctor_set(x_132, 2, x_130);
lean_ctor_set(x_132, 3, x_131);
lean_inc(x_34);
x_133 = l_Lean_Syntax_node1(x_34, x_37, x_21);
lean_inc(x_34);
x_134 = l_Lean_Syntax_node2(x_34, x_127, x_132, x_133);
lean_inc(x_34);
x_135 = l_Lean_Syntax_node2(x_34, x_126, x_59, x_134);
lean_inc_ref(x_39);
lean_inc(x_34);
x_136 = l_Lean_Syntax_node2(x_34, x_125, x_39, x_135);
x_137 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__86));
x_138 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__87));
lean_inc(x_34);
x_139 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_139, 0, x_34);
lean_ctor_set(x_139, 1, x_138);
x_140 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__89));
x_141 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__91));
x_142 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__93));
x_143 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__94, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__94_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__94);
x_144 = lean_box(0);
lean_inc(x_32);
lean_inc(x_31);
x_145 = l_Lean_addMacroScope(x_31, x_144, x_32);
x_146 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__107));
lean_inc(x_34);
x_147 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_147, 0, x_34);
lean_ctor_set(x_147, 1, x_143);
lean_ctor_set(x_147, 2, x_145);
lean_ctor_set(x_147, 3, x_146);
lean_inc(x_34);
x_148 = l_Lean_Syntax_node1(x_34, x_142, x_147);
lean_inc(x_148);
lean_inc(x_34);
x_149 = l_Lean_Syntax_node2(x_34, x_141, x_51, x_148);
x_150 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__108, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__108_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__108);
x_151 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__109));
x_152 = l_Lean_addMacroScope(x_31, x_151, x_32);
x_153 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__112));
lean_inc(x_34);
x_154 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_154, 0, x_34);
lean_ctor_set(x_154, 1, x_150);
lean_ctor_set(x_154, 2, x_152);
lean_ctor_set(x_154, 3, x_153);
x_155 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__114));
x_156 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__116));
x_157 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__117));
lean_inc(x_34);
x_158 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_158, 0, x_34);
lean_ctor_set(x_158, 1, x_157);
lean_inc(x_34);
x_159 = l_Lean_Syntax_node2(x_34, x_156, x_158, x_148);
x_160 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__118));
lean_inc(x_34);
x_161 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_161, 0, x_34);
lean_ctor_set(x_161, 1, x_160);
lean_inc_ref(x_154);
lean_inc(x_34);
x_162 = l_Lean_Syntax_node3(x_34, x_155, x_159, x_161, x_154);
lean_inc(x_34);
x_163 = l_Lean_Syntax_node1(x_34, x_37, x_162);
lean_inc(x_34);
x_164 = l_Lean_Syntax_node2(x_34, x_127, x_154, x_163);
lean_inc(x_34);
x_165 = l_Lean_Syntax_node3(x_34, x_140, x_149, x_164, x_62);
lean_inc(x_34);
x_166 = l_Lean_Syntax_node1(x_34, x_37, x_165);
x_167 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__119));
lean_inc(x_34);
x_168 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_168, 0, x_34);
lean_ctor_set(x_168, 1, x_167);
lean_inc(x_34);
x_169 = l_Lean_Syntax_node3(x_34, x_137, x_139, x_166, x_168);
lean_inc_ref(x_39);
lean_inc(x_34);
x_170 = l_Lean_Syntax_node4(x_34, x_97, x_77, x_169, x_99, x_39);
lean_inc(x_34);
x_171 = l_Lean_Syntax_node6(x_34, x_119, x_121, x_122, x_39, x_124, x_136, x_170);
x_172 = l_Lean_Syntax_node2(x_34, x_35, x_40, x_171);
x_173 = lean_array_push(x_117, x_172);
if (x_108 == 0)
{
lean_ctor_set(x_107, 0, x_173);
x_174 = x_107;
goto block_175;
}
else
{
lean_object* x_176; 
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_173);
lean_ctor_set(x_176, 1, x_106);
x_174 = x_176;
goto block_175;
}
block_175:
{
return x_174;
}
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; uint8_t x_187; 
lean_dec(x_99);
lean_dec(x_96);
lean_dec_ref(x_77);
lean_dec_ref(x_62);
lean_dec_ref(x_59);
lean_dec_ref(x_51);
lean_dec_ref(x_47);
lean_dec_ref(x_43);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_21);
lean_dec(x_18);
lean_dec_ref(x_1);
x_179 = lean_ctor_get(x_104, 0);
x_180 = lean_ctor_get(x_104, 1);
x_187 = !lean_is_exclusive(x_104);
if (x_187 == 0)
{
x_181 = x_104;
x_182 = x_187;
goto block_186;
}
else
{
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_104);
x_181 = lean_box(0);
x_182 = x_187;
goto block_186;
}
block_186:
{
lean_object* x_183; 
if (x_182 == 0)
{
x_183 = x_181;
goto block_184;
}
else
{
lean_object* x_185; 
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_179);
lean_ctor_set(x_185, 1, x_180);
x_183 = x_185;
goto block_184;
}
block_184:
{
return x_183;
}
}
}
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; uint8_t x_198; 
lean_dec(x_21);
lean_dec(x_18);
lean_dec_ref(x_14);
lean_del_object(x_11);
lean_dec(x_2);
lean_dec_ref(x_1);
x_190 = lean_ctor_get(x_28, 0);
x_191 = lean_ctor_get(x_28, 1);
x_198 = !lean_is_exclusive(x_28);
if (x_198 == 0)
{
x_192 = x_28;
x_193 = x_198;
goto block_197;
}
else
{
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_28);
x_192 = lean_box(0);
x_193 = x_198;
goto block_197;
}
block_197:
{
lean_object* x_194; 
if (x_193 == 0)
{
x_194 = x_192;
goto block_195;
}
else
{
lean_object* x_196; 
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_190);
lean_ctor_set(x_196, 1, x_191);
x_194 = x_196;
goto block_195;
}
block_195:
{
return x_194;
}
}
}
}
block_216:
{
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
lean_dec_ref(x_204);
x_14 = x_201;
x_15 = x_200;
x_16 = x_202;
x_17 = x_203;
x_18 = x_205;
x_19 = x_206;
goto block_199;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; uint8_t x_215; 
lean_dec_ref(x_202);
lean_dec_ref(x_201);
lean_dec(x_200);
lean_del_object(x_11);
lean_dec(x_2);
lean_dec_ref(x_1);
x_207 = lean_ctor_get(x_204, 0);
x_208 = lean_ctor_get(x_204, 1);
x_215 = !lean_is_exclusive(x_204);
if (x_215 == 0)
{
x_209 = x_204;
x_210 = x_215;
goto block_214;
}
else
{
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_204);
x_209 = lean_box(0);
x_210 = x_215;
goto block_214;
}
block_214:
{
lean_object* x_211; 
if (x_210 == 0)
{
x_211 = x_209;
goto block_212;
}
else
{
lean_object* x_213; 
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_207);
lean_ctor_set(x_213, 1, x_208);
x_211 = x_213;
goto block_212;
}
block_212:
{
return x_211;
}
}
}
}
block_235:
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; 
x_222 = lean_mk_empty_array_with_capacity(x_10);
x_223 = lean_unsigned_to_nat(0u);
x_224 = lean_array_get_size(x_9);
x_225 = lean_nat_dec_lt(x_223, x_224);
if (x_225 == 0)
{
lean_dec_ref(x_218);
lean_dec_ref(x_9);
x_14 = x_220;
x_15 = x_10;
x_16 = x_222;
x_17 = x_223;
x_18 = x_219;
x_19 = x_221;
goto block_199;
}
else
{
uint8_t x_226; 
x_226 = lean_nat_dec_le(x_224, x_224);
if (x_226 == 0)
{
if (x_225 == 0)
{
lean_dec_ref(x_218);
lean_dec_ref(x_9);
x_14 = x_220;
x_15 = x_10;
x_16 = x_222;
x_17 = x_223;
x_18 = x_219;
x_19 = x_221;
goto block_199;
}
else
{
size_t x_227; size_t x_228; lean_object* x_229; lean_object* x_230; 
x_227 = 0;
x_228 = lean_usize_of_nat(x_224);
x_229 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_7, x_218, x_9, x_227, x_228, x_219);
lean_inc_ref(x_220);
x_230 = lean_apply_2(x_229, x_220, x_221);
x_200 = x_10;
x_201 = x_220;
x_202 = x_222;
x_203 = x_223;
x_204 = x_230;
goto block_216;
}
}
else
{
size_t x_231; size_t x_232; lean_object* x_233; lean_object* x_234; 
x_231 = 0;
x_232 = lean_usize_of_nat(x_224);
x_233 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_7, x_218, x_9, x_231, x_232, x_219);
lean_inc_ref(x_220);
x_234 = lean_apply_2(x_233, x_220, x_221);
x_200 = x_10;
x_201 = x_220;
x_202 = x_222;
x_203 = x_223;
x_204 = x_234;
goto block_216;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget_borrowed(x_2, x_3);
x_7 = lean_name_eq(x_1, x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
else
{
return x_7;
}
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__0_spec__1(x_1, x_2, x_5, x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
return x_5;
}
else
{
if (x_5 == 0)
{
return x_5;
}
else
{
size_t x_6; size_t x_7; uint8_t x_8; 
x_6 = 0;
x_7 = lean_usize_of_nat(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__0_spec__1(x_2, x_1, x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_contains___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_14; 
x_14 = lean_usize_dec_eq(x_3, x_4);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_array_uget_borrowed(x_2, x_3);
x_16 = lean_ctor_get_uint8(x_15, sizeof(void*)*2);
if (x_16 == 0)
{
x_8 = x_5;
x_9 = x_7;
goto block_13;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = l_Array_contains___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__0(x_1, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_ctor_get(x_6, 2);
x_21 = lean_ctor_get(x_6, 5);
x_22 = l_Lean_SourceInfo_fromRef(x_21, x_18);
x_23 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__4));
x_24 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__5));
lean_inc(x_22);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__7, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__7_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__7);
x_27 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__8));
lean_inc(x_20);
lean_inc(x_19);
x_28 = l_Lean_addMacroScope(x_19, x_27, x_20);
x_29 = lean_box(0);
lean_inc(x_22);
x_30 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_30, 0, x_22);
lean_ctor_set(x_30, 1, x_26);
lean_ctor_set(x_30, 2, x_28);
lean_ctor_set(x_30, 3, x_29);
x_31 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__10));
x_32 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__12, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__12_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__12);
x_33 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__13));
lean_inc(x_20);
lean_inc(x_19);
x_34 = l_Lean_addMacroScope(x_19, x_33, x_20);
lean_inc(x_22);
x_35 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_35, 0, x_22);
lean_ctor_set(x_35, 1, x_32);
lean_ctor_set(x_35, 2, x_34);
lean_ctor_set(x_35, 3, x_29);
lean_inc(x_17);
x_36 = l_Lean_instQuoteNameMkStr1___private__1(x_17);
lean_inc(x_22);
x_37 = l_Lean_Syntax_node2(x_22, x_31, x_35, x_36);
x_38 = l_Lean_Syntax_node4(x_22, x_23, x_5, x_25, x_30, x_37);
x_8 = x_38;
x_9 = x_7;
goto block_13;
}
else
{
x_8 = x_5;
x_9 = x_7;
goto block_13;
}
}
}
else
{
lean_object* x_39; 
lean_dec_ref(x_6);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_5);
lean_ctor_set(x_39, 1, x_7);
return x_39;
}
block_13:
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_3 = x_11;
x_5 = x_8;
x_7 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__3(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 5);
x_6 = l_Lean_mkIdentFrom(x_5, x_1, x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_mkIdentFromRef___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__2(x_1, x_5, x_3, x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 1)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
x_8 = lean_nat_sub(x_1, x_2);
lean_dec(x_2);
x_9 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__0___closed__0));
x_10 = lean_nat_add(x_8, x_6);
lean_dec(x_8);
x_11 = l_Nat_reprFast(x_10);
x_12 = lean_string_append(x_9, x_11);
lean_dec_ref(x_11);
x_13 = lean_box(0);
x_14 = l_Lean_Name_str___override(x_13, x_12);
x_15 = lean_mk_syntax_ident(x_14);
x_16 = lean_array_push(x_3, x_15);
x_2 = x_7;
x_3 = x_16;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__1___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_211; lean_object* x_212; uint8_t x_213; 
x_193 = l_Lake_LeanConfig_instConfigInfo;
x_211 = lean_ctor_get(x_193, 2);
lean_inc(x_211);
x_212 = lean_unsigned_to_nat(0u);
x_213 = lean_nat_dec_eq(x_211, x_212);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_214 = lean_ctor_get(x_4, 1);
x_215 = lean_ctor_get(x_4, 2);
x_216 = lean_ctor_get(x_4, 5);
x_217 = l_Lean_SourceInfo_fromRef(x_216, x_213);
x_218 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__76));
x_219 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__122, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__122_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__122);
x_220 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__124));
lean_inc(x_215);
lean_inc(x_214);
x_221 = l_Lean_addMacroScope(x_214, x_220, x_215);
x_222 = lean_box(0);
lean_inc(x_217);
x_223 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_223, 0, x_217);
lean_ctor_set(x_223, 1, x_219);
lean_ctor_set(x_223, 2, x_221);
lean_ctor_set(x_223, 3, x_222);
x_224 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__10));
x_225 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__126));
x_226 = ((lean_object*)(l_Lake_Dependency_toToml___closed__12));
x_227 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__127));
lean_inc(x_217);
x_228 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_228, 0, x_217);
lean_ctor_set(x_228, 1, x_227);
lean_inc(x_217);
x_229 = l_Lean_Syntax_node1(x_217, x_226, x_228);
lean_inc(x_217);
x_230 = l_Lean_Syntax_node1(x_217, x_225, x_229);
x_231 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__0___closed__0));
x_232 = l_Nat_reprFast(x_211);
x_233 = lean_string_append(x_231, x_232);
lean_dec_ref(x_232);
x_234 = lean_box(0);
x_235 = l_Lean_Name_str___override(x_234, x_233);
x_236 = lean_mk_syntax_ident(x_235);
lean_inc(x_217);
x_237 = l_Lean_Syntax_node2(x_217, x_224, x_230, x_236);
x_238 = l_Lean_Syntax_node2(x_217, x_218, x_223, x_237);
x_194 = x_238;
x_195 = x_4;
x_196 = x_5;
goto block_210;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; uint8_t x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_211);
x_239 = lean_ctor_get(x_4, 1);
x_240 = lean_ctor_get(x_4, 2);
x_241 = lean_ctor_get(x_4, 5);
x_242 = 0;
x_243 = l_Lean_SourceInfo_fromRef(x_241, x_242);
x_244 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__34, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__34_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__34);
x_245 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__35));
lean_inc(x_240);
lean_inc(x_239);
x_246 = l_Lean_addMacroScope(x_239, x_245, x_240);
x_247 = lean_box(0);
x_248 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_248, 0, x_243);
lean_ctor_set(x_248, 1, x_244);
lean_ctor_set(x_248, 2, x_246);
lean_ctor_set(x_248, 3, x_247);
x_194 = x_248;
x_195 = x_4;
x_196 = x_5;
goto block_210;
}
block_175:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_174; 
lean_inc(x_6);
x_12 = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__1___redArg(x_6, x_6, x_7);
lean_dec(x_6);
lean_inc(x_2);
x_13 = l_Lean_Syntax_mkCApp(x_2, x_12);
x_14 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__13));
x_15 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__14));
lean_inc(x_2);
x_16 = l_Lean_Name_str___override(x_2, x_15);
x_17 = l_Lean_Name_append(x_14, x_16);
x_18 = 0;
x_19 = l_Lean_mkIdentFromRef___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__2(x_17, x_18, x_9, x_11);
x_20 = lean_ctor_get(x_19, 0);
x_21 = lean_ctor_get(x_19, 1);
x_174 = !lean_is_exclusive(x_19);
if (x_174 == 0)
{
x_22 = x_19;
x_23 = x_174;
goto block_173;
}
else
{
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_19);
x_22 = lean_box(0);
x_23 = x_174;
goto block_173;
}
block_173:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_24 = lean_ctor_get(x_9, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_9, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_9, 5);
x_27 = l_Lean_SourceInfo_fromRef(x_26, x_18);
x_28 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__17));
x_29 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__19));
x_30 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__10));
x_31 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__20, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__20_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__20);
lean_inc(x_27);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_32, 2, x_31);
lean_inc_ref_n(x_32, 7);
lean_inc(x_27);
x_33 = l_Lean_Syntax_node7(x_27, x_29, x_32, x_32, x_32, x_32, x_32, x_32, x_32);
x_34 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__22));
x_35 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__23));
lean_inc(x_27);
if (x_23 == 0)
{
lean_ctor_set_tag(x_22, 2);
lean_ctor_set(x_22, 1, x_35);
lean_ctor_set(x_22, 0, x_27);
x_36 = x_22;
goto block_171;
}
else
{
lean_object* x_172; 
x_172 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_172, 0, x_27);
lean_ctor_set(x_172, 1, x_35);
x_36 = x_172;
goto block_171;
}
block_171:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; uint8_t x_170; 
x_37 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__25));
x_38 = lean_mk_empty_array_with_capacity(x_8);
x_39 = lean_box(2);
x_40 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_30);
lean_ctor_set(x_40, 2, x_38);
x_41 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__27));
x_42 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__29));
x_43 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__30));
lean_inc(x_27);
x_44 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_44, 0, x_27);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__12, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__12_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__12);
x_46 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__13));
lean_inc(x_25);
lean_inc(x_24);
x_47 = l_Lean_addMacroScope(x_24, x_46, x_25);
x_48 = lean_box(0);
lean_inc(x_27);
x_49 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_49, 0, x_27);
lean_ctor_set(x_49, 1, x_45);
lean_ctor_set(x_49, 2, x_47);
lean_ctor_set(x_49, 3, x_48);
lean_inc(x_27);
x_50 = l_Lean_Syntax_node1(x_27, x_30, x_49);
x_51 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__31));
lean_inc(x_27);
x_52 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_52, 0, x_27);
lean_ctor_set(x_52, 1, x_51);
lean_inc(x_13);
lean_inc_ref(x_52);
lean_inc(x_27);
x_53 = l_Lean_Syntax_node2(x_27, x_30, x_52, x_13);
x_54 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__32));
lean_inc(x_27);
x_55 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_55, 0, x_27);
lean_ctor_set(x_55, 1, x_54);
lean_inc_ref(x_55);
lean_inc_ref(x_32);
lean_inc_ref(x_44);
lean_inc(x_27);
x_56 = l_Lean_Syntax_node5(x_27, x_42, x_44, x_50, x_53, x_32, x_55);
x_57 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__34, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__34_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__34);
x_58 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__35));
lean_inc(x_25);
lean_inc(x_24);
x_59 = l_Lean_addMacroScope(x_24, x_58, x_25);
lean_inc(x_27);
x_60 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_60, 0, x_27);
lean_ctor_set(x_60, 1, x_57);
lean_ctor_set(x_60, 2, x_59);
lean_ctor_set(x_60, 3, x_48);
lean_inc(x_27);
x_61 = l_Lean_Syntax_node1(x_27, x_30, x_60);
x_62 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__37, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__37_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__37);
x_63 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__38));
lean_inc(x_25);
lean_inc(x_24);
x_64 = l_Lean_addMacroScope(x_24, x_63, x_25);
x_65 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__45));
lean_inc(x_27);
x_66 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_66, 0, x_27);
lean_ctor_set(x_66, 1, x_62);
lean_ctor_set(x_66, 2, x_64);
lean_ctor_set(x_66, 3, x_65);
lean_inc_ref(x_52);
lean_inc(x_27);
x_67 = l_Lean_Syntax_node2(x_27, x_30, x_52, x_66);
x_68 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__47));
x_69 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__48));
lean_inc(x_27);
x_70 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_70, 0, x_27);
lean_ctor_set(x_70, 1, x_69);
x_71 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__50));
x_72 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__52));
x_73 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__53));
lean_inc(x_27);
x_74 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_74, 0, x_27);
lean_ctor_set(x_74, 1, x_73);
x_75 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__54));
lean_inc(x_27);
x_76 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_76, 0, x_27);
lean_ctor_set(x_76, 1, x_75);
lean_inc_ref(x_76);
lean_inc_ref(x_74);
lean_inc(x_27);
x_77 = l_Lean_Syntax_node2(x_27, x_72, x_74, x_76);
x_78 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__56));
x_79 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__58));
lean_inc_ref(x_32);
lean_inc(x_27);
x_80 = l_Lean_Syntax_node1(x_27, x_79, x_32);
x_81 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__60));
lean_inc_ref(x_32);
lean_inc(x_27);
x_82 = l_Lean_Syntax_node1(x_27, x_81, x_32);
lean_inc_ref_n(x_32, 2);
lean_inc(x_27);
x_83 = l_Lean_Syntax_node6(x_27, x_78, x_74, x_32, x_80, x_82, x_32, x_76);
lean_inc(x_27);
x_84 = l_Lean_Syntax_node2(x_27, x_71, x_77, x_83);
lean_inc_ref(x_70);
lean_inc(x_27);
x_85 = l_Lean_Syntax_node2(x_27, x_68, x_70, x_84);
lean_inc(x_27);
x_86 = l_Lean_Syntax_node1(x_27, x_30, x_85);
lean_inc_ref(x_55);
lean_inc_ref(x_44);
lean_inc(x_27);
x_87 = l_Lean_Syntax_node5(x_27, x_42, x_44, x_61, x_67, x_86, x_55);
lean_inc(x_27);
x_88 = l_Lean_Syntax_node2(x_27, x_30, x_56, x_87);
lean_inc_ref(x_32);
lean_inc(x_27);
x_89 = l_Lean_Syntax_node2(x_27, x_41, x_88, x_32);
x_90 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__62));
x_91 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__65));
lean_inc_ref_n(x_32, 2);
lean_inc(x_27);
x_92 = l_Lean_Syntax_node2(x_27, x_91, x_32, x_32);
x_93 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__66));
x_94 = l_Lean_Name_str___override(x_2, x_93);
x_95 = l_Lean_Name_append(x_14, x_94);
x_96 = l_Lean_mkIdentFromRef___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__2(x_95, x_18, x_9, x_21);
lean_dec_ref(x_9);
x_97 = lean_ctor_get(x_96, 0);
x_98 = lean_ctor_get(x_96, 1);
x_170 = !lean_is_exclusive(x_96);
if (x_170 == 0)
{
x_99 = x_96;
x_100 = x_170;
goto block_169;
}
else
{
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_96);
x_99 = lean_box(0);
x_100 = x_170;
goto block_169;
}
block_169:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_inc_ref(x_32);
lean_inc(x_92);
lean_inc_ref(x_70);
lean_inc(x_27);
x_101 = l_Lean_Syntax_node4(x_27, x_90, x_70, x_10, x_92, x_32);
x_102 = lean_unsigned_to_nat(2u);
x_103 = lean_mk_empty_array_with_capacity(x_102);
x_104 = lean_array_push(x_103, x_20);
x_105 = lean_array_push(x_104, x_40);
x_106 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_106, 0, x_39);
lean_ctor_set(x_106, 1, x_37);
lean_ctor_set(x_106, 2, x_105);
lean_inc_ref(x_32);
lean_inc(x_27);
x_107 = l_Lean_Syntax_node5(x_27, x_34, x_36, x_106, x_89, x_101, x_32);
lean_inc(x_33);
lean_inc(x_27);
x_108 = l_Lean_Syntax_node2(x_27, x_28, x_33, x_107);
x_109 = lean_array_push(x_1, x_108);
x_110 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__67));
x_111 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__68));
x_112 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__70));
lean_inc_ref(x_32);
lean_inc(x_27);
x_113 = l_Lean_Syntax_node1(x_27, x_112, x_32);
lean_inc(x_27);
x_114 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_114, 0, x_27);
lean_ctor_set(x_114, 1, x_110);
lean_inc_ref(x_32);
lean_inc(x_27);
x_115 = l_Lean_Syntax_node2(x_27, x_37, x_97, x_32);
lean_inc(x_27);
x_116 = l_Lean_Syntax_node1(x_27, x_30, x_115);
x_117 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__72));
x_118 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__74));
x_119 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__76));
x_120 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__78, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__78_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__78);
x_121 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__79));
lean_inc(x_25);
lean_inc(x_24);
x_122 = l_Lean_addMacroScope(x_24, x_121, x_25);
x_123 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__84));
lean_inc(x_27);
x_124 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_124, 0, x_27);
lean_ctor_set(x_124, 1, x_120);
lean_ctor_set(x_124, 2, x_122);
lean_ctor_set(x_124, 3, x_123);
lean_inc(x_27);
x_125 = l_Lean_Syntax_node1(x_27, x_30, x_13);
lean_inc(x_27);
x_126 = l_Lean_Syntax_node2(x_27, x_119, x_124, x_125);
lean_inc(x_27);
x_127 = l_Lean_Syntax_node2(x_27, x_118, x_52, x_126);
lean_inc_ref(x_32);
lean_inc(x_27);
x_128 = l_Lean_Syntax_node2(x_27, x_117, x_32, x_127);
x_129 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__86));
x_130 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__87));
lean_inc(x_27);
x_131 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_131, 0, x_27);
lean_ctor_set(x_131, 1, x_130);
x_132 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__89));
x_133 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__91));
x_134 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__93));
x_135 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__94, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__94_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__94);
x_136 = lean_box(0);
lean_inc(x_25);
lean_inc(x_24);
x_137 = l_Lean_addMacroScope(x_24, x_136, x_25);
x_138 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__107));
lean_inc(x_27);
x_139 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_139, 0, x_27);
lean_ctor_set(x_139, 1, x_135);
lean_ctor_set(x_139, 2, x_137);
lean_ctor_set(x_139, 3, x_138);
lean_inc(x_27);
x_140 = l_Lean_Syntax_node1(x_27, x_134, x_139);
lean_inc(x_140);
lean_inc(x_27);
x_141 = l_Lean_Syntax_node2(x_27, x_133, x_44, x_140);
x_142 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__108, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__108_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__108);
x_143 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__109));
x_144 = l_Lean_addMacroScope(x_24, x_143, x_25);
x_145 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__112));
lean_inc(x_27);
x_146 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_146, 0, x_27);
lean_ctor_set(x_146, 1, x_142);
lean_ctor_set(x_146, 2, x_144);
lean_ctor_set(x_146, 3, x_145);
x_147 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__114));
x_148 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__116));
x_149 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__117));
lean_inc(x_27);
x_150 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_150, 0, x_27);
lean_ctor_set(x_150, 1, x_149);
lean_inc(x_27);
x_151 = l_Lean_Syntax_node2(x_27, x_148, x_150, x_140);
x_152 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__118));
lean_inc(x_27);
x_153 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_153, 0, x_27);
lean_ctor_set(x_153, 1, x_152);
lean_inc_ref(x_146);
lean_inc(x_27);
x_154 = l_Lean_Syntax_node3(x_27, x_147, x_151, x_153, x_146);
lean_inc(x_27);
x_155 = l_Lean_Syntax_node1(x_27, x_30, x_154);
lean_inc(x_27);
x_156 = l_Lean_Syntax_node2(x_27, x_119, x_146, x_155);
lean_inc(x_27);
x_157 = l_Lean_Syntax_node3(x_27, x_132, x_141, x_156, x_55);
lean_inc(x_27);
x_158 = l_Lean_Syntax_node1(x_27, x_30, x_157);
x_159 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__119));
lean_inc(x_27);
x_160 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_160, 0, x_27);
lean_ctor_set(x_160, 1, x_159);
lean_inc(x_27);
x_161 = l_Lean_Syntax_node3(x_27, x_129, x_131, x_158, x_160);
lean_inc_ref(x_32);
lean_inc(x_27);
x_162 = l_Lean_Syntax_node4(x_27, x_90, x_70, x_161, x_92, x_32);
lean_inc(x_27);
x_163 = l_Lean_Syntax_node6(x_27, x_111, x_113, x_114, x_32, x_116, x_128, x_162);
x_164 = l_Lean_Syntax_node2(x_27, x_28, x_33, x_163);
x_165 = lean_array_push(x_109, x_164);
if (x_100 == 0)
{
lean_ctor_set(x_99, 0, x_165);
x_166 = x_99;
goto block_167;
}
else
{
lean_object* x_168; 
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_165);
lean_ctor_set(x_168, 1, x_98);
x_166 = x_168;
goto block_167;
}
block_167:
{
return x_166;
}
}
}
}
}
block_192:
{
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
lean_dec_ref(x_180);
x_6 = x_176;
x_7 = x_177;
x_8 = x_179;
x_9 = x_178;
x_10 = x_181;
x_11 = x_182;
goto block_175;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; uint8_t x_191; 
lean_dec_ref(x_178);
lean_dec_ref(x_177);
lean_dec(x_176);
lean_dec(x_2);
lean_dec_ref(x_1);
x_183 = lean_ctor_get(x_180, 0);
x_184 = lean_ctor_get(x_180, 1);
x_191 = !lean_is_exclusive(x_180);
if (x_191 == 0)
{
x_185 = x_180;
x_186 = x_191;
goto block_190;
}
else
{
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_180);
x_185 = lean_box(0);
x_186 = x_191;
goto block_190;
}
block_190:
{
lean_object* x_187; 
if (x_186 == 0)
{
x_187 = x_185;
goto block_188;
}
else
{
lean_object* x_189; 
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_183);
lean_ctor_set(x_189, 1, x_184);
x_187 = x_189;
goto block_188;
}
block_188:
{
return x_187;
}
}
}
}
block_210:
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; 
x_197 = lean_ctor_get(x_193, 0);
lean_inc_ref(x_197);
x_198 = lean_ctor_get(x_193, 2);
lean_inc(x_198);
x_199 = lean_mk_empty_array_with_capacity(x_198);
x_200 = lean_unsigned_to_nat(0u);
x_201 = lean_array_get_size(x_197);
x_202 = lean_nat_dec_lt(x_200, x_201);
if (x_202 == 0)
{
lean_dec_ref(x_197);
x_6 = x_198;
x_7 = x_199;
x_8 = x_200;
x_9 = x_195;
x_10 = x_194;
x_11 = x_196;
goto block_175;
}
else
{
uint8_t x_203; 
x_203 = lean_nat_dec_le(x_201, x_201);
if (x_203 == 0)
{
if (x_202 == 0)
{
lean_dec_ref(x_197);
x_6 = x_198;
x_7 = x_199;
x_8 = x_200;
x_9 = x_195;
x_10 = x_194;
x_11 = x_196;
goto block_175;
}
else
{
size_t x_204; size_t x_205; lean_object* x_206; 
x_204 = 0;
x_205 = lean_usize_of_nat(x_201);
lean_inc_ref(x_195);
x_206 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__3(x_3, x_197, x_204, x_205, x_194, x_195, x_196);
lean_dec_ref(x_197);
x_176 = x_198;
x_177 = x_199;
x_178 = x_195;
x_179 = x_200;
x_180 = x_206;
goto block_192;
}
}
else
{
size_t x_207; size_t x_208; lean_object* x_209; 
x_207 = 0;
x_208 = lean_usize_of_nat(x_201);
lean_inc_ref(x_195);
x_209 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__3(x_3, x_197, x_207, x_208, x_194, x_195, x_196);
lean_dec_ref(x_197);
x_176 = x_198;
x_177 = x_199;
x_178 = x_195;
x_179 = x_200;
x_180 = x_209;
goto block_192;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_211; lean_object* x_212; uint8_t x_213; 
x_193 = l_Lake_LeanExeConfig_instConfigInfo;
x_211 = lean_ctor_get(x_193, 2);
lean_inc(x_211);
x_212 = lean_unsigned_to_nat(0u);
x_213 = lean_nat_dec_eq(x_211, x_212);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_214 = lean_ctor_get(x_4, 1);
x_215 = lean_ctor_get(x_4, 2);
x_216 = lean_ctor_get(x_4, 5);
x_217 = l_Lean_SourceInfo_fromRef(x_216, x_213);
x_218 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__76));
x_219 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__122, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__122_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__122);
x_220 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__124));
lean_inc(x_215);
lean_inc(x_214);
x_221 = l_Lean_addMacroScope(x_214, x_220, x_215);
x_222 = lean_box(0);
lean_inc(x_217);
x_223 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_223, 0, x_217);
lean_ctor_set(x_223, 1, x_219);
lean_ctor_set(x_223, 2, x_221);
lean_ctor_set(x_223, 3, x_222);
x_224 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__10));
x_225 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__126));
x_226 = ((lean_object*)(l_Lake_Dependency_toToml___closed__12));
x_227 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__127));
lean_inc(x_217);
x_228 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_228, 0, x_217);
lean_ctor_set(x_228, 1, x_227);
lean_inc(x_217);
x_229 = l_Lean_Syntax_node1(x_217, x_226, x_228);
lean_inc(x_217);
x_230 = l_Lean_Syntax_node1(x_217, x_225, x_229);
x_231 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__0___closed__0));
x_232 = l_Nat_reprFast(x_211);
x_233 = lean_string_append(x_231, x_232);
lean_dec_ref(x_232);
x_234 = lean_box(0);
x_235 = l_Lean_Name_str___override(x_234, x_233);
x_236 = lean_mk_syntax_ident(x_235);
lean_inc(x_217);
x_237 = l_Lean_Syntax_node2(x_217, x_224, x_230, x_236);
x_238 = l_Lean_Syntax_node2(x_217, x_218, x_223, x_237);
x_194 = x_238;
x_195 = x_4;
x_196 = x_5;
goto block_210;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; uint8_t x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_211);
x_239 = lean_ctor_get(x_4, 1);
x_240 = lean_ctor_get(x_4, 2);
x_241 = lean_ctor_get(x_4, 5);
x_242 = 0;
x_243 = l_Lean_SourceInfo_fromRef(x_241, x_242);
x_244 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__34, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__34_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__34);
x_245 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__35));
lean_inc(x_240);
lean_inc(x_239);
x_246 = l_Lean_addMacroScope(x_239, x_245, x_240);
x_247 = lean_box(0);
x_248 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_248, 0, x_243);
lean_ctor_set(x_248, 1, x_244);
lean_ctor_set(x_248, 2, x_246);
lean_ctor_set(x_248, 3, x_247);
x_194 = x_248;
x_195 = x_4;
x_196 = x_5;
goto block_210;
}
block_175:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_174; 
lean_inc(x_6);
x_12 = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__1___redArg(x_6, x_6, x_8);
lean_dec(x_6);
lean_inc(x_2);
x_13 = l_Lean_Syntax_mkCApp(x_2, x_12);
x_14 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__13));
x_15 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__14));
lean_inc(x_2);
x_16 = l_Lean_Name_str___override(x_2, x_15);
x_17 = l_Lean_Name_append(x_14, x_16);
x_18 = 0;
x_19 = l_Lean_mkIdentFromRef___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__2(x_17, x_18, x_7, x_11);
x_20 = lean_ctor_get(x_19, 0);
x_21 = lean_ctor_get(x_19, 1);
x_174 = !lean_is_exclusive(x_19);
if (x_174 == 0)
{
x_22 = x_19;
x_23 = x_174;
goto block_173;
}
else
{
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_19);
x_22 = lean_box(0);
x_23 = x_174;
goto block_173;
}
block_173:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_24 = lean_ctor_get(x_7, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_7, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_7, 5);
x_27 = l_Lean_SourceInfo_fromRef(x_26, x_18);
x_28 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__17));
x_29 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__19));
x_30 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__10));
x_31 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__20, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__20_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__20);
lean_inc(x_27);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_32, 2, x_31);
lean_inc_ref_n(x_32, 7);
lean_inc(x_27);
x_33 = l_Lean_Syntax_node7(x_27, x_29, x_32, x_32, x_32, x_32, x_32, x_32, x_32);
x_34 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__22));
x_35 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__23));
lean_inc(x_27);
if (x_23 == 0)
{
lean_ctor_set_tag(x_22, 2);
lean_ctor_set(x_22, 1, x_35);
lean_ctor_set(x_22, 0, x_27);
x_36 = x_22;
goto block_171;
}
else
{
lean_object* x_172; 
x_172 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_172, 0, x_27);
lean_ctor_set(x_172, 1, x_35);
x_36 = x_172;
goto block_171;
}
block_171:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; uint8_t x_170; 
x_37 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__25));
x_38 = lean_mk_empty_array_with_capacity(x_9);
x_39 = lean_box(2);
x_40 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_30);
lean_ctor_set(x_40, 2, x_38);
x_41 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__27));
x_42 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__29));
x_43 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__30));
lean_inc(x_27);
x_44 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_44, 0, x_27);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__12, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__12_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__12);
x_46 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__13));
lean_inc(x_25);
lean_inc(x_24);
x_47 = l_Lean_addMacroScope(x_24, x_46, x_25);
x_48 = lean_box(0);
lean_inc(x_27);
x_49 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_49, 0, x_27);
lean_ctor_set(x_49, 1, x_45);
lean_ctor_set(x_49, 2, x_47);
lean_ctor_set(x_49, 3, x_48);
lean_inc(x_27);
x_50 = l_Lean_Syntax_node1(x_27, x_30, x_49);
x_51 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__31));
lean_inc(x_27);
x_52 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_52, 0, x_27);
lean_ctor_set(x_52, 1, x_51);
lean_inc(x_13);
lean_inc_ref(x_52);
lean_inc(x_27);
x_53 = l_Lean_Syntax_node2(x_27, x_30, x_52, x_13);
x_54 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__32));
lean_inc(x_27);
x_55 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_55, 0, x_27);
lean_ctor_set(x_55, 1, x_54);
lean_inc_ref(x_55);
lean_inc_ref(x_32);
lean_inc_ref(x_44);
lean_inc(x_27);
x_56 = l_Lean_Syntax_node5(x_27, x_42, x_44, x_50, x_53, x_32, x_55);
x_57 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__34, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__34_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__34);
x_58 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__35));
lean_inc(x_25);
lean_inc(x_24);
x_59 = l_Lean_addMacroScope(x_24, x_58, x_25);
lean_inc(x_27);
x_60 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_60, 0, x_27);
lean_ctor_set(x_60, 1, x_57);
lean_ctor_set(x_60, 2, x_59);
lean_ctor_set(x_60, 3, x_48);
lean_inc(x_27);
x_61 = l_Lean_Syntax_node1(x_27, x_30, x_60);
x_62 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__37, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__37_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__37);
x_63 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__38));
lean_inc(x_25);
lean_inc(x_24);
x_64 = l_Lean_addMacroScope(x_24, x_63, x_25);
x_65 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__45));
lean_inc(x_27);
x_66 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_66, 0, x_27);
lean_ctor_set(x_66, 1, x_62);
lean_ctor_set(x_66, 2, x_64);
lean_ctor_set(x_66, 3, x_65);
lean_inc_ref(x_52);
lean_inc(x_27);
x_67 = l_Lean_Syntax_node2(x_27, x_30, x_52, x_66);
x_68 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__47));
x_69 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__48));
lean_inc(x_27);
x_70 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_70, 0, x_27);
lean_ctor_set(x_70, 1, x_69);
x_71 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__50));
x_72 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__52));
x_73 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__53));
lean_inc(x_27);
x_74 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_74, 0, x_27);
lean_ctor_set(x_74, 1, x_73);
x_75 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__54));
lean_inc(x_27);
x_76 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_76, 0, x_27);
lean_ctor_set(x_76, 1, x_75);
lean_inc_ref(x_76);
lean_inc_ref(x_74);
lean_inc(x_27);
x_77 = l_Lean_Syntax_node2(x_27, x_72, x_74, x_76);
x_78 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__56));
x_79 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__58));
lean_inc_ref(x_32);
lean_inc(x_27);
x_80 = l_Lean_Syntax_node1(x_27, x_79, x_32);
x_81 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__60));
lean_inc_ref(x_32);
lean_inc(x_27);
x_82 = l_Lean_Syntax_node1(x_27, x_81, x_32);
lean_inc_ref_n(x_32, 2);
lean_inc(x_27);
x_83 = l_Lean_Syntax_node6(x_27, x_78, x_74, x_32, x_80, x_82, x_32, x_76);
lean_inc(x_27);
x_84 = l_Lean_Syntax_node2(x_27, x_71, x_77, x_83);
lean_inc_ref(x_70);
lean_inc(x_27);
x_85 = l_Lean_Syntax_node2(x_27, x_68, x_70, x_84);
lean_inc(x_27);
x_86 = l_Lean_Syntax_node1(x_27, x_30, x_85);
lean_inc_ref(x_55);
lean_inc_ref(x_44);
lean_inc(x_27);
x_87 = l_Lean_Syntax_node5(x_27, x_42, x_44, x_61, x_67, x_86, x_55);
lean_inc(x_27);
x_88 = l_Lean_Syntax_node2(x_27, x_30, x_56, x_87);
lean_inc_ref(x_32);
lean_inc(x_27);
x_89 = l_Lean_Syntax_node2(x_27, x_41, x_88, x_32);
x_90 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__62));
x_91 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__65));
lean_inc_ref_n(x_32, 2);
lean_inc(x_27);
x_92 = l_Lean_Syntax_node2(x_27, x_91, x_32, x_32);
x_93 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__66));
x_94 = l_Lean_Name_str___override(x_2, x_93);
x_95 = l_Lean_Name_append(x_14, x_94);
x_96 = l_Lean_mkIdentFromRef___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__2(x_95, x_18, x_7, x_21);
lean_dec_ref(x_7);
x_97 = lean_ctor_get(x_96, 0);
x_98 = lean_ctor_get(x_96, 1);
x_170 = !lean_is_exclusive(x_96);
if (x_170 == 0)
{
x_99 = x_96;
x_100 = x_170;
goto block_169;
}
else
{
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_96);
x_99 = lean_box(0);
x_100 = x_170;
goto block_169;
}
block_169:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_inc_ref(x_32);
lean_inc(x_92);
lean_inc_ref(x_70);
lean_inc(x_27);
x_101 = l_Lean_Syntax_node4(x_27, x_90, x_70, x_10, x_92, x_32);
x_102 = lean_unsigned_to_nat(2u);
x_103 = lean_mk_empty_array_with_capacity(x_102);
x_104 = lean_array_push(x_103, x_20);
x_105 = lean_array_push(x_104, x_40);
x_106 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_106, 0, x_39);
lean_ctor_set(x_106, 1, x_37);
lean_ctor_set(x_106, 2, x_105);
lean_inc_ref(x_32);
lean_inc(x_27);
x_107 = l_Lean_Syntax_node5(x_27, x_34, x_36, x_106, x_89, x_101, x_32);
lean_inc(x_33);
lean_inc(x_27);
x_108 = l_Lean_Syntax_node2(x_27, x_28, x_33, x_107);
x_109 = lean_array_push(x_1, x_108);
x_110 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__67));
x_111 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__68));
x_112 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__70));
lean_inc_ref(x_32);
lean_inc(x_27);
x_113 = l_Lean_Syntax_node1(x_27, x_112, x_32);
lean_inc(x_27);
x_114 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_114, 0, x_27);
lean_ctor_set(x_114, 1, x_110);
lean_inc_ref(x_32);
lean_inc(x_27);
x_115 = l_Lean_Syntax_node2(x_27, x_37, x_97, x_32);
lean_inc(x_27);
x_116 = l_Lean_Syntax_node1(x_27, x_30, x_115);
x_117 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__72));
x_118 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__74));
x_119 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__76));
x_120 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__78, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__78_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__78);
x_121 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__79));
lean_inc(x_25);
lean_inc(x_24);
x_122 = l_Lean_addMacroScope(x_24, x_121, x_25);
x_123 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__84));
lean_inc(x_27);
x_124 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_124, 0, x_27);
lean_ctor_set(x_124, 1, x_120);
lean_ctor_set(x_124, 2, x_122);
lean_ctor_set(x_124, 3, x_123);
lean_inc(x_27);
x_125 = l_Lean_Syntax_node1(x_27, x_30, x_13);
lean_inc(x_27);
x_126 = l_Lean_Syntax_node2(x_27, x_119, x_124, x_125);
lean_inc(x_27);
x_127 = l_Lean_Syntax_node2(x_27, x_118, x_52, x_126);
lean_inc_ref(x_32);
lean_inc(x_27);
x_128 = l_Lean_Syntax_node2(x_27, x_117, x_32, x_127);
x_129 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__86));
x_130 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__87));
lean_inc(x_27);
x_131 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_131, 0, x_27);
lean_ctor_set(x_131, 1, x_130);
x_132 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__89));
x_133 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__91));
x_134 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__93));
x_135 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__94, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__94_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__94);
x_136 = lean_box(0);
lean_inc(x_25);
lean_inc(x_24);
x_137 = l_Lean_addMacroScope(x_24, x_136, x_25);
x_138 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__107));
lean_inc(x_27);
x_139 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_139, 0, x_27);
lean_ctor_set(x_139, 1, x_135);
lean_ctor_set(x_139, 2, x_137);
lean_ctor_set(x_139, 3, x_138);
lean_inc(x_27);
x_140 = l_Lean_Syntax_node1(x_27, x_134, x_139);
lean_inc(x_140);
lean_inc(x_27);
x_141 = l_Lean_Syntax_node2(x_27, x_133, x_44, x_140);
x_142 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__108, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__108_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__108);
x_143 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__109));
x_144 = l_Lean_addMacroScope(x_24, x_143, x_25);
x_145 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__112));
lean_inc(x_27);
x_146 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_146, 0, x_27);
lean_ctor_set(x_146, 1, x_142);
lean_ctor_set(x_146, 2, x_144);
lean_ctor_set(x_146, 3, x_145);
x_147 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__114));
x_148 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__116));
x_149 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__117));
lean_inc(x_27);
x_150 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_150, 0, x_27);
lean_ctor_set(x_150, 1, x_149);
lean_inc(x_27);
x_151 = l_Lean_Syntax_node2(x_27, x_148, x_150, x_140);
x_152 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__118));
lean_inc(x_27);
x_153 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_153, 0, x_27);
lean_ctor_set(x_153, 1, x_152);
lean_inc_ref(x_146);
lean_inc(x_27);
x_154 = l_Lean_Syntax_node3(x_27, x_147, x_151, x_153, x_146);
lean_inc(x_27);
x_155 = l_Lean_Syntax_node1(x_27, x_30, x_154);
lean_inc(x_27);
x_156 = l_Lean_Syntax_node2(x_27, x_119, x_146, x_155);
lean_inc(x_27);
x_157 = l_Lean_Syntax_node3(x_27, x_132, x_141, x_156, x_55);
lean_inc(x_27);
x_158 = l_Lean_Syntax_node1(x_27, x_30, x_157);
x_159 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__119));
lean_inc(x_27);
x_160 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_160, 0, x_27);
lean_ctor_set(x_160, 1, x_159);
lean_inc(x_27);
x_161 = l_Lean_Syntax_node3(x_27, x_129, x_131, x_158, x_160);
lean_inc_ref(x_32);
lean_inc(x_27);
x_162 = l_Lean_Syntax_node4(x_27, x_90, x_70, x_161, x_92, x_32);
lean_inc(x_27);
x_163 = l_Lean_Syntax_node6(x_27, x_111, x_113, x_114, x_32, x_116, x_128, x_162);
x_164 = l_Lean_Syntax_node2(x_27, x_28, x_33, x_163);
x_165 = lean_array_push(x_109, x_164);
if (x_100 == 0)
{
lean_ctor_set(x_99, 0, x_165);
x_166 = x_99;
goto block_167;
}
else
{
lean_object* x_168; 
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_165);
lean_ctor_set(x_168, 1, x_98);
x_166 = x_168;
goto block_167;
}
block_167:
{
return x_166;
}
}
}
}
}
block_192:
{
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
lean_dec_ref(x_180);
x_6 = x_176;
x_7 = x_177;
x_8 = x_178;
x_9 = x_179;
x_10 = x_181;
x_11 = x_182;
goto block_175;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; uint8_t x_191; 
lean_dec_ref(x_178);
lean_dec_ref(x_177);
lean_dec(x_176);
lean_dec(x_2);
lean_dec_ref(x_1);
x_183 = lean_ctor_get(x_180, 0);
x_184 = lean_ctor_get(x_180, 1);
x_191 = !lean_is_exclusive(x_180);
if (x_191 == 0)
{
x_185 = x_180;
x_186 = x_191;
goto block_190;
}
else
{
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_180);
x_185 = lean_box(0);
x_186 = x_191;
goto block_190;
}
block_190:
{
lean_object* x_187; 
if (x_186 == 0)
{
x_187 = x_185;
goto block_188;
}
else
{
lean_object* x_189; 
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_183);
lean_ctor_set(x_189, 1, x_184);
x_187 = x_189;
goto block_188;
}
block_188:
{
return x_187;
}
}
}
}
block_210:
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; 
x_197 = lean_ctor_get(x_193, 0);
lean_inc_ref(x_197);
x_198 = lean_ctor_get(x_193, 2);
lean_inc(x_198);
x_199 = lean_mk_empty_array_with_capacity(x_198);
x_200 = lean_unsigned_to_nat(0u);
x_201 = lean_array_get_size(x_197);
x_202 = lean_nat_dec_lt(x_200, x_201);
if (x_202 == 0)
{
lean_dec_ref(x_197);
x_6 = x_198;
x_7 = x_195;
x_8 = x_199;
x_9 = x_200;
x_10 = x_194;
x_11 = x_196;
goto block_175;
}
else
{
uint8_t x_203; 
x_203 = lean_nat_dec_le(x_201, x_201);
if (x_203 == 0)
{
if (x_202 == 0)
{
lean_dec_ref(x_197);
x_6 = x_198;
x_7 = x_195;
x_8 = x_199;
x_9 = x_200;
x_10 = x_194;
x_11 = x_196;
goto block_175;
}
else
{
size_t x_204; size_t x_205; lean_object* x_206; 
x_204 = 0;
x_205 = lean_usize_of_nat(x_201);
lean_inc_ref(x_195);
x_206 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__3(x_3, x_197, x_204, x_205, x_194, x_195, x_196);
lean_dec_ref(x_197);
x_176 = x_198;
x_177 = x_195;
x_178 = x_199;
x_179 = x_200;
x_180 = x_206;
goto block_192;
}
}
else
{
size_t x_207; size_t x_208; lean_object* x_209; 
x_207 = 0;
x_208 = lean_usize_of_nat(x_201);
lean_inc_ref(x_195);
x_209 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__3(x_3, x_197, x_207, x_208, x_194, x_195, x_196);
lean_dec_ref(x_197);
x_176 = x_198;
x_177 = x_195;
x_178 = x_199;
x_179 = x_200;
x_180 = x_209;
goto block_192;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_211; lean_object* x_212; uint8_t x_213; 
x_193 = l_Lake_PackageConfig_instConfigInfo;
x_211 = lean_ctor_get(x_193, 2);
lean_inc(x_211);
x_212 = lean_unsigned_to_nat(0u);
x_213 = lean_nat_dec_eq(x_211, x_212);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_214 = lean_ctor_get(x_4, 1);
x_215 = lean_ctor_get(x_4, 2);
x_216 = lean_ctor_get(x_4, 5);
x_217 = l_Lean_SourceInfo_fromRef(x_216, x_213);
x_218 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__76));
x_219 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__122, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__122_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__122);
x_220 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__124));
lean_inc(x_215);
lean_inc(x_214);
x_221 = l_Lean_addMacroScope(x_214, x_220, x_215);
x_222 = lean_box(0);
lean_inc(x_217);
x_223 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_223, 0, x_217);
lean_ctor_set(x_223, 1, x_219);
lean_ctor_set(x_223, 2, x_221);
lean_ctor_set(x_223, 3, x_222);
x_224 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__10));
x_225 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__126));
x_226 = ((lean_object*)(l_Lake_Dependency_toToml___closed__12));
x_227 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__127));
lean_inc(x_217);
x_228 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_228, 0, x_217);
lean_ctor_set(x_228, 1, x_227);
lean_inc(x_217);
x_229 = l_Lean_Syntax_node1(x_217, x_226, x_228);
lean_inc(x_217);
x_230 = l_Lean_Syntax_node1(x_217, x_225, x_229);
x_231 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__0___closed__0));
x_232 = l_Nat_reprFast(x_211);
x_233 = lean_string_append(x_231, x_232);
lean_dec_ref(x_232);
x_234 = lean_box(0);
x_235 = l_Lean_Name_str___override(x_234, x_233);
x_236 = lean_mk_syntax_ident(x_235);
lean_inc(x_217);
x_237 = l_Lean_Syntax_node2(x_217, x_224, x_230, x_236);
x_238 = l_Lean_Syntax_node2(x_217, x_218, x_223, x_237);
x_194 = x_238;
x_195 = x_4;
x_196 = x_5;
goto block_210;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; uint8_t x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_211);
x_239 = lean_ctor_get(x_4, 1);
x_240 = lean_ctor_get(x_4, 2);
x_241 = lean_ctor_get(x_4, 5);
x_242 = 0;
x_243 = l_Lean_SourceInfo_fromRef(x_241, x_242);
x_244 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__34, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__34_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__34);
x_245 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__35));
lean_inc(x_240);
lean_inc(x_239);
x_246 = l_Lean_addMacroScope(x_239, x_245, x_240);
x_247 = lean_box(0);
x_248 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_248, 0, x_243);
lean_ctor_set(x_248, 1, x_244);
lean_ctor_set(x_248, 2, x_246);
lean_ctor_set(x_248, 3, x_247);
x_194 = x_248;
x_195 = x_4;
x_196 = x_5;
goto block_210;
}
block_175:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_174; 
lean_inc(x_8);
x_12 = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__1___redArg(x_8, x_8, x_9);
lean_dec(x_8);
lean_inc(x_2);
x_13 = l_Lean_Syntax_mkCApp(x_2, x_12);
x_14 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__13));
x_15 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__14));
lean_inc(x_2);
x_16 = l_Lean_Name_str___override(x_2, x_15);
x_17 = l_Lean_Name_append(x_14, x_16);
x_18 = 0;
x_19 = l_Lean_mkIdentFromRef___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__2(x_17, x_18, x_6, x_11);
x_20 = lean_ctor_get(x_19, 0);
x_21 = lean_ctor_get(x_19, 1);
x_174 = !lean_is_exclusive(x_19);
if (x_174 == 0)
{
x_22 = x_19;
x_23 = x_174;
goto block_173;
}
else
{
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_19);
x_22 = lean_box(0);
x_23 = x_174;
goto block_173;
}
block_173:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_24 = lean_ctor_get(x_6, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_6, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_6, 5);
x_27 = l_Lean_SourceInfo_fromRef(x_26, x_18);
x_28 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__17));
x_29 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__19));
x_30 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__10));
x_31 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__20, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__20_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__20);
lean_inc(x_27);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_32, 2, x_31);
lean_inc_ref_n(x_32, 7);
lean_inc(x_27);
x_33 = l_Lean_Syntax_node7(x_27, x_29, x_32, x_32, x_32, x_32, x_32, x_32, x_32);
x_34 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__22));
x_35 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__23));
lean_inc(x_27);
if (x_23 == 0)
{
lean_ctor_set_tag(x_22, 2);
lean_ctor_set(x_22, 1, x_35);
lean_ctor_set(x_22, 0, x_27);
x_36 = x_22;
goto block_171;
}
else
{
lean_object* x_172; 
x_172 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_172, 0, x_27);
lean_ctor_set(x_172, 1, x_35);
x_36 = x_172;
goto block_171;
}
block_171:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; uint8_t x_170; 
x_37 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__25));
x_38 = lean_mk_empty_array_with_capacity(x_7);
x_39 = lean_box(2);
x_40 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_30);
lean_ctor_set(x_40, 2, x_38);
x_41 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__27));
x_42 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__29));
x_43 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__30));
lean_inc(x_27);
x_44 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_44, 0, x_27);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__12, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__12_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__12);
x_46 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__13));
lean_inc(x_25);
lean_inc(x_24);
x_47 = l_Lean_addMacroScope(x_24, x_46, x_25);
x_48 = lean_box(0);
lean_inc(x_27);
x_49 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_49, 0, x_27);
lean_ctor_set(x_49, 1, x_45);
lean_ctor_set(x_49, 2, x_47);
lean_ctor_set(x_49, 3, x_48);
lean_inc(x_27);
x_50 = l_Lean_Syntax_node1(x_27, x_30, x_49);
x_51 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__31));
lean_inc(x_27);
x_52 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_52, 0, x_27);
lean_ctor_set(x_52, 1, x_51);
lean_inc(x_13);
lean_inc_ref(x_52);
lean_inc(x_27);
x_53 = l_Lean_Syntax_node2(x_27, x_30, x_52, x_13);
x_54 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__32));
lean_inc(x_27);
x_55 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_55, 0, x_27);
lean_ctor_set(x_55, 1, x_54);
lean_inc_ref(x_55);
lean_inc_ref(x_32);
lean_inc_ref(x_44);
lean_inc(x_27);
x_56 = l_Lean_Syntax_node5(x_27, x_42, x_44, x_50, x_53, x_32, x_55);
x_57 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__34, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__34_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__34);
x_58 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__35));
lean_inc(x_25);
lean_inc(x_24);
x_59 = l_Lean_addMacroScope(x_24, x_58, x_25);
lean_inc(x_27);
x_60 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_60, 0, x_27);
lean_ctor_set(x_60, 1, x_57);
lean_ctor_set(x_60, 2, x_59);
lean_ctor_set(x_60, 3, x_48);
lean_inc(x_27);
x_61 = l_Lean_Syntax_node1(x_27, x_30, x_60);
x_62 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__37, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__37_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__37);
x_63 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__38));
lean_inc(x_25);
lean_inc(x_24);
x_64 = l_Lean_addMacroScope(x_24, x_63, x_25);
x_65 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__45));
lean_inc(x_27);
x_66 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_66, 0, x_27);
lean_ctor_set(x_66, 1, x_62);
lean_ctor_set(x_66, 2, x_64);
lean_ctor_set(x_66, 3, x_65);
lean_inc_ref(x_52);
lean_inc(x_27);
x_67 = l_Lean_Syntax_node2(x_27, x_30, x_52, x_66);
x_68 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__47));
x_69 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__48));
lean_inc(x_27);
x_70 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_70, 0, x_27);
lean_ctor_set(x_70, 1, x_69);
x_71 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__50));
x_72 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__52));
x_73 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__53));
lean_inc(x_27);
x_74 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_74, 0, x_27);
lean_ctor_set(x_74, 1, x_73);
x_75 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__54));
lean_inc(x_27);
x_76 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_76, 0, x_27);
lean_ctor_set(x_76, 1, x_75);
lean_inc_ref(x_76);
lean_inc_ref(x_74);
lean_inc(x_27);
x_77 = l_Lean_Syntax_node2(x_27, x_72, x_74, x_76);
x_78 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__56));
x_79 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__58));
lean_inc_ref(x_32);
lean_inc(x_27);
x_80 = l_Lean_Syntax_node1(x_27, x_79, x_32);
x_81 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__60));
lean_inc_ref(x_32);
lean_inc(x_27);
x_82 = l_Lean_Syntax_node1(x_27, x_81, x_32);
lean_inc_ref_n(x_32, 2);
lean_inc(x_27);
x_83 = l_Lean_Syntax_node6(x_27, x_78, x_74, x_32, x_80, x_82, x_32, x_76);
lean_inc(x_27);
x_84 = l_Lean_Syntax_node2(x_27, x_71, x_77, x_83);
lean_inc_ref(x_70);
lean_inc(x_27);
x_85 = l_Lean_Syntax_node2(x_27, x_68, x_70, x_84);
lean_inc(x_27);
x_86 = l_Lean_Syntax_node1(x_27, x_30, x_85);
lean_inc_ref(x_55);
lean_inc_ref(x_44);
lean_inc(x_27);
x_87 = l_Lean_Syntax_node5(x_27, x_42, x_44, x_61, x_67, x_86, x_55);
lean_inc(x_27);
x_88 = l_Lean_Syntax_node2(x_27, x_30, x_56, x_87);
lean_inc_ref(x_32);
lean_inc(x_27);
x_89 = l_Lean_Syntax_node2(x_27, x_41, x_88, x_32);
x_90 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__62));
x_91 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__65));
lean_inc_ref_n(x_32, 2);
lean_inc(x_27);
x_92 = l_Lean_Syntax_node2(x_27, x_91, x_32, x_32);
x_93 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__66));
x_94 = l_Lean_Name_str___override(x_2, x_93);
x_95 = l_Lean_Name_append(x_14, x_94);
x_96 = l_Lean_mkIdentFromRef___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__2(x_95, x_18, x_6, x_21);
lean_dec_ref(x_6);
x_97 = lean_ctor_get(x_96, 0);
x_98 = lean_ctor_get(x_96, 1);
x_170 = !lean_is_exclusive(x_96);
if (x_170 == 0)
{
x_99 = x_96;
x_100 = x_170;
goto block_169;
}
else
{
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_96);
x_99 = lean_box(0);
x_100 = x_170;
goto block_169;
}
block_169:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_inc_ref(x_32);
lean_inc(x_92);
lean_inc_ref(x_70);
lean_inc(x_27);
x_101 = l_Lean_Syntax_node4(x_27, x_90, x_70, x_10, x_92, x_32);
x_102 = lean_unsigned_to_nat(2u);
x_103 = lean_mk_empty_array_with_capacity(x_102);
x_104 = lean_array_push(x_103, x_20);
x_105 = lean_array_push(x_104, x_40);
x_106 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_106, 0, x_39);
lean_ctor_set(x_106, 1, x_37);
lean_ctor_set(x_106, 2, x_105);
lean_inc_ref(x_32);
lean_inc(x_27);
x_107 = l_Lean_Syntax_node5(x_27, x_34, x_36, x_106, x_89, x_101, x_32);
lean_inc(x_33);
lean_inc(x_27);
x_108 = l_Lean_Syntax_node2(x_27, x_28, x_33, x_107);
x_109 = lean_array_push(x_1, x_108);
x_110 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__67));
x_111 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__68));
x_112 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__70));
lean_inc_ref(x_32);
lean_inc(x_27);
x_113 = l_Lean_Syntax_node1(x_27, x_112, x_32);
lean_inc(x_27);
x_114 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_114, 0, x_27);
lean_ctor_set(x_114, 1, x_110);
lean_inc_ref(x_32);
lean_inc(x_27);
x_115 = l_Lean_Syntax_node2(x_27, x_37, x_97, x_32);
lean_inc(x_27);
x_116 = l_Lean_Syntax_node1(x_27, x_30, x_115);
x_117 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__72));
x_118 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__74));
x_119 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__76));
x_120 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__78, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__78_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__78);
x_121 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__79));
lean_inc(x_25);
lean_inc(x_24);
x_122 = l_Lean_addMacroScope(x_24, x_121, x_25);
x_123 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__84));
lean_inc(x_27);
x_124 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_124, 0, x_27);
lean_ctor_set(x_124, 1, x_120);
lean_ctor_set(x_124, 2, x_122);
lean_ctor_set(x_124, 3, x_123);
lean_inc(x_27);
x_125 = l_Lean_Syntax_node1(x_27, x_30, x_13);
lean_inc(x_27);
x_126 = l_Lean_Syntax_node2(x_27, x_119, x_124, x_125);
lean_inc(x_27);
x_127 = l_Lean_Syntax_node2(x_27, x_118, x_52, x_126);
lean_inc_ref(x_32);
lean_inc(x_27);
x_128 = l_Lean_Syntax_node2(x_27, x_117, x_32, x_127);
x_129 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__86));
x_130 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__87));
lean_inc(x_27);
x_131 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_131, 0, x_27);
lean_ctor_set(x_131, 1, x_130);
x_132 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__89));
x_133 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__91));
x_134 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__93));
x_135 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__94, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__94_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__94);
x_136 = lean_box(0);
lean_inc(x_25);
lean_inc(x_24);
x_137 = l_Lean_addMacroScope(x_24, x_136, x_25);
x_138 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__107));
lean_inc(x_27);
x_139 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_139, 0, x_27);
lean_ctor_set(x_139, 1, x_135);
lean_ctor_set(x_139, 2, x_137);
lean_ctor_set(x_139, 3, x_138);
lean_inc(x_27);
x_140 = l_Lean_Syntax_node1(x_27, x_134, x_139);
lean_inc(x_140);
lean_inc(x_27);
x_141 = l_Lean_Syntax_node2(x_27, x_133, x_44, x_140);
x_142 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__108, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__108_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__108);
x_143 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__109));
x_144 = l_Lean_addMacroScope(x_24, x_143, x_25);
x_145 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__112));
lean_inc(x_27);
x_146 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_146, 0, x_27);
lean_ctor_set(x_146, 1, x_142);
lean_ctor_set(x_146, 2, x_144);
lean_ctor_set(x_146, 3, x_145);
x_147 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__114));
x_148 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__116));
x_149 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__117));
lean_inc(x_27);
x_150 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_150, 0, x_27);
lean_ctor_set(x_150, 1, x_149);
lean_inc(x_27);
x_151 = l_Lean_Syntax_node2(x_27, x_148, x_150, x_140);
x_152 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__118));
lean_inc(x_27);
x_153 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_153, 0, x_27);
lean_ctor_set(x_153, 1, x_152);
lean_inc_ref(x_146);
lean_inc(x_27);
x_154 = l_Lean_Syntax_node3(x_27, x_147, x_151, x_153, x_146);
lean_inc(x_27);
x_155 = l_Lean_Syntax_node1(x_27, x_30, x_154);
lean_inc(x_27);
x_156 = l_Lean_Syntax_node2(x_27, x_119, x_146, x_155);
lean_inc(x_27);
x_157 = l_Lean_Syntax_node3(x_27, x_132, x_141, x_156, x_55);
lean_inc(x_27);
x_158 = l_Lean_Syntax_node1(x_27, x_30, x_157);
x_159 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__119));
lean_inc(x_27);
x_160 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_160, 0, x_27);
lean_ctor_set(x_160, 1, x_159);
lean_inc(x_27);
x_161 = l_Lean_Syntax_node3(x_27, x_129, x_131, x_158, x_160);
lean_inc_ref(x_32);
lean_inc(x_27);
x_162 = l_Lean_Syntax_node4(x_27, x_90, x_70, x_161, x_92, x_32);
lean_inc(x_27);
x_163 = l_Lean_Syntax_node6(x_27, x_111, x_113, x_114, x_32, x_116, x_128, x_162);
x_164 = l_Lean_Syntax_node2(x_27, x_28, x_33, x_163);
x_165 = lean_array_push(x_109, x_164);
if (x_100 == 0)
{
lean_ctor_set(x_99, 0, x_165);
x_166 = x_99;
goto block_167;
}
else
{
lean_object* x_168; 
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_165);
lean_ctor_set(x_168, 1, x_98);
x_166 = x_168;
goto block_167;
}
block_167:
{
return x_166;
}
}
}
}
}
block_192:
{
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
lean_dec_ref(x_180);
x_6 = x_176;
x_7 = x_177;
x_8 = x_178;
x_9 = x_179;
x_10 = x_181;
x_11 = x_182;
goto block_175;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; uint8_t x_191; 
lean_dec_ref(x_179);
lean_dec(x_178);
lean_dec_ref(x_176);
lean_dec(x_2);
lean_dec_ref(x_1);
x_183 = lean_ctor_get(x_180, 0);
x_184 = lean_ctor_get(x_180, 1);
x_191 = !lean_is_exclusive(x_180);
if (x_191 == 0)
{
x_185 = x_180;
x_186 = x_191;
goto block_190;
}
else
{
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_180);
x_185 = lean_box(0);
x_186 = x_191;
goto block_190;
}
block_190:
{
lean_object* x_187; 
if (x_186 == 0)
{
x_187 = x_185;
goto block_188;
}
else
{
lean_object* x_189; 
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_183);
lean_ctor_set(x_189, 1, x_184);
x_187 = x_189;
goto block_188;
}
block_188:
{
return x_187;
}
}
}
}
block_210:
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; 
x_197 = lean_ctor_get(x_193, 0);
lean_inc_ref(x_197);
x_198 = lean_ctor_get(x_193, 2);
lean_inc(x_198);
x_199 = lean_mk_empty_array_with_capacity(x_198);
x_200 = lean_unsigned_to_nat(0u);
x_201 = lean_array_get_size(x_197);
x_202 = lean_nat_dec_lt(x_200, x_201);
if (x_202 == 0)
{
lean_dec_ref(x_197);
x_6 = x_195;
x_7 = x_200;
x_8 = x_198;
x_9 = x_199;
x_10 = x_194;
x_11 = x_196;
goto block_175;
}
else
{
uint8_t x_203; 
x_203 = lean_nat_dec_le(x_201, x_201);
if (x_203 == 0)
{
if (x_202 == 0)
{
lean_dec_ref(x_197);
x_6 = x_195;
x_7 = x_200;
x_8 = x_198;
x_9 = x_199;
x_10 = x_194;
x_11 = x_196;
goto block_175;
}
else
{
size_t x_204; size_t x_205; lean_object* x_206; 
x_204 = 0;
x_205 = lean_usize_of_nat(x_201);
lean_inc_ref(x_195);
x_206 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__3(x_3, x_197, x_204, x_205, x_194, x_195, x_196);
lean_dec_ref(x_197);
x_176 = x_195;
x_177 = x_200;
x_178 = x_198;
x_179 = x_199;
x_180 = x_206;
goto block_192;
}
}
else
{
size_t x_207; size_t x_208; lean_object* x_209; 
x_207 = 0;
x_208 = lean_usize_of_nat(x_201);
lean_inc_ref(x_195);
x_209 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__3(x_3, x_197, x_207, x_208, x_194, x_195, x_196);
lean_dec_ref(x_197);
x_176 = x_195;
x_177 = x_200;
x_178 = x_198;
x_179 = x_199;
x_180 = x_209;
goto block_192;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__6(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_211; lean_object* x_212; uint8_t x_213; 
x_193 = l_Lake_InputDirConfig_instConfigInfo;
x_211 = lean_ctor_get(x_193, 2);
lean_inc(x_211);
x_212 = lean_unsigned_to_nat(0u);
x_213 = lean_nat_dec_eq(x_211, x_212);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_214 = lean_ctor_get(x_4, 1);
x_215 = lean_ctor_get(x_4, 2);
x_216 = lean_ctor_get(x_4, 5);
x_217 = l_Lean_SourceInfo_fromRef(x_216, x_213);
x_218 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__76));
x_219 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__122, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__122_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__122);
x_220 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__124));
lean_inc(x_215);
lean_inc(x_214);
x_221 = l_Lean_addMacroScope(x_214, x_220, x_215);
x_222 = lean_box(0);
lean_inc(x_217);
x_223 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_223, 0, x_217);
lean_ctor_set(x_223, 1, x_219);
lean_ctor_set(x_223, 2, x_221);
lean_ctor_set(x_223, 3, x_222);
x_224 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__10));
x_225 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__126));
x_226 = ((lean_object*)(l_Lake_Dependency_toToml___closed__12));
x_227 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__127));
lean_inc(x_217);
x_228 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_228, 0, x_217);
lean_ctor_set(x_228, 1, x_227);
lean_inc(x_217);
x_229 = l_Lean_Syntax_node1(x_217, x_226, x_228);
lean_inc(x_217);
x_230 = l_Lean_Syntax_node1(x_217, x_225, x_229);
x_231 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__0___closed__0));
x_232 = l_Nat_reprFast(x_211);
x_233 = lean_string_append(x_231, x_232);
lean_dec_ref(x_232);
x_234 = lean_box(0);
x_235 = l_Lean_Name_str___override(x_234, x_233);
x_236 = lean_mk_syntax_ident(x_235);
lean_inc(x_217);
x_237 = l_Lean_Syntax_node2(x_217, x_224, x_230, x_236);
x_238 = l_Lean_Syntax_node2(x_217, x_218, x_223, x_237);
x_194 = x_238;
x_195 = x_4;
x_196 = x_5;
goto block_210;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; uint8_t x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_211);
x_239 = lean_ctor_get(x_4, 1);
x_240 = lean_ctor_get(x_4, 2);
x_241 = lean_ctor_get(x_4, 5);
x_242 = 0;
x_243 = l_Lean_SourceInfo_fromRef(x_241, x_242);
x_244 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__34, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__34_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__34);
x_245 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__35));
lean_inc(x_240);
lean_inc(x_239);
x_246 = l_Lean_addMacroScope(x_239, x_245, x_240);
x_247 = lean_box(0);
x_248 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_248, 0, x_243);
lean_ctor_set(x_248, 1, x_244);
lean_ctor_set(x_248, 2, x_246);
lean_ctor_set(x_248, 3, x_247);
x_194 = x_248;
x_195 = x_4;
x_196 = x_5;
goto block_210;
}
block_175:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_174; 
lean_inc(x_9);
x_12 = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__1___redArg(x_9, x_9, x_7);
lean_dec(x_9);
lean_inc(x_2);
x_13 = l_Lean_Syntax_mkCApp(x_2, x_12);
x_14 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__13));
x_15 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__14));
lean_inc(x_2);
x_16 = l_Lean_Name_str___override(x_2, x_15);
x_17 = l_Lean_Name_append(x_14, x_16);
x_18 = 0;
x_19 = l_Lean_mkIdentFromRef___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__2(x_17, x_18, x_8, x_11);
x_20 = lean_ctor_get(x_19, 0);
x_21 = lean_ctor_get(x_19, 1);
x_174 = !lean_is_exclusive(x_19);
if (x_174 == 0)
{
x_22 = x_19;
x_23 = x_174;
goto block_173;
}
else
{
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_19);
x_22 = lean_box(0);
x_23 = x_174;
goto block_173;
}
block_173:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_24 = lean_ctor_get(x_8, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_8, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_8, 5);
x_27 = l_Lean_SourceInfo_fromRef(x_26, x_18);
x_28 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__17));
x_29 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__19));
x_30 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__10));
x_31 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__20, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__20_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__20);
lean_inc(x_27);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_32, 2, x_31);
lean_inc_ref_n(x_32, 7);
lean_inc(x_27);
x_33 = l_Lean_Syntax_node7(x_27, x_29, x_32, x_32, x_32, x_32, x_32, x_32, x_32);
x_34 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__22));
x_35 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__23));
lean_inc(x_27);
if (x_23 == 0)
{
lean_ctor_set_tag(x_22, 2);
lean_ctor_set(x_22, 1, x_35);
lean_ctor_set(x_22, 0, x_27);
x_36 = x_22;
goto block_171;
}
else
{
lean_object* x_172; 
x_172 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_172, 0, x_27);
lean_ctor_set(x_172, 1, x_35);
x_36 = x_172;
goto block_171;
}
block_171:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; uint8_t x_170; 
x_37 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__25));
x_38 = lean_mk_empty_array_with_capacity(x_6);
x_39 = lean_box(2);
x_40 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_30);
lean_ctor_set(x_40, 2, x_38);
x_41 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__27));
x_42 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__29));
x_43 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__30));
lean_inc(x_27);
x_44 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_44, 0, x_27);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__12, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__12_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__12);
x_46 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__13));
lean_inc(x_25);
lean_inc(x_24);
x_47 = l_Lean_addMacroScope(x_24, x_46, x_25);
x_48 = lean_box(0);
lean_inc(x_27);
x_49 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_49, 0, x_27);
lean_ctor_set(x_49, 1, x_45);
lean_ctor_set(x_49, 2, x_47);
lean_ctor_set(x_49, 3, x_48);
lean_inc(x_27);
x_50 = l_Lean_Syntax_node1(x_27, x_30, x_49);
x_51 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__31));
lean_inc(x_27);
x_52 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_52, 0, x_27);
lean_ctor_set(x_52, 1, x_51);
lean_inc(x_13);
lean_inc_ref(x_52);
lean_inc(x_27);
x_53 = l_Lean_Syntax_node2(x_27, x_30, x_52, x_13);
x_54 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__32));
lean_inc(x_27);
x_55 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_55, 0, x_27);
lean_ctor_set(x_55, 1, x_54);
lean_inc_ref(x_55);
lean_inc_ref(x_32);
lean_inc_ref(x_44);
lean_inc(x_27);
x_56 = l_Lean_Syntax_node5(x_27, x_42, x_44, x_50, x_53, x_32, x_55);
x_57 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__34, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__34_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__34);
x_58 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__35));
lean_inc(x_25);
lean_inc(x_24);
x_59 = l_Lean_addMacroScope(x_24, x_58, x_25);
lean_inc(x_27);
x_60 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_60, 0, x_27);
lean_ctor_set(x_60, 1, x_57);
lean_ctor_set(x_60, 2, x_59);
lean_ctor_set(x_60, 3, x_48);
lean_inc(x_27);
x_61 = l_Lean_Syntax_node1(x_27, x_30, x_60);
x_62 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__37, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__37_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__37);
x_63 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__38));
lean_inc(x_25);
lean_inc(x_24);
x_64 = l_Lean_addMacroScope(x_24, x_63, x_25);
x_65 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__45));
lean_inc(x_27);
x_66 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_66, 0, x_27);
lean_ctor_set(x_66, 1, x_62);
lean_ctor_set(x_66, 2, x_64);
lean_ctor_set(x_66, 3, x_65);
lean_inc_ref(x_52);
lean_inc(x_27);
x_67 = l_Lean_Syntax_node2(x_27, x_30, x_52, x_66);
x_68 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__47));
x_69 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__48));
lean_inc(x_27);
x_70 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_70, 0, x_27);
lean_ctor_set(x_70, 1, x_69);
x_71 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__50));
x_72 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__52));
x_73 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__53));
lean_inc(x_27);
x_74 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_74, 0, x_27);
lean_ctor_set(x_74, 1, x_73);
x_75 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__54));
lean_inc(x_27);
x_76 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_76, 0, x_27);
lean_ctor_set(x_76, 1, x_75);
lean_inc_ref(x_76);
lean_inc_ref(x_74);
lean_inc(x_27);
x_77 = l_Lean_Syntax_node2(x_27, x_72, x_74, x_76);
x_78 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__56));
x_79 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__58));
lean_inc_ref(x_32);
lean_inc(x_27);
x_80 = l_Lean_Syntax_node1(x_27, x_79, x_32);
x_81 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__60));
lean_inc_ref(x_32);
lean_inc(x_27);
x_82 = l_Lean_Syntax_node1(x_27, x_81, x_32);
lean_inc_ref_n(x_32, 2);
lean_inc(x_27);
x_83 = l_Lean_Syntax_node6(x_27, x_78, x_74, x_32, x_80, x_82, x_32, x_76);
lean_inc(x_27);
x_84 = l_Lean_Syntax_node2(x_27, x_71, x_77, x_83);
lean_inc_ref(x_70);
lean_inc(x_27);
x_85 = l_Lean_Syntax_node2(x_27, x_68, x_70, x_84);
lean_inc(x_27);
x_86 = l_Lean_Syntax_node1(x_27, x_30, x_85);
lean_inc_ref(x_55);
lean_inc_ref(x_44);
lean_inc(x_27);
x_87 = l_Lean_Syntax_node5(x_27, x_42, x_44, x_61, x_67, x_86, x_55);
lean_inc(x_27);
x_88 = l_Lean_Syntax_node2(x_27, x_30, x_56, x_87);
lean_inc_ref(x_32);
lean_inc(x_27);
x_89 = l_Lean_Syntax_node2(x_27, x_41, x_88, x_32);
x_90 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__62));
x_91 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__65));
lean_inc_ref_n(x_32, 2);
lean_inc(x_27);
x_92 = l_Lean_Syntax_node2(x_27, x_91, x_32, x_32);
x_93 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__66));
x_94 = l_Lean_Name_str___override(x_2, x_93);
x_95 = l_Lean_Name_append(x_14, x_94);
x_96 = l_Lean_mkIdentFromRef___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__2(x_95, x_18, x_8, x_21);
lean_dec_ref(x_8);
x_97 = lean_ctor_get(x_96, 0);
x_98 = lean_ctor_get(x_96, 1);
x_170 = !lean_is_exclusive(x_96);
if (x_170 == 0)
{
x_99 = x_96;
x_100 = x_170;
goto block_169;
}
else
{
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_96);
x_99 = lean_box(0);
x_100 = x_170;
goto block_169;
}
block_169:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_inc_ref(x_32);
lean_inc(x_92);
lean_inc_ref(x_70);
lean_inc(x_27);
x_101 = l_Lean_Syntax_node4(x_27, x_90, x_70, x_10, x_92, x_32);
x_102 = lean_unsigned_to_nat(2u);
x_103 = lean_mk_empty_array_with_capacity(x_102);
x_104 = lean_array_push(x_103, x_20);
x_105 = lean_array_push(x_104, x_40);
x_106 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_106, 0, x_39);
lean_ctor_set(x_106, 1, x_37);
lean_ctor_set(x_106, 2, x_105);
lean_inc_ref(x_32);
lean_inc(x_27);
x_107 = l_Lean_Syntax_node5(x_27, x_34, x_36, x_106, x_89, x_101, x_32);
lean_inc(x_33);
lean_inc(x_27);
x_108 = l_Lean_Syntax_node2(x_27, x_28, x_33, x_107);
x_109 = lean_array_push(x_1, x_108);
x_110 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__67));
x_111 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__68));
x_112 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__70));
lean_inc_ref(x_32);
lean_inc(x_27);
x_113 = l_Lean_Syntax_node1(x_27, x_112, x_32);
lean_inc(x_27);
x_114 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_114, 0, x_27);
lean_ctor_set(x_114, 1, x_110);
lean_inc_ref(x_32);
lean_inc(x_27);
x_115 = l_Lean_Syntax_node2(x_27, x_37, x_97, x_32);
lean_inc(x_27);
x_116 = l_Lean_Syntax_node1(x_27, x_30, x_115);
x_117 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__72));
x_118 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__74));
x_119 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__76));
x_120 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__78, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__78_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__78);
x_121 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__79));
lean_inc(x_25);
lean_inc(x_24);
x_122 = l_Lean_addMacroScope(x_24, x_121, x_25);
x_123 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__84));
lean_inc(x_27);
x_124 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_124, 0, x_27);
lean_ctor_set(x_124, 1, x_120);
lean_ctor_set(x_124, 2, x_122);
lean_ctor_set(x_124, 3, x_123);
lean_inc(x_27);
x_125 = l_Lean_Syntax_node1(x_27, x_30, x_13);
lean_inc(x_27);
x_126 = l_Lean_Syntax_node2(x_27, x_119, x_124, x_125);
lean_inc(x_27);
x_127 = l_Lean_Syntax_node2(x_27, x_118, x_52, x_126);
lean_inc_ref(x_32);
lean_inc(x_27);
x_128 = l_Lean_Syntax_node2(x_27, x_117, x_32, x_127);
x_129 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__86));
x_130 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__87));
lean_inc(x_27);
x_131 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_131, 0, x_27);
lean_ctor_set(x_131, 1, x_130);
x_132 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__89));
x_133 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__91));
x_134 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__93));
x_135 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__94, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__94_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__94);
x_136 = lean_box(0);
lean_inc(x_25);
lean_inc(x_24);
x_137 = l_Lean_addMacroScope(x_24, x_136, x_25);
x_138 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__107));
lean_inc(x_27);
x_139 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_139, 0, x_27);
lean_ctor_set(x_139, 1, x_135);
lean_ctor_set(x_139, 2, x_137);
lean_ctor_set(x_139, 3, x_138);
lean_inc(x_27);
x_140 = l_Lean_Syntax_node1(x_27, x_134, x_139);
lean_inc(x_140);
lean_inc(x_27);
x_141 = l_Lean_Syntax_node2(x_27, x_133, x_44, x_140);
x_142 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__108, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__108_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__108);
x_143 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__109));
x_144 = l_Lean_addMacroScope(x_24, x_143, x_25);
x_145 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__112));
lean_inc(x_27);
x_146 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_146, 0, x_27);
lean_ctor_set(x_146, 1, x_142);
lean_ctor_set(x_146, 2, x_144);
lean_ctor_set(x_146, 3, x_145);
x_147 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__114));
x_148 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__116));
x_149 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__117));
lean_inc(x_27);
x_150 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_150, 0, x_27);
lean_ctor_set(x_150, 1, x_149);
lean_inc(x_27);
x_151 = l_Lean_Syntax_node2(x_27, x_148, x_150, x_140);
x_152 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__118));
lean_inc(x_27);
x_153 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_153, 0, x_27);
lean_ctor_set(x_153, 1, x_152);
lean_inc_ref(x_146);
lean_inc(x_27);
x_154 = l_Lean_Syntax_node3(x_27, x_147, x_151, x_153, x_146);
lean_inc(x_27);
x_155 = l_Lean_Syntax_node1(x_27, x_30, x_154);
lean_inc(x_27);
x_156 = l_Lean_Syntax_node2(x_27, x_119, x_146, x_155);
lean_inc(x_27);
x_157 = l_Lean_Syntax_node3(x_27, x_132, x_141, x_156, x_55);
lean_inc(x_27);
x_158 = l_Lean_Syntax_node1(x_27, x_30, x_157);
x_159 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__119));
lean_inc(x_27);
x_160 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_160, 0, x_27);
lean_ctor_set(x_160, 1, x_159);
lean_inc(x_27);
x_161 = l_Lean_Syntax_node3(x_27, x_129, x_131, x_158, x_160);
lean_inc_ref(x_32);
lean_inc(x_27);
x_162 = l_Lean_Syntax_node4(x_27, x_90, x_70, x_161, x_92, x_32);
lean_inc(x_27);
x_163 = l_Lean_Syntax_node6(x_27, x_111, x_113, x_114, x_32, x_116, x_128, x_162);
x_164 = l_Lean_Syntax_node2(x_27, x_28, x_33, x_163);
x_165 = lean_array_push(x_109, x_164);
if (x_100 == 0)
{
lean_ctor_set(x_99, 0, x_165);
x_166 = x_99;
goto block_167;
}
else
{
lean_object* x_168; 
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_165);
lean_ctor_set(x_168, 1, x_98);
x_166 = x_168;
goto block_167;
}
block_167:
{
return x_166;
}
}
}
}
}
block_192:
{
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
lean_dec_ref(x_180);
x_6 = x_177;
x_7 = x_176;
x_8 = x_178;
x_9 = x_179;
x_10 = x_181;
x_11 = x_182;
goto block_175;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; uint8_t x_191; 
lean_dec(x_179);
lean_dec_ref(x_178);
lean_dec_ref(x_176);
lean_dec(x_2);
lean_dec_ref(x_1);
x_183 = lean_ctor_get(x_180, 0);
x_184 = lean_ctor_get(x_180, 1);
x_191 = !lean_is_exclusive(x_180);
if (x_191 == 0)
{
x_185 = x_180;
x_186 = x_191;
goto block_190;
}
else
{
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_180);
x_185 = lean_box(0);
x_186 = x_191;
goto block_190;
}
block_190:
{
lean_object* x_187; 
if (x_186 == 0)
{
x_187 = x_185;
goto block_188;
}
else
{
lean_object* x_189; 
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_183);
lean_ctor_set(x_189, 1, x_184);
x_187 = x_189;
goto block_188;
}
block_188:
{
return x_187;
}
}
}
}
block_210:
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; 
x_197 = lean_ctor_get(x_193, 0);
lean_inc_ref(x_197);
x_198 = lean_ctor_get(x_193, 2);
lean_inc(x_198);
x_199 = lean_mk_empty_array_with_capacity(x_198);
x_200 = lean_unsigned_to_nat(0u);
x_201 = lean_array_get_size(x_197);
x_202 = lean_nat_dec_lt(x_200, x_201);
if (x_202 == 0)
{
lean_dec_ref(x_197);
x_6 = x_200;
x_7 = x_199;
x_8 = x_195;
x_9 = x_198;
x_10 = x_194;
x_11 = x_196;
goto block_175;
}
else
{
uint8_t x_203; 
x_203 = lean_nat_dec_le(x_201, x_201);
if (x_203 == 0)
{
if (x_202 == 0)
{
lean_dec_ref(x_197);
x_6 = x_200;
x_7 = x_199;
x_8 = x_195;
x_9 = x_198;
x_10 = x_194;
x_11 = x_196;
goto block_175;
}
else
{
size_t x_204; size_t x_205; lean_object* x_206; 
x_204 = 0;
x_205 = lean_usize_of_nat(x_201);
lean_inc_ref(x_195);
x_206 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__3(x_3, x_197, x_204, x_205, x_194, x_195, x_196);
lean_dec_ref(x_197);
x_176 = x_199;
x_177 = x_200;
x_178 = x_195;
x_179 = x_198;
x_180 = x_206;
goto block_192;
}
}
else
{
size_t x_207; size_t x_208; lean_object* x_209; 
x_207 = 0;
x_208 = lean_usize_of_nat(x_201);
lean_inc_ref(x_195);
x_209 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__3(x_3, x_197, x_207, x_208, x_194, x_195, x_196);
lean_dec_ref(x_197);
x_176 = x_199;
x_177 = x_200;
x_178 = x_195;
x_179 = x_198;
x_180 = x_209;
goto block_192;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_211; lean_object* x_212; uint8_t x_213; 
x_193 = l_Lake_InputFileConfig_instConfigInfo;
x_211 = lean_ctor_get(x_193, 2);
lean_inc(x_211);
x_212 = lean_unsigned_to_nat(0u);
x_213 = lean_nat_dec_eq(x_211, x_212);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_214 = lean_ctor_get(x_4, 1);
x_215 = lean_ctor_get(x_4, 2);
x_216 = lean_ctor_get(x_4, 5);
x_217 = l_Lean_SourceInfo_fromRef(x_216, x_213);
x_218 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__76));
x_219 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__122, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__122_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__122);
x_220 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__124));
lean_inc(x_215);
lean_inc(x_214);
x_221 = l_Lean_addMacroScope(x_214, x_220, x_215);
x_222 = lean_box(0);
lean_inc(x_217);
x_223 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_223, 0, x_217);
lean_ctor_set(x_223, 1, x_219);
lean_ctor_set(x_223, 2, x_221);
lean_ctor_set(x_223, 3, x_222);
x_224 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__10));
x_225 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__126));
x_226 = ((lean_object*)(l_Lake_Dependency_toToml___closed__12));
x_227 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__127));
lean_inc(x_217);
x_228 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_228, 0, x_217);
lean_ctor_set(x_228, 1, x_227);
lean_inc(x_217);
x_229 = l_Lean_Syntax_node1(x_217, x_226, x_228);
lean_inc(x_217);
x_230 = l_Lean_Syntax_node1(x_217, x_225, x_229);
x_231 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__0___closed__0));
x_232 = l_Nat_reprFast(x_211);
x_233 = lean_string_append(x_231, x_232);
lean_dec_ref(x_232);
x_234 = lean_box(0);
x_235 = l_Lean_Name_str___override(x_234, x_233);
x_236 = lean_mk_syntax_ident(x_235);
lean_inc(x_217);
x_237 = l_Lean_Syntax_node2(x_217, x_224, x_230, x_236);
x_238 = l_Lean_Syntax_node2(x_217, x_218, x_223, x_237);
x_194 = x_238;
x_195 = x_4;
x_196 = x_5;
goto block_210;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; uint8_t x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_211);
x_239 = lean_ctor_get(x_4, 1);
x_240 = lean_ctor_get(x_4, 2);
x_241 = lean_ctor_get(x_4, 5);
x_242 = 0;
x_243 = l_Lean_SourceInfo_fromRef(x_241, x_242);
x_244 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__34, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__34_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__34);
x_245 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__35));
lean_inc(x_240);
lean_inc(x_239);
x_246 = l_Lean_addMacroScope(x_239, x_245, x_240);
x_247 = lean_box(0);
x_248 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_248, 0, x_243);
lean_ctor_set(x_248, 1, x_244);
lean_ctor_set(x_248, 2, x_246);
lean_ctor_set(x_248, 3, x_247);
x_194 = x_248;
x_195 = x_4;
x_196 = x_5;
goto block_210;
}
block_175:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_174; 
lean_inc(x_9);
x_12 = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__1___redArg(x_9, x_9, x_8);
lean_dec(x_9);
lean_inc(x_2);
x_13 = l_Lean_Syntax_mkCApp(x_2, x_12);
x_14 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__13));
x_15 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__14));
lean_inc(x_2);
x_16 = l_Lean_Name_str___override(x_2, x_15);
x_17 = l_Lean_Name_append(x_14, x_16);
x_18 = 0;
x_19 = l_Lean_mkIdentFromRef___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__2(x_17, x_18, x_6, x_11);
x_20 = lean_ctor_get(x_19, 0);
x_21 = lean_ctor_get(x_19, 1);
x_174 = !lean_is_exclusive(x_19);
if (x_174 == 0)
{
x_22 = x_19;
x_23 = x_174;
goto block_173;
}
else
{
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_19);
x_22 = lean_box(0);
x_23 = x_174;
goto block_173;
}
block_173:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_24 = lean_ctor_get(x_6, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_6, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_6, 5);
x_27 = l_Lean_SourceInfo_fromRef(x_26, x_18);
x_28 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__17));
x_29 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__19));
x_30 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__10));
x_31 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__20, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__20_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__20);
lean_inc(x_27);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_32, 2, x_31);
lean_inc_ref_n(x_32, 7);
lean_inc(x_27);
x_33 = l_Lean_Syntax_node7(x_27, x_29, x_32, x_32, x_32, x_32, x_32, x_32, x_32);
x_34 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__22));
x_35 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__23));
lean_inc(x_27);
if (x_23 == 0)
{
lean_ctor_set_tag(x_22, 2);
lean_ctor_set(x_22, 1, x_35);
lean_ctor_set(x_22, 0, x_27);
x_36 = x_22;
goto block_171;
}
else
{
lean_object* x_172; 
x_172 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_172, 0, x_27);
lean_ctor_set(x_172, 1, x_35);
x_36 = x_172;
goto block_171;
}
block_171:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; uint8_t x_170; 
x_37 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__25));
x_38 = lean_mk_empty_array_with_capacity(x_7);
x_39 = lean_box(2);
x_40 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_30);
lean_ctor_set(x_40, 2, x_38);
x_41 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__27));
x_42 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__29));
x_43 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__30));
lean_inc(x_27);
x_44 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_44, 0, x_27);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__12, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__12_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__12);
x_46 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__13));
lean_inc(x_25);
lean_inc(x_24);
x_47 = l_Lean_addMacroScope(x_24, x_46, x_25);
x_48 = lean_box(0);
lean_inc(x_27);
x_49 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_49, 0, x_27);
lean_ctor_set(x_49, 1, x_45);
lean_ctor_set(x_49, 2, x_47);
lean_ctor_set(x_49, 3, x_48);
lean_inc(x_27);
x_50 = l_Lean_Syntax_node1(x_27, x_30, x_49);
x_51 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__31));
lean_inc(x_27);
x_52 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_52, 0, x_27);
lean_ctor_set(x_52, 1, x_51);
lean_inc(x_13);
lean_inc_ref(x_52);
lean_inc(x_27);
x_53 = l_Lean_Syntax_node2(x_27, x_30, x_52, x_13);
x_54 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__32));
lean_inc(x_27);
x_55 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_55, 0, x_27);
lean_ctor_set(x_55, 1, x_54);
lean_inc_ref(x_55);
lean_inc_ref(x_32);
lean_inc_ref(x_44);
lean_inc(x_27);
x_56 = l_Lean_Syntax_node5(x_27, x_42, x_44, x_50, x_53, x_32, x_55);
x_57 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__34, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__34_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__34);
x_58 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__35));
lean_inc(x_25);
lean_inc(x_24);
x_59 = l_Lean_addMacroScope(x_24, x_58, x_25);
lean_inc(x_27);
x_60 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_60, 0, x_27);
lean_ctor_set(x_60, 1, x_57);
lean_ctor_set(x_60, 2, x_59);
lean_ctor_set(x_60, 3, x_48);
lean_inc(x_27);
x_61 = l_Lean_Syntax_node1(x_27, x_30, x_60);
x_62 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__37, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__37_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__37);
x_63 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__38));
lean_inc(x_25);
lean_inc(x_24);
x_64 = l_Lean_addMacroScope(x_24, x_63, x_25);
x_65 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__45));
lean_inc(x_27);
x_66 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_66, 0, x_27);
lean_ctor_set(x_66, 1, x_62);
lean_ctor_set(x_66, 2, x_64);
lean_ctor_set(x_66, 3, x_65);
lean_inc_ref(x_52);
lean_inc(x_27);
x_67 = l_Lean_Syntax_node2(x_27, x_30, x_52, x_66);
x_68 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__47));
x_69 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__48));
lean_inc(x_27);
x_70 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_70, 0, x_27);
lean_ctor_set(x_70, 1, x_69);
x_71 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__50));
x_72 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__52));
x_73 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__53));
lean_inc(x_27);
x_74 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_74, 0, x_27);
lean_ctor_set(x_74, 1, x_73);
x_75 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__54));
lean_inc(x_27);
x_76 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_76, 0, x_27);
lean_ctor_set(x_76, 1, x_75);
lean_inc_ref(x_76);
lean_inc_ref(x_74);
lean_inc(x_27);
x_77 = l_Lean_Syntax_node2(x_27, x_72, x_74, x_76);
x_78 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__56));
x_79 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__58));
lean_inc_ref(x_32);
lean_inc(x_27);
x_80 = l_Lean_Syntax_node1(x_27, x_79, x_32);
x_81 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__60));
lean_inc_ref(x_32);
lean_inc(x_27);
x_82 = l_Lean_Syntax_node1(x_27, x_81, x_32);
lean_inc_ref_n(x_32, 2);
lean_inc(x_27);
x_83 = l_Lean_Syntax_node6(x_27, x_78, x_74, x_32, x_80, x_82, x_32, x_76);
lean_inc(x_27);
x_84 = l_Lean_Syntax_node2(x_27, x_71, x_77, x_83);
lean_inc_ref(x_70);
lean_inc(x_27);
x_85 = l_Lean_Syntax_node2(x_27, x_68, x_70, x_84);
lean_inc(x_27);
x_86 = l_Lean_Syntax_node1(x_27, x_30, x_85);
lean_inc_ref(x_55);
lean_inc_ref(x_44);
lean_inc(x_27);
x_87 = l_Lean_Syntax_node5(x_27, x_42, x_44, x_61, x_67, x_86, x_55);
lean_inc(x_27);
x_88 = l_Lean_Syntax_node2(x_27, x_30, x_56, x_87);
lean_inc_ref(x_32);
lean_inc(x_27);
x_89 = l_Lean_Syntax_node2(x_27, x_41, x_88, x_32);
x_90 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__62));
x_91 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__65));
lean_inc_ref_n(x_32, 2);
lean_inc(x_27);
x_92 = l_Lean_Syntax_node2(x_27, x_91, x_32, x_32);
x_93 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__66));
x_94 = l_Lean_Name_str___override(x_2, x_93);
x_95 = l_Lean_Name_append(x_14, x_94);
x_96 = l_Lean_mkIdentFromRef___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__2(x_95, x_18, x_6, x_21);
lean_dec_ref(x_6);
x_97 = lean_ctor_get(x_96, 0);
x_98 = lean_ctor_get(x_96, 1);
x_170 = !lean_is_exclusive(x_96);
if (x_170 == 0)
{
x_99 = x_96;
x_100 = x_170;
goto block_169;
}
else
{
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_96);
x_99 = lean_box(0);
x_100 = x_170;
goto block_169;
}
block_169:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_inc_ref(x_32);
lean_inc(x_92);
lean_inc_ref(x_70);
lean_inc(x_27);
x_101 = l_Lean_Syntax_node4(x_27, x_90, x_70, x_10, x_92, x_32);
x_102 = lean_unsigned_to_nat(2u);
x_103 = lean_mk_empty_array_with_capacity(x_102);
x_104 = lean_array_push(x_103, x_20);
x_105 = lean_array_push(x_104, x_40);
x_106 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_106, 0, x_39);
lean_ctor_set(x_106, 1, x_37);
lean_ctor_set(x_106, 2, x_105);
lean_inc_ref(x_32);
lean_inc(x_27);
x_107 = l_Lean_Syntax_node5(x_27, x_34, x_36, x_106, x_89, x_101, x_32);
lean_inc(x_33);
lean_inc(x_27);
x_108 = l_Lean_Syntax_node2(x_27, x_28, x_33, x_107);
x_109 = lean_array_push(x_1, x_108);
x_110 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__67));
x_111 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__68));
x_112 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__70));
lean_inc_ref(x_32);
lean_inc(x_27);
x_113 = l_Lean_Syntax_node1(x_27, x_112, x_32);
lean_inc(x_27);
x_114 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_114, 0, x_27);
lean_ctor_set(x_114, 1, x_110);
lean_inc_ref(x_32);
lean_inc(x_27);
x_115 = l_Lean_Syntax_node2(x_27, x_37, x_97, x_32);
lean_inc(x_27);
x_116 = l_Lean_Syntax_node1(x_27, x_30, x_115);
x_117 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__72));
x_118 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__74));
x_119 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__76));
x_120 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__78, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__78_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__78);
x_121 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__79));
lean_inc(x_25);
lean_inc(x_24);
x_122 = l_Lean_addMacroScope(x_24, x_121, x_25);
x_123 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__84));
lean_inc(x_27);
x_124 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_124, 0, x_27);
lean_ctor_set(x_124, 1, x_120);
lean_ctor_set(x_124, 2, x_122);
lean_ctor_set(x_124, 3, x_123);
lean_inc(x_27);
x_125 = l_Lean_Syntax_node1(x_27, x_30, x_13);
lean_inc(x_27);
x_126 = l_Lean_Syntax_node2(x_27, x_119, x_124, x_125);
lean_inc(x_27);
x_127 = l_Lean_Syntax_node2(x_27, x_118, x_52, x_126);
lean_inc_ref(x_32);
lean_inc(x_27);
x_128 = l_Lean_Syntax_node2(x_27, x_117, x_32, x_127);
x_129 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__86));
x_130 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__87));
lean_inc(x_27);
x_131 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_131, 0, x_27);
lean_ctor_set(x_131, 1, x_130);
x_132 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__89));
x_133 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__91));
x_134 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__93));
x_135 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__94, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__94_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__94);
x_136 = lean_box(0);
lean_inc(x_25);
lean_inc(x_24);
x_137 = l_Lean_addMacroScope(x_24, x_136, x_25);
x_138 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__107));
lean_inc(x_27);
x_139 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_139, 0, x_27);
lean_ctor_set(x_139, 1, x_135);
lean_ctor_set(x_139, 2, x_137);
lean_ctor_set(x_139, 3, x_138);
lean_inc(x_27);
x_140 = l_Lean_Syntax_node1(x_27, x_134, x_139);
lean_inc(x_140);
lean_inc(x_27);
x_141 = l_Lean_Syntax_node2(x_27, x_133, x_44, x_140);
x_142 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__108, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__108_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__108);
x_143 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__109));
x_144 = l_Lean_addMacroScope(x_24, x_143, x_25);
x_145 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__112));
lean_inc(x_27);
x_146 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_146, 0, x_27);
lean_ctor_set(x_146, 1, x_142);
lean_ctor_set(x_146, 2, x_144);
lean_ctor_set(x_146, 3, x_145);
x_147 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__114));
x_148 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__116));
x_149 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__117));
lean_inc(x_27);
x_150 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_150, 0, x_27);
lean_ctor_set(x_150, 1, x_149);
lean_inc(x_27);
x_151 = l_Lean_Syntax_node2(x_27, x_148, x_150, x_140);
x_152 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__118));
lean_inc(x_27);
x_153 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_153, 0, x_27);
lean_ctor_set(x_153, 1, x_152);
lean_inc_ref(x_146);
lean_inc(x_27);
x_154 = l_Lean_Syntax_node3(x_27, x_147, x_151, x_153, x_146);
lean_inc(x_27);
x_155 = l_Lean_Syntax_node1(x_27, x_30, x_154);
lean_inc(x_27);
x_156 = l_Lean_Syntax_node2(x_27, x_119, x_146, x_155);
lean_inc(x_27);
x_157 = l_Lean_Syntax_node3(x_27, x_132, x_141, x_156, x_55);
lean_inc(x_27);
x_158 = l_Lean_Syntax_node1(x_27, x_30, x_157);
x_159 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__119));
lean_inc(x_27);
x_160 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_160, 0, x_27);
lean_ctor_set(x_160, 1, x_159);
lean_inc(x_27);
x_161 = l_Lean_Syntax_node3(x_27, x_129, x_131, x_158, x_160);
lean_inc_ref(x_32);
lean_inc(x_27);
x_162 = l_Lean_Syntax_node4(x_27, x_90, x_70, x_161, x_92, x_32);
lean_inc(x_27);
x_163 = l_Lean_Syntax_node6(x_27, x_111, x_113, x_114, x_32, x_116, x_128, x_162);
x_164 = l_Lean_Syntax_node2(x_27, x_28, x_33, x_163);
x_165 = lean_array_push(x_109, x_164);
if (x_100 == 0)
{
lean_ctor_set(x_99, 0, x_165);
x_166 = x_99;
goto block_167;
}
else
{
lean_object* x_168; 
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_165);
lean_ctor_set(x_168, 1, x_98);
x_166 = x_168;
goto block_167;
}
block_167:
{
return x_166;
}
}
}
}
}
block_192:
{
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
lean_dec_ref(x_180);
x_6 = x_176;
x_7 = x_177;
x_8 = x_178;
x_9 = x_179;
x_10 = x_181;
x_11 = x_182;
goto block_175;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; uint8_t x_191; 
lean_dec(x_179);
lean_dec_ref(x_178);
lean_dec_ref(x_176);
lean_dec(x_2);
lean_dec_ref(x_1);
x_183 = lean_ctor_get(x_180, 0);
x_184 = lean_ctor_get(x_180, 1);
x_191 = !lean_is_exclusive(x_180);
if (x_191 == 0)
{
x_185 = x_180;
x_186 = x_191;
goto block_190;
}
else
{
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_180);
x_185 = lean_box(0);
x_186 = x_191;
goto block_190;
}
block_190:
{
lean_object* x_187; 
if (x_186 == 0)
{
x_187 = x_185;
goto block_188;
}
else
{
lean_object* x_189; 
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_183);
lean_ctor_set(x_189, 1, x_184);
x_187 = x_189;
goto block_188;
}
block_188:
{
return x_187;
}
}
}
}
block_210:
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; 
x_197 = lean_ctor_get(x_193, 0);
lean_inc_ref(x_197);
x_198 = lean_ctor_get(x_193, 2);
lean_inc(x_198);
x_199 = lean_mk_empty_array_with_capacity(x_198);
x_200 = lean_unsigned_to_nat(0u);
x_201 = lean_array_get_size(x_197);
x_202 = lean_nat_dec_lt(x_200, x_201);
if (x_202 == 0)
{
lean_dec_ref(x_197);
x_6 = x_195;
x_7 = x_200;
x_8 = x_199;
x_9 = x_198;
x_10 = x_194;
x_11 = x_196;
goto block_175;
}
else
{
uint8_t x_203; 
x_203 = lean_nat_dec_le(x_201, x_201);
if (x_203 == 0)
{
if (x_202 == 0)
{
lean_dec_ref(x_197);
x_6 = x_195;
x_7 = x_200;
x_8 = x_199;
x_9 = x_198;
x_10 = x_194;
x_11 = x_196;
goto block_175;
}
else
{
size_t x_204; size_t x_205; lean_object* x_206; 
x_204 = 0;
x_205 = lean_usize_of_nat(x_201);
lean_inc_ref(x_195);
x_206 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__3(x_3, x_197, x_204, x_205, x_194, x_195, x_196);
lean_dec_ref(x_197);
x_176 = x_195;
x_177 = x_200;
x_178 = x_199;
x_179 = x_198;
x_180 = x_206;
goto block_192;
}
}
else
{
size_t x_207; size_t x_208; lean_object* x_209; 
x_207 = 0;
x_208 = lean_usize_of_nat(x_201);
lean_inc_ref(x_195);
x_209 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__3(x_3, x_197, x_207, x_208, x_194, x_195, x_196);
lean_dec_ref(x_197);
x_176 = x_195;
x_177 = x_200;
x_178 = x_199;
x_179 = x_198;
x_180 = x_209;
goto block_192;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_211; lean_object* x_212; uint8_t x_213; 
x_193 = l_Lake_WorkspaceConfig_instConfigInfo;
x_211 = lean_ctor_get(x_193, 2);
lean_inc(x_211);
x_212 = lean_unsigned_to_nat(0u);
x_213 = lean_nat_dec_eq(x_211, x_212);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_214 = lean_ctor_get(x_4, 1);
x_215 = lean_ctor_get(x_4, 2);
x_216 = lean_ctor_get(x_4, 5);
x_217 = l_Lean_SourceInfo_fromRef(x_216, x_213);
x_218 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__76));
x_219 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__122, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__122_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__122);
x_220 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__124));
lean_inc(x_215);
lean_inc(x_214);
x_221 = l_Lean_addMacroScope(x_214, x_220, x_215);
x_222 = lean_box(0);
lean_inc(x_217);
x_223 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_223, 0, x_217);
lean_ctor_set(x_223, 1, x_219);
lean_ctor_set(x_223, 2, x_221);
lean_ctor_set(x_223, 3, x_222);
x_224 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__10));
x_225 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__126));
x_226 = ((lean_object*)(l_Lake_Dependency_toToml___closed__12));
x_227 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__127));
lean_inc(x_217);
x_228 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_228, 0, x_217);
lean_ctor_set(x_228, 1, x_227);
lean_inc(x_217);
x_229 = l_Lean_Syntax_node1(x_217, x_226, x_228);
lean_inc(x_217);
x_230 = l_Lean_Syntax_node1(x_217, x_225, x_229);
x_231 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__0___closed__0));
x_232 = l_Nat_reprFast(x_211);
x_233 = lean_string_append(x_231, x_232);
lean_dec_ref(x_232);
x_234 = lean_box(0);
x_235 = l_Lean_Name_str___override(x_234, x_233);
x_236 = lean_mk_syntax_ident(x_235);
lean_inc(x_217);
x_237 = l_Lean_Syntax_node2(x_217, x_224, x_230, x_236);
x_238 = l_Lean_Syntax_node2(x_217, x_218, x_223, x_237);
x_194 = x_238;
x_195 = x_4;
x_196 = x_5;
goto block_210;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; uint8_t x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_211);
x_239 = lean_ctor_get(x_4, 1);
x_240 = lean_ctor_get(x_4, 2);
x_241 = lean_ctor_get(x_4, 5);
x_242 = 0;
x_243 = l_Lean_SourceInfo_fromRef(x_241, x_242);
x_244 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__34, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__34_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__34);
x_245 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__35));
lean_inc(x_240);
lean_inc(x_239);
x_246 = l_Lean_addMacroScope(x_239, x_245, x_240);
x_247 = lean_box(0);
x_248 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_248, 0, x_243);
lean_ctor_set(x_248, 1, x_244);
lean_ctor_set(x_248, 2, x_246);
lean_ctor_set(x_248, 3, x_247);
x_194 = x_248;
x_195 = x_4;
x_196 = x_5;
goto block_210;
}
block_175:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_174; 
lean_inc(x_7);
x_12 = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__1___redArg(x_7, x_7, x_9);
lean_dec(x_7);
lean_inc(x_2);
x_13 = l_Lean_Syntax_mkCApp(x_2, x_12);
x_14 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__13));
x_15 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__14));
lean_inc(x_2);
x_16 = l_Lean_Name_str___override(x_2, x_15);
x_17 = l_Lean_Name_append(x_14, x_16);
x_18 = 0;
x_19 = l_Lean_mkIdentFromRef___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__2(x_17, x_18, x_8, x_11);
x_20 = lean_ctor_get(x_19, 0);
x_21 = lean_ctor_get(x_19, 1);
x_174 = !lean_is_exclusive(x_19);
if (x_174 == 0)
{
x_22 = x_19;
x_23 = x_174;
goto block_173;
}
else
{
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_19);
x_22 = lean_box(0);
x_23 = x_174;
goto block_173;
}
block_173:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_24 = lean_ctor_get(x_8, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_8, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_8, 5);
x_27 = l_Lean_SourceInfo_fromRef(x_26, x_18);
x_28 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__17));
x_29 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__19));
x_30 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__10));
x_31 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__20, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__20_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__20);
lean_inc(x_27);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_32, 2, x_31);
lean_inc_ref_n(x_32, 7);
lean_inc(x_27);
x_33 = l_Lean_Syntax_node7(x_27, x_29, x_32, x_32, x_32, x_32, x_32, x_32, x_32);
x_34 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__22));
x_35 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__23));
lean_inc(x_27);
if (x_23 == 0)
{
lean_ctor_set_tag(x_22, 2);
lean_ctor_set(x_22, 1, x_35);
lean_ctor_set(x_22, 0, x_27);
x_36 = x_22;
goto block_171;
}
else
{
lean_object* x_172; 
x_172 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_172, 0, x_27);
lean_ctor_set(x_172, 1, x_35);
x_36 = x_172;
goto block_171;
}
block_171:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; uint8_t x_170; 
x_37 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__25));
x_38 = lean_mk_empty_array_with_capacity(x_6);
x_39 = lean_box(2);
x_40 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_30);
lean_ctor_set(x_40, 2, x_38);
x_41 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__27));
x_42 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__29));
x_43 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__30));
lean_inc(x_27);
x_44 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_44, 0, x_27);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__12, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__12_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__12);
x_46 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__13));
lean_inc(x_25);
lean_inc(x_24);
x_47 = l_Lean_addMacroScope(x_24, x_46, x_25);
x_48 = lean_box(0);
lean_inc(x_27);
x_49 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_49, 0, x_27);
lean_ctor_set(x_49, 1, x_45);
lean_ctor_set(x_49, 2, x_47);
lean_ctor_set(x_49, 3, x_48);
lean_inc(x_27);
x_50 = l_Lean_Syntax_node1(x_27, x_30, x_49);
x_51 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__31));
lean_inc(x_27);
x_52 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_52, 0, x_27);
lean_ctor_set(x_52, 1, x_51);
lean_inc(x_13);
lean_inc_ref(x_52);
lean_inc(x_27);
x_53 = l_Lean_Syntax_node2(x_27, x_30, x_52, x_13);
x_54 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__32));
lean_inc(x_27);
x_55 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_55, 0, x_27);
lean_ctor_set(x_55, 1, x_54);
lean_inc_ref(x_55);
lean_inc_ref(x_32);
lean_inc_ref(x_44);
lean_inc(x_27);
x_56 = l_Lean_Syntax_node5(x_27, x_42, x_44, x_50, x_53, x_32, x_55);
x_57 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__34, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__34_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__34);
x_58 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__35));
lean_inc(x_25);
lean_inc(x_24);
x_59 = l_Lean_addMacroScope(x_24, x_58, x_25);
lean_inc(x_27);
x_60 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_60, 0, x_27);
lean_ctor_set(x_60, 1, x_57);
lean_ctor_set(x_60, 2, x_59);
lean_ctor_set(x_60, 3, x_48);
lean_inc(x_27);
x_61 = l_Lean_Syntax_node1(x_27, x_30, x_60);
x_62 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__37, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__37_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__37);
x_63 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__38));
lean_inc(x_25);
lean_inc(x_24);
x_64 = l_Lean_addMacroScope(x_24, x_63, x_25);
x_65 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__45));
lean_inc(x_27);
x_66 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_66, 0, x_27);
lean_ctor_set(x_66, 1, x_62);
lean_ctor_set(x_66, 2, x_64);
lean_ctor_set(x_66, 3, x_65);
lean_inc_ref(x_52);
lean_inc(x_27);
x_67 = l_Lean_Syntax_node2(x_27, x_30, x_52, x_66);
x_68 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__47));
x_69 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__48));
lean_inc(x_27);
x_70 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_70, 0, x_27);
lean_ctor_set(x_70, 1, x_69);
x_71 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__50));
x_72 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__52));
x_73 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__53));
lean_inc(x_27);
x_74 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_74, 0, x_27);
lean_ctor_set(x_74, 1, x_73);
x_75 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__54));
lean_inc(x_27);
x_76 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_76, 0, x_27);
lean_ctor_set(x_76, 1, x_75);
lean_inc_ref(x_76);
lean_inc_ref(x_74);
lean_inc(x_27);
x_77 = l_Lean_Syntax_node2(x_27, x_72, x_74, x_76);
x_78 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__56));
x_79 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__58));
lean_inc_ref(x_32);
lean_inc(x_27);
x_80 = l_Lean_Syntax_node1(x_27, x_79, x_32);
x_81 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__60));
lean_inc_ref(x_32);
lean_inc(x_27);
x_82 = l_Lean_Syntax_node1(x_27, x_81, x_32);
lean_inc_ref_n(x_32, 2);
lean_inc(x_27);
x_83 = l_Lean_Syntax_node6(x_27, x_78, x_74, x_32, x_80, x_82, x_32, x_76);
lean_inc(x_27);
x_84 = l_Lean_Syntax_node2(x_27, x_71, x_77, x_83);
lean_inc_ref(x_70);
lean_inc(x_27);
x_85 = l_Lean_Syntax_node2(x_27, x_68, x_70, x_84);
lean_inc(x_27);
x_86 = l_Lean_Syntax_node1(x_27, x_30, x_85);
lean_inc_ref(x_55);
lean_inc_ref(x_44);
lean_inc(x_27);
x_87 = l_Lean_Syntax_node5(x_27, x_42, x_44, x_61, x_67, x_86, x_55);
lean_inc(x_27);
x_88 = l_Lean_Syntax_node2(x_27, x_30, x_56, x_87);
lean_inc_ref(x_32);
lean_inc(x_27);
x_89 = l_Lean_Syntax_node2(x_27, x_41, x_88, x_32);
x_90 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__62));
x_91 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__65));
lean_inc_ref_n(x_32, 2);
lean_inc(x_27);
x_92 = l_Lean_Syntax_node2(x_27, x_91, x_32, x_32);
x_93 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__66));
x_94 = l_Lean_Name_str___override(x_2, x_93);
x_95 = l_Lean_Name_append(x_14, x_94);
x_96 = l_Lean_mkIdentFromRef___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__2(x_95, x_18, x_8, x_21);
lean_dec_ref(x_8);
x_97 = lean_ctor_get(x_96, 0);
x_98 = lean_ctor_get(x_96, 1);
x_170 = !lean_is_exclusive(x_96);
if (x_170 == 0)
{
x_99 = x_96;
x_100 = x_170;
goto block_169;
}
else
{
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_96);
x_99 = lean_box(0);
x_100 = x_170;
goto block_169;
}
block_169:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_inc_ref(x_32);
lean_inc(x_92);
lean_inc_ref(x_70);
lean_inc(x_27);
x_101 = l_Lean_Syntax_node4(x_27, x_90, x_70, x_10, x_92, x_32);
x_102 = lean_unsigned_to_nat(2u);
x_103 = lean_mk_empty_array_with_capacity(x_102);
x_104 = lean_array_push(x_103, x_20);
x_105 = lean_array_push(x_104, x_40);
x_106 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_106, 0, x_39);
lean_ctor_set(x_106, 1, x_37);
lean_ctor_set(x_106, 2, x_105);
lean_inc_ref(x_32);
lean_inc(x_27);
x_107 = l_Lean_Syntax_node5(x_27, x_34, x_36, x_106, x_89, x_101, x_32);
lean_inc(x_33);
lean_inc(x_27);
x_108 = l_Lean_Syntax_node2(x_27, x_28, x_33, x_107);
x_109 = lean_array_push(x_1, x_108);
x_110 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__67));
x_111 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__68));
x_112 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__70));
lean_inc_ref(x_32);
lean_inc(x_27);
x_113 = l_Lean_Syntax_node1(x_27, x_112, x_32);
lean_inc(x_27);
x_114 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_114, 0, x_27);
lean_ctor_set(x_114, 1, x_110);
lean_inc_ref(x_32);
lean_inc(x_27);
x_115 = l_Lean_Syntax_node2(x_27, x_37, x_97, x_32);
lean_inc(x_27);
x_116 = l_Lean_Syntax_node1(x_27, x_30, x_115);
x_117 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__72));
x_118 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__74));
x_119 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__76));
x_120 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__78, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__78_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__78);
x_121 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__79));
lean_inc(x_25);
lean_inc(x_24);
x_122 = l_Lean_addMacroScope(x_24, x_121, x_25);
x_123 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__84));
lean_inc(x_27);
x_124 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_124, 0, x_27);
lean_ctor_set(x_124, 1, x_120);
lean_ctor_set(x_124, 2, x_122);
lean_ctor_set(x_124, 3, x_123);
lean_inc(x_27);
x_125 = l_Lean_Syntax_node1(x_27, x_30, x_13);
lean_inc(x_27);
x_126 = l_Lean_Syntax_node2(x_27, x_119, x_124, x_125);
lean_inc(x_27);
x_127 = l_Lean_Syntax_node2(x_27, x_118, x_52, x_126);
lean_inc_ref(x_32);
lean_inc(x_27);
x_128 = l_Lean_Syntax_node2(x_27, x_117, x_32, x_127);
x_129 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__86));
x_130 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__87));
lean_inc(x_27);
x_131 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_131, 0, x_27);
lean_ctor_set(x_131, 1, x_130);
x_132 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__89));
x_133 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__91));
x_134 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__93));
x_135 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__94, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__94_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__94);
x_136 = lean_box(0);
lean_inc(x_25);
lean_inc(x_24);
x_137 = l_Lean_addMacroScope(x_24, x_136, x_25);
x_138 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__107));
lean_inc(x_27);
x_139 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_139, 0, x_27);
lean_ctor_set(x_139, 1, x_135);
lean_ctor_set(x_139, 2, x_137);
lean_ctor_set(x_139, 3, x_138);
lean_inc(x_27);
x_140 = l_Lean_Syntax_node1(x_27, x_134, x_139);
lean_inc(x_140);
lean_inc(x_27);
x_141 = l_Lean_Syntax_node2(x_27, x_133, x_44, x_140);
x_142 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__108, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__108_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__108);
x_143 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__109));
x_144 = l_Lean_addMacroScope(x_24, x_143, x_25);
x_145 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__112));
lean_inc(x_27);
x_146 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_146, 0, x_27);
lean_ctor_set(x_146, 1, x_142);
lean_ctor_set(x_146, 2, x_144);
lean_ctor_set(x_146, 3, x_145);
x_147 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__114));
x_148 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__116));
x_149 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__117));
lean_inc(x_27);
x_150 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_150, 0, x_27);
lean_ctor_set(x_150, 1, x_149);
lean_inc(x_27);
x_151 = l_Lean_Syntax_node2(x_27, x_148, x_150, x_140);
x_152 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__118));
lean_inc(x_27);
x_153 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_153, 0, x_27);
lean_ctor_set(x_153, 1, x_152);
lean_inc_ref(x_146);
lean_inc(x_27);
x_154 = l_Lean_Syntax_node3(x_27, x_147, x_151, x_153, x_146);
lean_inc(x_27);
x_155 = l_Lean_Syntax_node1(x_27, x_30, x_154);
lean_inc(x_27);
x_156 = l_Lean_Syntax_node2(x_27, x_119, x_146, x_155);
lean_inc(x_27);
x_157 = l_Lean_Syntax_node3(x_27, x_132, x_141, x_156, x_55);
lean_inc(x_27);
x_158 = l_Lean_Syntax_node1(x_27, x_30, x_157);
x_159 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__119));
lean_inc(x_27);
x_160 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_160, 0, x_27);
lean_ctor_set(x_160, 1, x_159);
lean_inc(x_27);
x_161 = l_Lean_Syntax_node3(x_27, x_129, x_131, x_158, x_160);
lean_inc_ref(x_32);
lean_inc(x_27);
x_162 = l_Lean_Syntax_node4(x_27, x_90, x_70, x_161, x_92, x_32);
lean_inc(x_27);
x_163 = l_Lean_Syntax_node6(x_27, x_111, x_113, x_114, x_32, x_116, x_128, x_162);
x_164 = l_Lean_Syntax_node2(x_27, x_28, x_33, x_163);
x_165 = lean_array_push(x_109, x_164);
if (x_100 == 0)
{
lean_ctor_set(x_99, 0, x_165);
x_166 = x_99;
goto block_167;
}
else
{
lean_object* x_168; 
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_165);
lean_ctor_set(x_168, 1, x_98);
x_166 = x_168;
goto block_167;
}
block_167:
{
return x_166;
}
}
}
}
}
block_192:
{
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
lean_dec_ref(x_180);
x_6 = x_176;
x_7 = x_177;
x_8 = x_179;
x_9 = x_178;
x_10 = x_181;
x_11 = x_182;
goto block_175;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; uint8_t x_191; 
lean_dec_ref(x_179);
lean_dec_ref(x_178);
lean_dec(x_177);
lean_dec(x_2);
lean_dec_ref(x_1);
x_183 = lean_ctor_get(x_180, 0);
x_184 = lean_ctor_get(x_180, 1);
x_191 = !lean_is_exclusive(x_180);
if (x_191 == 0)
{
x_185 = x_180;
x_186 = x_191;
goto block_190;
}
else
{
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_180);
x_185 = lean_box(0);
x_186 = x_191;
goto block_190;
}
block_190:
{
lean_object* x_187; 
if (x_186 == 0)
{
x_187 = x_185;
goto block_188;
}
else
{
lean_object* x_189; 
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_183);
lean_ctor_set(x_189, 1, x_184);
x_187 = x_189;
goto block_188;
}
block_188:
{
return x_187;
}
}
}
}
block_210:
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; 
x_197 = lean_ctor_get(x_193, 0);
lean_inc_ref(x_197);
x_198 = lean_ctor_get(x_193, 2);
lean_inc(x_198);
x_199 = lean_mk_empty_array_with_capacity(x_198);
x_200 = lean_unsigned_to_nat(0u);
x_201 = lean_array_get_size(x_197);
x_202 = lean_nat_dec_lt(x_200, x_201);
if (x_202 == 0)
{
lean_dec_ref(x_197);
x_6 = x_200;
x_7 = x_198;
x_8 = x_195;
x_9 = x_199;
x_10 = x_194;
x_11 = x_196;
goto block_175;
}
else
{
uint8_t x_203; 
x_203 = lean_nat_dec_le(x_201, x_201);
if (x_203 == 0)
{
if (x_202 == 0)
{
lean_dec_ref(x_197);
x_6 = x_200;
x_7 = x_198;
x_8 = x_195;
x_9 = x_199;
x_10 = x_194;
x_11 = x_196;
goto block_175;
}
else
{
size_t x_204; size_t x_205; lean_object* x_206; 
x_204 = 0;
x_205 = lean_usize_of_nat(x_201);
lean_inc_ref(x_195);
x_206 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__3(x_3, x_197, x_204, x_205, x_194, x_195, x_196);
lean_dec_ref(x_197);
x_176 = x_200;
x_177 = x_198;
x_178 = x_199;
x_179 = x_195;
x_180 = x_206;
goto block_192;
}
}
else
{
size_t x_207; size_t x_208; lean_object* x_209; 
x_207 = 0;
x_208 = lean_usize_of_nat(x_201);
lean_inc_ref(x_195);
x_209 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__3(x_3, x_197, x_207, x_208, x_194, x_195, x_196);
lean_dec_ref(x_197);
x_176 = x_200;
x_177 = x_198;
x_178 = x_199;
x_179 = x_195;
x_180 = x_209;
goto block_192;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__5(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_211; lean_object* x_212; uint8_t x_213; 
x_193 = l_Lake_LeanLibConfig_instConfigInfo;
x_211 = lean_ctor_get(x_193, 2);
lean_inc(x_211);
x_212 = lean_unsigned_to_nat(0u);
x_213 = lean_nat_dec_eq(x_211, x_212);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_214 = lean_ctor_get(x_4, 1);
x_215 = lean_ctor_get(x_4, 2);
x_216 = lean_ctor_get(x_4, 5);
x_217 = l_Lean_SourceInfo_fromRef(x_216, x_213);
x_218 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__76));
x_219 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__122, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__122_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__122);
x_220 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__124));
lean_inc(x_215);
lean_inc(x_214);
x_221 = l_Lean_addMacroScope(x_214, x_220, x_215);
x_222 = lean_box(0);
lean_inc(x_217);
x_223 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_223, 0, x_217);
lean_ctor_set(x_223, 1, x_219);
lean_ctor_set(x_223, 2, x_221);
lean_ctor_set(x_223, 3, x_222);
x_224 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__10));
x_225 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__126));
x_226 = ((lean_object*)(l_Lake_Dependency_toToml___closed__12));
x_227 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__127));
lean_inc(x_217);
x_228 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_228, 0, x_217);
lean_ctor_set(x_228, 1, x_227);
lean_inc(x_217);
x_229 = l_Lean_Syntax_node1(x_217, x_226, x_228);
lean_inc(x_217);
x_230 = l_Lean_Syntax_node1(x_217, x_225, x_229);
x_231 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__0___closed__0));
x_232 = l_Nat_reprFast(x_211);
x_233 = lean_string_append(x_231, x_232);
lean_dec_ref(x_232);
x_234 = lean_box(0);
x_235 = l_Lean_Name_str___override(x_234, x_233);
x_236 = lean_mk_syntax_ident(x_235);
lean_inc(x_217);
x_237 = l_Lean_Syntax_node2(x_217, x_224, x_230, x_236);
x_238 = l_Lean_Syntax_node2(x_217, x_218, x_223, x_237);
x_194 = x_238;
x_195 = x_4;
x_196 = x_5;
goto block_210;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; uint8_t x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_211);
x_239 = lean_ctor_get(x_4, 1);
x_240 = lean_ctor_get(x_4, 2);
x_241 = lean_ctor_get(x_4, 5);
x_242 = 0;
x_243 = l_Lean_SourceInfo_fromRef(x_241, x_242);
x_244 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__34, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__34_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__34);
x_245 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__35));
lean_inc(x_240);
lean_inc(x_239);
x_246 = l_Lean_addMacroScope(x_239, x_245, x_240);
x_247 = lean_box(0);
x_248 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_248, 0, x_243);
lean_ctor_set(x_248, 1, x_244);
lean_ctor_set(x_248, 2, x_246);
lean_ctor_set(x_248, 3, x_247);
x_194 = x_248;
x_195 = x_4;
x_196 = x_5;
goto block_210;
}
block_175:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_174; 
lean_inc(x_9);
x_12 = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__1___redArg(x_9, x_9, x_6);
lean_dec(x_9);
lean_inc(x_2);
x_13 = l_Lean_Syntax_mkCApp(x_2, x_12);
x_14 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__13));
x_15 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__14));
lean_inc(x_2);
x_16 = l_Lean_Name_str___override(x_2, x_15);
x_17 = l_Lean_Name_append(x_14, x_16);
x_18 = 0;
x_19 = l_Lean_mkIdentFromRef___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__2(x_17, x_18, x_8, x_11);
x_20 = lean_ctor_get(x_19, 0);
x_21 = lean_ctor_get(x_19, 1);
x_174 = !lean_is_exclusive(x_19);
if (x_174 == 0)
{
x_22 = x_19;
x_23 = x_174;
goto block_173;
}
else
{
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_19);
x_22 = lean_box(0);
x_23 = x_174;
goto block_173;
}
block_173:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_24 = lean_ctor_get(x_8, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_8, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_8, 5);
x_27 = l_Lean_SourceInfo_fromRef(x_26, x_18);
x_28 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__17));
x_29 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__19));
x_30 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__10));
x_31 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__20, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__20_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__20);
lean_inc(x_27);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_32, 2, x_31);
lean_inc_ref_n(x_32, 7);
lean_inc(x_27);
x_33 = l_Lean_Syntax_node7(x_27, x_29, x_32, x_32, x_32, x_32, x_32, x_32, x_32);
x_34 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__22));
x_35 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__23));
lean_inc(x_27);
if (x_23 == 0)
{
lean_ctor_set_tag(x_22, 2);
lean_ctor_set(x_22, 1, x_35);
lean_ctor_set(x_22, 0, x_27);
x_36 = x_22;
goto block_171;
}
else
{
lean_object* x_172; 
x_172 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_172, 0, x_27);
lean_ctor_set(x_172, 1, x_35);
x_36 = x_172;
goto block_171;
}
block_171:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; uint8_t x_170; 
x_37 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__25));
x_38 = lean_mk_empty_array_with_capacity(x_7);
x_39 = lean_box(2);
x_40 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_30);
lean_ctor_set(x_40, 2, x_38);
x_41 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__27));
x_42 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__29));
x_43 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__30));
lean_inc(x_27);
x_44 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_44, 0, x_27);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__12, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__12_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__12);
x_46 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__13));
lean_inc(x_25);
lean_inc(x_24);
x_47 = l_Lean_addMacroScope(x_24, x_46, x_25);
x_48 = lean_box(0);
lean_inc(x_27);
x_49 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_49, 0, x_27);
lean_ctor_set(x_49, 1, x_45);
lean_ctor_set(x_49, 2, x_47);
lean_ctor_set(x_49, 3, x_48);
lean_inc(x_27);
x_50 = l_Lean_Syntax_node1(x_27, x_30, x_49);
x_51 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__31));
lean_inc(x_27);
x_52 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_52, 0, x_27);
lean_ctor_set(x_52, 1, x_51);
lean_inc(x_13);
lean_inc_ref(x_52);
lean_inc(x_27);
x_53 = l_Lean_Syntax_node2(x_27, x_30, x_52, x_13);
x_54 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__32));
lean_inc(x_27);
x_55 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_55, 0, x_27);
lean_ctor_set(x_55, 1, x_54);
lean_inc_ref(x_55);
lean_inc_ref(x_32);
lean_inc_ref(x_44);
lean_inc(x_27);
x_56 = l_Lean_Syntax_node5(x_27, x_42, x_44, x_50, x_53, x_32, x_55);
x_57 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__34, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__34_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__34);
x_58 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__35));
lean_inc(x_25);
lean_inc(x_24);
x_59 = l_Lean_addMacroScope(x_24, x_58, x_25);
lean_inc(x_27);
x_60 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_60, 0, x_27);
lean_ctor_set(x_60, 1, x_57);
lean_ctor_set(x_60, 2, x_59);
lean_ctor_set(x_60, 3, x_48);
lean_inc(x_27);
x_61 = l_Lean_Syntax_node1(x_27, x_30, x_60);
x_62 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__37, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__37_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__37);
x_63 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__38));
lean_inc(x_25);
lean_inc(x_24);
x_64 = l_Lean_addMacroScope(x_24, x_63, x_25);
x_65 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__45));
lean_inc(x_27);
x_66 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_66, 0, x_27);
lean_ctor_set(x_66, 1, x_62);
lean_ctor_set(x_66, 2, x_64);
lean_ctor_set(x_66, 3, x_65);
lean_inc_ref(x_52);
lean_inc(x_27);
x_67 = l_Lean_Syntax_node2(x_27, x_30, x_52, x_66);
x_68 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__47));
x_69 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__48));
lean_inc(x_27);
x_70 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_70, 0, x_27);
lean_ctor_set(x_70, 1, x_69);
x_71 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__50));
x_72 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__52));
x_73 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__53));
lean_inc(x_27);
x_74 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_74, 0, x_27);
lean_ctor_set(x_74, 1, x_73);
x_75 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__54));
lean_inc(x_27);
x_76 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_76, 0, x_27);
lean_ctor_set(x_76, 1, x_75);
lean_inc_ref(x_76);
lean_inc_ref(x_74);
lean_inc(x_27);
x_77 = l_Lean_Syntax_node2(x_27, x_72, x_74, x_76);
x_78 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__56));
x_79 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__58));
lean_inc_ref(x_32);
lean_inc(x_27);
x_80 = l_Lean_Syntax_node1(x_27, x_79, x_32);
x_81 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__60));
lean_inc_ref(x_32);
lean_inc(x_27);
x_82 = l_Lean_Syntax_node1(x_27, x_81, x_32);
lean_inc_ref_n(x_32, 2);
lean_inc(x_27);
x_83 = l_Lean_Syntax_node6(x_27, x_78, x_74, x_32, x_80, x_82, x_32, x_76);
lean_inc(x_27);
x_84 = l_Lean_Syntax_node2(x_27, x_71, x_77, x_83);
lean_inc_ref(x_70);
lean_inc(x_27);
x_85 = l_Lean_Syntax_node2(x_27, x_68, x_70, x_84);
lean_inc(x_27);
x_86 = l_Lean_Syntax_node1(x_27, x_30, x_85);
lean_inc_ref(x_55);
lean_inc_ref(x_44);
lean_inc(x_27);
x_87 = l_Lean_Syntax_node5(x_27, x_42, x_44, x_61, x_67, x_86, x_55);
lean_inc(x_27);
x_88 = l_Lean_Syntax_node2(x_27, x_30, x_56, x_87);
lean_inc_ref(x_32);
lean_inc(x_27);
x_89 = l_Lean_Syntax_node2(x_27, x_41, x_88, x_32);
x_90 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__62));
x_91 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__65));
lean_inc_ref_n(x_32, 2);
lean_inc(x_27);
x_92 = l_Lean_Syntax_node2(x_27, x_91, x_32, x_32);
x_93 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__66));
x_94 = l_Lean_Name_str___override(x_2, x_93);
x_95 = l_Lean_Name_append(x_14, x_94);
x_96 = l_Lean_mkIdentFromRef___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__2(x_95, x_18, x_8, x_21);
lean_dec_ref(x_8);
x_97 = lean_ctor_get(x_96, 0);
x_98 = lean_ctor_get(x_96, 1);
x_170 = !lean_is_exclusive(x_96);
if (x_170 == 0)
{
x_99 = x_96;
x_100 = x_170;
goto block_169;
}
else
{
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_96);
x_99 = lean_box(0);
x_100 = x_170;
goto block_169;
}
block_169:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_inc_ref(x_32);
lean_inc(x_92);
lean_inc_ref(x_70);
lean_inc(x_27);
x_101 = l_Lean_Syntax_node4(x_27, x_90, x_70, x_10, x_92, x_32);
x_102 = lean_unsigned_to_nat(2u);
x_103 = lean_mk_empty_array_with_capacity(x_102);
x_104 = lean_array_push(x_103, x_20);
x_105 = lean_array_push(x_104, x_40);
x_106 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_106, 0, x_39);
lean_ctor_set(x_106, 1, x_37);
lean_ctor_set(x_106, 2, x_105);
lean_inc_ref(x_32);
lean_inc(x_27);
x_107 = l_Lean_Syntax_node5(x_27, x_34, x_36, x_106, x_89, x_101, x_32);
lean_inc(x_33);
lean_inc(x_27);
x_108 = l_Lean_Syntax_node2(x_27, x_28, x_33, x_107);
x_109 = lean_array_push(x_1, x_108);
x_110 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__67));
x_111 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__68));
x_112 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__70));
lean_inc_ref(x_32);
lean_inc(x_27);
x_113 = l_Lean_Syntax_node1(x_27, x_112, x_32);
lean_inc(x_27);
x_114 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_114, 0, x_27);
lean_ctor_set(x_114, 1, x_110);
lean_inc_ref(x_32);
lean_inc(x_27);
x_115 = l_Lean_Syntax_node2(x_27, x_37, x_97, x_32);
lean_inc(x_27);
x_116 = l_Lean_Syntax_node1(x_27, x_30, x_115);
x_117 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__72));
x_118 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__74));
x_119 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__76));
x_120 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__78, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__78_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__78);
x_121 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__79));
lean_inc(x_25);
lean_inc(x_24);
x_122 = l_Lean_addMacroScope(x_24, x_121, x_25);
x_123 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__84));
lean_inc(x_27);
x_124 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_124, 0, x_27);
lean_ctor_set(x_124, 1, x_120);
lean_ctor_set(x_124, 2, x_122);
lean_ctor_set(x_124, 3, x_123);
lean_inc(x_27);
x_125 = l_Lean_Syntax_node1(x_27, x_30, x_13);
lean_inc(x_27);
x_126 = l_Lean_Syntax_node2(x_27, x_119, x_124, x_125);
lean_inc(x_27);
x_127 = l_Lean_Syntax_node2(x_27, x_118, x_52, x_126);
lean_inc_ref(x_32);
lean_inc(x_27);
x_128 = l_Lean_Syntax_node2(x_27, x_117, x_32, x_127);
x_129 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__86));
x_130 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__87));
lean_inc(x_27);
x_131 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_131, 0, x_27);
lean_ctor_set(x_131, 1, x_130);
x_132 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__89));
x_133 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__91));
x_134 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__93));
x_135 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__94, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__94_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__94);
x_136 = lean_box(0);
lean_inc(x_25);
lean_inc(x_24);
x_137 = l_Lean_addMacroScope(x_24, x_136, x_25);
x_138 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__107));
lean_inc(x_27);
x_139 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_139, 0, x_27);
lean_ctor_set(x_139, 1, x_135);
lean_ctor_set(x_139, 2, x_137);
lean_ctor_set(x_139, 3, x_138);
lean_inc(x_27);
x_140 = l_Lean_Syntax_node1(x_27, x_134, x_139);
lean_inc(x_140);
lean_inc(x_27);
x_141 = l_Lean_Syntax_node2(x_27, x_133, x_44, x_140);
x_142 = lean_obj_once(&l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__108, &l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__108_once, _init_l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__108);
x_143 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__109));
x_144 = l_Lean_addMacroScope(x_24, x_143, x_25);
x_145 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__112));
lean_inc(x_27);
x_146 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_146, 0, x_27);
lean_ctor_set(x_146, 1, x_142);
lean_ctor_set(x_146, 2, x_144);
lean_ctor_set(x_146, 3, x_145);
x_147 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__114));
x_148 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__116));
x_149 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__117));
lean_inc(x_27);
x_150 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_150, 0, x_27);
lean_ctor_set(x_150, 1, x_149);
lean_inc(x_27);
x_151 = l_Lean_Syntax_node2(x_27, x_148, x_150, x_140);
x_152 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__118));
lean_inc(x_27);
x_153 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_153, 0, x_27);
lean_ctor_set(x_153, 1, x_152);
lean_inc_ref(x_146);
lean_inc(x_27);
x_154 = l_Lean_Syntax_node3(x_27, x_147, x_151, x_153, x_146);
lean_inc(x_27);
x_155 = l_Lean_Syntax_node1(x_27, x_30, x_154);
lean_inc(x_27);
x_156 = l_Lean_Syntax_node2(x_27, x_119, x_146, x_155);
lean_inc(x_27);
x_157 = l_Lean_Syntax_node3(x_27, x_132, x_141, x_156, x_55);
lean_inc(x_27);
x_158 = l_Lean_Syntax_node1(x_27, x_30, x_157);
x_159 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___closed__119));
lean_inc(x_27);
x_160 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_160, 0, x_27);
lean_ctor_set(x_160, 1, x_159);
lean_inc(x_27);
x_161 = l_Lean_Syntax_node3(x_27, x_129, x_131, x_158, x_160);
lean_inc_ref(x_32);
lean_inc(x_27);
x_162 = l_Lean_Syntax_node4(x_27, x_90, x_70, x_161, x_92, x_32);
lean_inc(x_27);
x_163 = l_Lean_Syntax_node6(x_27, x_111, x_113, x_114, x_32, x_116, x_128, x_162);
x_164 = l_Lean_Syntax_node2(x_27, x_28, x_33, x_163);
x_165 = lean_array_push(x_109, x_164);
if (x_100 == 0)
{
lean_ctor_set(x_99, 0, x_165);
x_166 = x_99;
goto block_167;
}
else
{
lean_object* x_168; 
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_165);
lean_ctor_set(x_168, 1, x_98);
x_166 = x_168;
goto block_167;
}
block_167:
{
return x_166;
}
}
}
}
}
block_192:
{
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
lean_dec_ref(x_180);
x_6 = x_176;
x_7 = x_178;
x_8 = x_177;
x_9 = x_179;
x_10 = x_181;
x_11 = x_182;
goto block_175;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; uint8_t x_191; 
lean_dec(x_179);
lean_dec_ref(x_177);
lean_dec_ref(x_176);
lean_dec(x_2);
lean_dec_ref(x_1);
x_183 = lean_ctor_get(x_180, 0);
x_184 = lean_ctor_get(x_180, 1);
x_191 = !lean_is_exclusive(x_180);
if (x_191 == 0)
{
x_185 = x_180;
x_186 = x_191;
goto block_190;
}
else
{
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_180);
x_185 = lean_box(0);
x_186 = x_191;
goto block_190;
}
block_190:
{
lean_object* x_187; 
if (x_186 == 0)
{
x_187 = x_185;
goto block_188;
}
else
{
lean_object* x_189; 
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_183);
lean_ctor_set(x_189, 1, x_184);
x_187 = x_189;
goto block_188;
}
block_188:
{
return x_187;
}
}
}
}
block_210:
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; 
x_197 = lean_ctor_get(x_193, 0);
lean_inc_ref(x_197);
x_198 = lean_ctor_get(x_193, 2);
lean_inc(x_198);
x_199 = lean_mk_empty_array_with_capacity(x_198);
x_200 = lean_unsigned_to_nat(0u);
x_201 = lean_array_get_size(x_197);
x_202 = lean_nat_dec_lt(x_200, x_201);
if (x_202 == 0)
{
lean_dec_ref(x_197);
x_6 = x_199;
x_7 = x_200;
x_8 = x_195;
x_9 = x_198;
x_10 = x_194;
x_11 = x_196;
goto block_175;
}
else
{
uint8_t x_203; 
x_203 = lean_nat_dec_le(x_201, x_201);
if (x_203 == 0)
{
if (x_202 == 0)
{
lean_dec_ref(x_197);
x_6 = x_199;
x_7 = x_200;
x_8 = x_195;
x_9 = x_198;
x_10 = x_194;
x_11 = x_196;
goto block_175;
}
else
{
size_t x_204; size_t x_205; lean_object* x_206; 
x_204 = 0;
x_205 = lean_usize_of_nat(x_201);
lean_inc_ref(x_195);
x_206 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__3(x_3, x_197, x_204, x_205, x_194, x_195, x_196);
lean_dec_ref(x_197);
x_176 = x_199;
x_177 = x_195;
x_178 = x_200;
x_179 = x_198;
x_180 = x_206;
goto block_192;
}
}
else
{
size_t x_207; size_t x_208; lean_object* x_209; 
x_207 = 0;
x_208 = lean_usize_of_nat(x_201);
lean_inc_ref(x_195);
x_209 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__3(x_3, x_197, x_207, x_208, x_194, x_195, x_196);
lean_dec_ref(x_197);
x_176 = x_199;
x_177 = x_195;
x_178 = x_200;
x_179 = x_198;
x_180 = x_209;
goto block_192;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_commandGen__toml__encoders_x25___closed__11));
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_2);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__0));
x_9 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__2));
lean_inc_ref(x_2);
x_10 = l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0(x_8, x_9, x_8, x_2, x_3);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__4));
x_14 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__7));
lean_inc_ref(x_2);
x_15 = l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__1(x_11, x_13, x_14, x_2, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__9));
lean_inc_ref(x_2);
x_19 = l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__2(x_16, x_18, x_14, x_2, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__11));
lean_inc_ref(x_2);
x_23 = l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__3(x_20, x_22, x_8, x_2, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec_ref(x_23);
x_26 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__13));
lean_inc_ref(x_2);
x_27 = l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__4(x_24, x_26, x_8, x_2, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec_ref(x_27);
x_30 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__15));
lean_inc_ref(x_2);
x_31 = l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__5(x_28, x_30, x_8, x_2, x_29);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec_ref(x_31);
x_34 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1___closed__17));
x_35 = l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__6(x_32, x_34, x_8, x_2, x_33);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_47; 
x_36 = lean_ctor_get(x_35, 0);
x_37 = lean_ctor_get(x_35, 1);
x_47 = !lean_is_exclusive(x_35);
if (x_47 == 0)
{
x_38 = x_35;
x_39 = x_47;
goto block_46;
}
else
{
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_35);
x_38 = lean_box(0);
x_39 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_genToToml___lam__1___closed__10));
x_41 = lean_box(2);
x_42 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
lean_ctor_set(x_42, 2, x_36);
if (x_39 == 0)
{
lean_ctor_set(x_38, 0, x_42);
x_43 = x_38;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_37);
x_43 = x_45;
goto block_44;
}
block_44:
{
return x_43;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_56; 
x_48 = lean_ctor_get(x_35, 0);
x_49 = lean_ctor_get(x_35, 1);
x_56 = !lean_is_exclusive(x_35);
if (x_56 == 0)
{
x_50 = x_35;
x_51 = x_56;
goto block_55;
}
else
{
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_35);
x_50 = lean_box(0);
x_51 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_52; 
if (x_51 == 0)
{
x_52 = x_50;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_48);
lean_ctor_set(x_54, 1, x_49);
x_52 = x_54;
goto block_53;
}
block_53:
{
return x_52;
}
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_65; 
lean_dec_ref(x_2);
x_57 = lean_ctor_get(x_31, 0);
x_58 = lean_ctor_get(x_31, 1);
x_65 = !lean_is_exclusive(x_31);
if (x_65 == 0)
{
x_59 = x_31;
x_60 = x_65;
goto block_64;
}
else
{
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_31);
x_59 = lean_box(0);
x_60 = x_65;
goto block_64;
}
block_64:
{
lean_object* x_61; 
if (x_60 == 0)
{
x_61 = x_59;
goto block_62;
}
else
{
lean_object* x_63; 
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_57);
lean_ctor_set(x_63, 1, x_58);
x_61 = x_63;
goto block_62;
}
block_62:
{
return x_61;
}
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_74; 
lean_dec_ref(x_2);
x_66 = lean_ctor_get(x_27, 0);
x_67 = lean_ctor_get(x_27, 1);
x_74 = !lean_is_exclusive(x_27);
if (x_74 == 0)
{
x_68 = x_27;
x_69 = x_74;
goto block_73;
}
else
{
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_27);
x_68 = lean_box(0);
x_69 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_70; 
if (x_69 == 0)
{
x_70 = x_68;
goto block_71;
}
else
{
lean_object* x_72; 
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_66);
lean_ctor_set(x_72, 1, x_67);
x_70 = x_72;
goto block_71;
}
block_71:
{
return x_70;
}
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; uint8_t x_83; 
lean_dec_ref(x_2);
x_75 = lean_ctor_get(x_23, 0);
x_76 = lean_ctor_get(x_23, 1);
x_83 = !lean_is_exclusive(x_23);
if (x_83 == 0)
{
x_77 = x_23;
x_78 = x_83;
goto block_82;
}
else
{
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_23);
x_77 = lean_box(0);
x_78 = x_83;
goto block_82;
}
block_82:
{
lean_object* x_79; 
if (x_78 == 0)
{
x_79 = x_77;
goto block_80;
}
else
{
lean_object* x_81; 
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_75);
lean_ctor_set(x_81, 1, x_76);
x_79 = x_81;
goto block_80;
}
block_80:
{
return x_79;
}
}
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; uint8_t x_92; 
lean_dec_ref(x_2);
x_84 = lean_ctor_get(x_19, 0);
x_85 = lean_ctor_get(x_19, 1);
x_92 = !lean_is_exclusive(x_19);
if (x_92 == 0)
{
x_86 = x_19;
x_87 = x_92;
goto block_91;
}
else
{
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_19);
x_86 = lean_box(0);
x_87 = x_92;
goto block_91;
}
block_91:
{
lean_object* x_88; 
if (x_87 == 0)
{
x_88 = x_86;
goto block_89;
}
else
{
lean_object* x_90; 
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_84);
lean_ctor_set(x_90, 1, x_85);
x_88 = x_90;
goto block_89;
}
block_89:
{
return x_88;
}
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; uint8_t x_101; 
lean_dec_ref(x_2);
x_93 = lean_ctor_get(x_15, 0);
x_94 = lean_ctor_get(x_15, 1);
x_101 = !lean_is_exclusive(x_15);
if (x_101 == 0)
{
x_95 = x_15;
x_96 = x_101;
goto block_100;
}
else
{
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_15);
x_95 = lean_box(0);
x_96 = x_101;
goto block_100;
}
block_100:
{
lean_object* x_97; 
if (x_96 == 0)
{
x_97 = x_95;
goto block_98;
}
else
{
lean_object* x_99; 
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_93);
lean_ctor_set(x_99, 1, x_94);
x_97 = x_99;
goto block_98;
}
block_98:
{
return x_97;
}
}
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; uint8_t x_110; 
lean_dec_ref(x_2);
x_102 = lean_ctor_get(x_10, 0);
x_103 = lean_ctor_get(x_10, 1);
x_110 = !lean_is_exclusive(x_10);
if (x_110 == 0)
{
x_104 = x_10;
x_105 = x_110;
goto block_109;
}
else
{
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_10);
x_104 = lean_box(0);
x_105 = x_110;
goto block_109;
}
block_109:
{
lean_object* x_106; 
if (x_105 == 0)
{
x_106 = x_104;
goto block_107;
}
else
{
lean_object* x_108; 
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_102);
lean_ctor_set(x_108, 1, x_103);
x_106 = x_108;
goto block_107;
}
block_107:
{
return x_106;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__1___redArg(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_CLI_Translate_Toml_0__Lake_genToToml___at___00__private_Lake_CLI_Translate_Toml_0__Lake___aux__Lake__CLI__Translate__Toml______macroRules____private__Lake__CLI__Translate__Toml__0__Lake__commandGen__toml__encoders_x25__1_spec__0_spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 1)
{
lean_dec(x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_3, x_6);
lean_dec(x_3);
x_8 = lean_array_fget_borrowed(x_1, x_7);
x_9 = lean_array_fget_borrowed(x_2, x_7);
x_10 = lean_string_dec_eq(x_8, x_9);
if (x_10 == 0)
{
lean_dec(x_7);
return x_10;
}
else
{
x_3 = x_7;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__1___redArg(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lake_PartialBuildKey_toString(x_5);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_13 = lean_array_uset(x_7, x_2, x_10);
x_2 = x_12;
x_3 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lake_PartialBuildKey_toString(x_5);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_13 = lean_array_uset(x_7, x_2, x_10);
x_2 = x_12;
x_3 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_22; lean_object* x_23; lean_object* x_38; lean_object* x_39; lean_object* x_50; lean_object* x_51; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_78; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_100; lean_object* x_111; lean_object* x_112; lean_object* x_127; lean_object* x_128; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_154; lean_object* x_165; lean_object* x_166; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_190; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_212; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_234; lean_object* x_245; lean_object* x_246; lean_object* x_259; lean_object* x_260; uint8_t x_261; uint8_t x_262; uint8_t x_263; 
x_3 = l_Lake_LeanConfig_buildType___proj;
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 3);
lean_inc(x_5);
x_6 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__1));
x_22 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__3));
x_38 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__5));
x_50 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__7));
x_67 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__9));
x_89 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__11));
x_111 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__13));
x_127 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__15));
x_143 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__17));
x_165 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__19));
x_179 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__21));
x_201 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__23));
x_223 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__25));
x_245 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__27));
lean_inc_ref(x_1);
x_259 = lean_apply_1(x_4, x_1);
lean_inc_ref(x_1);
x_260 = lean_apply_1(x_5, x_1);
x_261 = lean_unbox(x_259);
x_262 = lean_unbox(x_260);
x_263 = l_Lake_instDecidableEqBuildType(x_261, x_262);
if (x_263 == 0)
{
lean_object* x_264; lean_object* x_265; uint8_t x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_264 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__29));
x_265 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_266 = lean_unbox(x_259);
x_267 = l_Lake_BuildType_toString(x_266);
x_268 = lean_box(0);
x_269 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_269, 0, x_268);
lean_ctor_set(x_269, 1, x_267);
x_270 = l_Lake_Toml_RBDict_insert___redArg(x_265, x_264, x_269, x_2);
x_246 = x_270;
goto block_258;
}
else
{
x_246 = x_2;
goto block_258;
}
block_21:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = l_Lake_LeanConfig_plugins___proj;
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_apply_1(x_9, x_1);
x_11 = lean_array_get_size(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_15 = lean_box(0);
x_16 = lean_array_size(x_10);
x_17 = 0;
x_18 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__0(x_16, x_17, x_10);
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lake_Toml_RBDict_insert___redArg(x_14, x_6, x_19, x_7);
return x_20;
}
else
{
lean_dec_ref(x_10);
return x_7;
}
}
block_37:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_24 = l_Lake_LeanConfig_dynlibs___proj;
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_inc_ref(x_1);
x_26 = lean_apply_1(x_25, x_1);
x_27 = lean_array_get_size(x_26);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_nat_dec_eq(x_27, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_31 = lean_box(0);
x_32 = lean_array_size(x_26);
x_33 = 0;
x_34 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__0(x_32, x_33, x_26);
x_35 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_35, 0, x_31);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lake_Toml_RBDict_insert___redArg(x_30, x_22, x_35, x_23);
x_7 = x_36;
goto block_21;
}
else
{
lean_dec_ref(x_26);
x_7 = x_23;
goto block_21;
}
}
block_49:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = l_Lake_LeanConfig_platformIndependent___proj;
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_inc_ref(x_1);
x_42 = lean_apply_1(x_41, x_1);
if (lean_obj_tag(x_42) == 0)
{
x_23 = x_39;
goto block_37;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec_ref(x_42);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(x_45, 0, x_44);
x_46 = lean_unbox(x_43);
lean_dec(x_43);
lean_ctor_set_uint8(x_45, sizeof(void*)*1, x_46);
x_47 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_48 = l_Lake_Toml_RBDict_insert___redArg(x_47, x_38, x_45, x_39);
x_23 = x_48;
goto block_37;
}
}
block_66:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; 
x_52 = l_Lake_LeanConfig_backend___proj;
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 3);
lean_inc(x_54);
lean_inc_ref(x_1);
x_55 = lean_apply_1(x_53, x_1);
lean_inc_ref(x_1);
x_56 = lean_apply_1(x_54, x_1);
x_57 = lean_unbox(x_55);
x_58 = lean_unbox(x_56);
x_59 = l_Lake_instDecidableEqBackend(x_57, x_58);
if (x_59 == 0)
{
lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_60 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_61 = lean_unbox(x_55);
x_62 = l_Lake_Backend_toString(x_61);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
x_65 = l_Lake_Toml_RBDict_insert___redArg(x_60, x_50, x_64, x_51);
x_39 = x_65;
goto block_49;
}
else
{
x_39 = x_51;
goto block_49;
}
}
block_77:
{
lean_object* x_70; lean_object* x_71; size_t x_72; size_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_70 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_71 = lean_box(0);
x_72 = lean_array_size(x_69);
x_73 = 0;
x_74 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_StrPatDescr_toToml_spec__0(x_72, x_73, x_69);
x_75 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_75, 0, x_71);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Lake_Toml_RBDict_insert___redArg(x_70, x_67, x_75, x_68);
x_51 = x_76;
goto block_66;
}
block_88:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_79 = l_Lake_LeanConfig_weakLinkArgs___proj;
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 3);
lean_inc(x_81);
lean_inc_ref(x_1);
x_82 = lean_apply_1(x_80, x_1);
lean_inc_ref(x_1);
x_83 = lean_apply_1(x_81, x_1);
x_84 = lean_array_get_size(x_82);
x_85 = lean_array_get_size(x_83);
x_86 = lean_nat_dec_eq(x_84, x_85);
if (x_86 == 0)
{
lean_dec_ref(x_83);
x_68 = x_78;
x_69 = x_82;
goto block_77;
}
else
{
uint8_t x_87; 
x_87 = l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__1___redArg(x_82, x_83, x_84);
lean_dec_ref(x_83);
if (x_87 == 0)
{
x_68 = x_78;
x_69 = x_82;
goto block_77;
}
else
{
lean_dec_ref(x_82);
x_51 = x_78;
goto block_66;
}
}
}
block_99:
{
lean_object* x_92; lean_object* x_93; size_t x_94; size_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_92 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_93 = lean_box(0);
x_94 = lean_array_size(x_91);
x_95 = 0;
x_96 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_StrPatDescr_toToml_spec__0(x_94, x_95, x_91);
x_97 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_97, 0, x_93);
lean_ctor_set(x_97, 1, x_96);
x_98 = l_Lake_Toml_RBDict_insert___redArg(x_92, x_89, x_97, x_90);
x_78 = x_98;
goto block_88;
}
block_110:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_101 = l_Lake_LeanConfig_moreLinkArgs___proj;
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 3);
lean_inc(x_103);
lean_inc_ref(x_1);
x_104 = lean_apply_1(x_102, x_1);
lean_inc_ref(x_1);
x_105 = lean_apply_1(x_103, x_1);
x_106 = lean_array_get_size(x_104);
x_107 = lean_array_get_size(x_105);
x_108 = lean_nat_dec_eq(x_106, x_107);
if (x_108 == 0)
{
lean_dec_ref(x_105);
x_90 = x_100;
x_91 = x_104;
goto block_99;
}
else
{
uint8_t x_109; 
x_109 = l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__1___redArg(x_104, x_105, x_106);
lean_dec_ref(x_105);
if (x_109 == 0)
{
x_90 = x_100;
x_91 = x_104;
goto block_99;
}
else
{
lean_dec_ref(x_104);
x_78 = x_100;
goto block_88;
}
}
}
block_126:
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_113 = l_Lake_LeanConfig_moreLinkLibs___proj;
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
lean_inc_ref(x_1);
x_115 = lean_apply_1(x_114, x_1);
x_116 = lean_array_get_size(x_115);
x_117 = lean_unsigned_to_nat(0u);
x_118 = lean_nat_dec_eq(x_116, x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; size_t x_121; size_t x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_119 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_120 = lean_box(0);
x_121 = lean_array_size(x_115);
x_122 = 0;
x_123 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__0(x_121, x_122, x_115);
x_124 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_124, 0, x_120);
lean_ctor_set(x_124, 1, x_123);
x_125 = l_Lake_Toml_RBDict_insert___redArg(x_119, x_111, x_124, x_112);
x_100 = x_125;
goto block_110;
}
else
{
lean_dec_ref(x_115);
x_100 = x_112;
goto block_110;
}
}
block_142:
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_129 = l_Lake_LeanConfig_moreLinkObjs___proj;
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
lean_inc_ref(x_1);
x_131 = lean_apply_1(x_130, x_1);
x_132 = lean_array_get_size(x_131);
x_133 = lean_unsigned_to_nat(0u);
x_134 = lean_nat_dec_eq(x_132, x_133);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; size_t x_137; size_t x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_135 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_136 = lean_box(0);
x_137 = lean_array_size(x_131);
x_138 = 0;
x_139 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__2(x_137, x_138, x_131);
x_140 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_140, 0, x_136);
lean_ctor_set(x_140, 1, x_139);
x_141 = l_Lake_Toml_RBDict_insert___redArg(x_135, x_127, x_140, x_128);
x_112 = x_141;
goto block_126;
}
else
{
lean_dec_ref(x_131);
x_112 = x_128;
goto block_126;
}
}
block_153:
{
lean_object* x_146; lean_object* x_147; size_t x_148; size_t x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_146 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_147 = lean_box(0);
x_148 = lean_array_size(x_145);
x_149 = 0;
x_150 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_StrPatDescr_toToml_spec__0(x_148, x_149, x_145);
x_151 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_151, 0, x_147);
lean_ctor_set(x_151, 1, x_150);
x_152 = l_Lake_Toml_RBDict_insert___redArg(x_146, x_143, x_151, x_144);
x_128 = x_152;
goto block_142;
}
block_164:
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_155 = l_Lake_LeanConfig_weakLeancArgs___proj;
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 3);
lean_inc(x_157);
lean_inc_ref(x_1);
x_158 = lean_apply_1(x_156, x_1);
lean_inc_ref(x_1);
x_159 = lean_apply_1(x_157, x_1);
x_160 = lean_array_get_size(x_158);
x_161 = lean_array_get_size(x_159);
x_162 = lean_nat_dec_eq(x_160, x_161);
if (x_162 == 0)
{
lean_dec_ref(x_159);
x_144 = x_154;
x_145 = x_158;
goto block_153;
}
else
{
uint8_t x_163; 
x_163 = l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__1___redArg(x_158, x_159, x_160);
lean_dec_ref(x_159);
if (x_163 == 0)
{
x_144 = x_154;
x_145 = x_158;
goto block_153;
}
else
{
lean_dec_ref(x_158);
x_128 = x_154;
goto block_142;
}
}
}
block_178:
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; 
x_167 = l_Lake_LeanConfig_moreServerOptions___proj;
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
lean_inc_ref(x_1);
x_169 = lean_apply_1(x_168, x_1);
x_170 = lean_array_get_size(x_169);
x_171 = lean_unsigned_to_nat(0u);
x_172 = lean_nat_dec_eq(x_170, x_171);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_173 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_174 = lean_box(0);
x_175 = l_Lake_Toml_encodeLeanOptions(x_169);
lean_dec_ref(x_169);
x_176 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
x_177 = l_Lake_Toml_RBDict_insert___redArg(x_173, x_165, x_176, x_166);
x_154 = x_177;
goto block_164;
}
else
{
lean_dec_ref(x_169);
x_154 = x_166;
goto block_164;
}
}
block_189:
{
lean_object* x_182; lean_object* x_183; size_t x_184; size_t x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_182 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_183 = lean_box(0);
x_184 = lean_array_size(x_180);
x_185 = 0;
x_186 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_StrPatDescr_toToml_spec__0(x_184, x_185, x_180);
x_187 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_187, 0, x_183);
lean_ctor_set(x_187, 1, x_186);
x_188 = l_Lake_Toml_RBDict_insert___redArg(x_182, x_179, x_187, x_181);
x_166 = x_188;
goto block_178;
}
block_200:
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; 
x_191 = l_Lake_LeanConfig_moreLeancArgs___proj;
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 3);
lean_inc(x_193);
lean_inc_ref(x_1);
x_194 = lean_apply_1(x_192, x_1);
lean_inc_ref(x_1);
x_195 = lean_apply_1(x_193, x_1);
x_196 = lean_array_get_size(x_194);
x_197 = lean_array_get_size(x_195);
x_198 = lean_nat_dec_eq(x_196, x_197);
if (x_198 == 0)
{
lean_dec_ref(x_195);
x_180 = x_194;
x_181 = x_190;
goto block_189;
}
else
{
uint8_t x_199; 
x_199 = l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__1___redArg(x_194, x_195, x_196);
lean_dec_ref(x_195);
if (x_199 == 0)
{
x_180 = x_194;
x_181 = x_190;
goto block_189;
}
else
{
lean_dec_ref(x_194);
x_166 = x_190;
goto block_178;
}
}
}
block_211:
{
lean_object* x_204; lean_object* x_205; size_t x_206; size_t x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_204 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_205 = lean_box(0);
x_206 = lean_array_size(x_202);
x_207 = 0;
x_208 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_StrPatDescr_toToml_spec__0(x_206, x_207, x_202);
x_209 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_209, 0, x_205);
lean_ctor_set(x_209, 1, x_208);
x_210 = l_Lake_Toml_RBDict_insert___redArg(x_204, x_201, x_209, x_203);
x_190 = x_210;
goto block_200;
}
block_222:
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; uint8_t x_220; 
x_213 = l_Lake_LeanConfig_weakLeanArgs___proj;
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_213, 3);
lean_inc(x_215);
lean_inc_ref(x_1);
x_216 = lean_apply_1(x_214, x_1);
lean_inc_ref(x_1);
x_217 = lean_apply_1(x_215, x_1);
x_218 = lean_array_get_size(x_216);
x_219 = lean_array_get_size(x_217);
x_220 = lean_nat_dec_eq(x_218, x_219);
if (x_220 == 0)
{
lean_dec_ref(x_217);
x_202 = x_216;
x_203 = x_212;
goto block_211;
}
else
{
uint8_t x_221; 
x_221 = l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__1___redArg(x_216, x_217, x_218);
lean_dec_ref(x_217);
if (x_221 == 0)
{
x_202 = x_216;
x_203 = x_212;
goto block_211;
}
else
{
lean_dec_ref(x_216);
x_190 = x_212;
goto block_200;
}
}
}
block_233:
{
lean_object* x_226; lean_object* x_227; size_t x_228; size_t x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_226 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_227 = lean_box(0);
x_228 = lean_array_size(x_225);
x_229 = 0;
x_230 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_StrPatDescr_toToml_spec__0(x_228, x_229, x_225);
x_231 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_231, 0, x_227);
lean_ctor_set(x_231, 1, x_230);
x_232 = l_Lake_Toml_RBDict_insert___redArg(x_226, x_223, x_231, x_224);
x_212 = x_232;
goto block_222;
}
block_244:
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; uint8_t x_242; 
x_235 = l_Lake_LeanConfig_moreLeanArgs___proj;
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_235, 3);
lean_inc(x_237);
lean_inc_ref(x_1);
x_238 = lean_apply_1(x_236, x_1);
lean_inc_ref(x_1);
x_239 = lean_apply_1(x_237, x_1);
x_240 = lean_array_get_size(x_238);
x_241 = lean_array_get_size(x_239);
x_242 = lean_nat_dec_eq(x_240, x_241);
if (x_242 == 0)
{
lean_dec_ref(x_239);
x_224 = x_234;
x_225 = x_238;
goto block_233;
}
else
{
uint8_t x_243; 
x_243 = l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__1___redArg(x_238, x_239, x_240);
lean_dec_ref(x_239);
if (x_243 == 0)
{
x_224 = x_234;
x_225 = x_238;
goto block_233;
}
else
{
lean_dec_ref(x_238);
x_212 = x_234;
goto block_222;
}
}
}
block_258:
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; 
x_247 = l_Lake_LeanConfig_leanOptions___proj;
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
lean_inc_ref(x_1);
x_249 = lean_apply_1(x_248, x_1);
x_250 = lean_array_get_size(x_249);
x_251 = lean_unsigned_to_nat(0u);
x_252 = lean_nat_dec_eq(x_250, x_251);
if (x_252 == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_253 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_254 = lean_box(0);
x_255 = l_Lake_Toml_encodeLeanOptions(x_249);
lean_dec_ref(x_249);
x_256 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_256, 0, x_254);
lean_ctor_set(x_256, 1, x_255);
x_257 = l_Lake_Toml_RBDict_insert___redArg(x_253, x_245, x_256, x_246);
x_234 = x_257;
goto block_244;
}
else
{
lean_dec_ref(x_249);
x_234 = x_246;
goto block_244;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__1___redArg(x_1, x_2, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_instToToml___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_box(0);
x_3 = lean_obj_once(&l_Lake_Toml_encodeLeanOptions___closed__0, &l_Lake_Toml_encodeLeanOptions___closed__0_once, _init_l_Lake_Toml_encodeLeanOptions___closed__0);
x_4 = l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml(x_1, x_3);
x_5 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_Name_toString(x_5, x_4);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_13 = lean_array_uset(x_7, x_2, x_10);
x_2 = x_12;
x_3 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml_spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 1)
{
lean_dec(x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_3, x_6);
lean_dec(x_3);
x_8 = lean_array_fget_borrowed(x_1, x_7);
x_9 = lean_array_fget_borrowed(x_2, x_7);
x_10 = lean_name_eq(x_8, x_9);
if (x_10 == 0)
{
lean_dec(x_7);
return x_10;
}
else
{
x_3 = x_7;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml_spec__0___redArg(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 1)
{
lean_dec(x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_3, x_6);
lean_dec(x_3);
x_8 = lean_array_fget_borrowed(x_1, x_7);
x_9 = lean_array_fget_borrowed(x_2, x_7);
x_10 = l_Lake_instDecidableEqGlob_decEq(x_8, x_9);
if (x_10 == 0)
{
lean_dec(x_7);
return x_10;
}
else
{
x_3 = x_7;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml_spec__4___redArg(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml_spec__3(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lake_Glob_toString(x_5);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_13 = lean_array_uset(x_7, x_2, x_10);
x_2 = x_12;
x_3 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml_spec__3(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml_spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lake_PartialBuildKey_toString(x_5);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_13 = lean_array_uset(x_7, x_2, x_10);
x_2 = x_12;
x_3 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml_spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_26; lean_object* x_27; lean_object* x_45; lean_object* x_46; lean_object* x_60; lean_object* x_61; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_91; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_116; lean_object* x_130; lean_object* x_131; lean_object* x_149; lean_object* x_150; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_179; lean_object* x_193; lean_object* x_194; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_221; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_246; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_271; lean_object* x_285; lean_object* x_286; lean_object* x_302; lean_object* x_303; lean_object* x_322; uint8_t x_323; lean_object* x_324; lean_object* x_330; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_349; lean_object* x_360; lean_object* x_361; uint8_t x_362; lean_object* x_368; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_391; lean_object* x_402; lean_object* x_403; lean_object* x_418; uint8_t x_419; lean_object* x_420; lean_object* x_426; lean_object* x_438; lean_object* x_439; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_462; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_484; lean_object* x_495; lean_object* x_496; uint8_t x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; uint8_t x_506; 
x_4 = l_Lake_LeanLibConfig_srcDir___proj(x_1);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 3);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__1));
x_26 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__3));
x_45 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__5));
x_60 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__7));
x_80 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__9));
x_105 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__11));
x_130 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__13));
x_149 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__15));
x_168 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__17));
x_193 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__19));
x_210 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__21));
x_235 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__23));
x_260 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__25));
x_285 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__27));
x_302 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__29));
x_322 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__1));
x_342 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__3));
x_360 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__5));
x_380 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__7));
x_402 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__9));
x_418 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__11));
x_438 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__13));
x_451 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__15));
x_473 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__17));
x_495 = ((lean_object*)(l_Lake_Dependency_toToml___closed__12));
x_496 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_497 = 1;
lean_inc(x_1);
x_498 = l_Lean_Name_toString(x_1, x_497);
x_499 = lean_box(0);
x_500 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_500, 0, x_499);
lean_ctor_set(x_500, 1, x_498);
x_501 = l_Lake_Toml_RBDict_insert___redArg(x_496, x_495, x_500, x_3);
lean_inc_ref(x_2);
x_502 = lean_apply_1(x_5, x_2);
lean_inc_ref(x_2);
x_503 = lean_apply_1(x_6, x_2);
lean_inc_ref(x_502);
x_504 = l_System_FilePath_normalize(x_502);
x_505 = l_System_FilePath_normalize(x_503);
x_506 = lean_string_dec_eq(x_504, x_505);
lean_dec_ref(x_505);
lean_dec_ref(x_504);
if (x_506 == 0)
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; 
x_507 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__19));
x_508 = l_Lake_mkRelPathString(x_502);
x_509 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_509, 0, x_499);
lean_ctor_set(x_509, 1, x_508);
x_510 = l_Lake_Toml_RBDict_insert___redArg(x_496, x_507, x_509, x_501);
x_484 = x_510;
goto block_494;
}
else
{
lean_dec_ref(x_502);
x_484 = x_501;
goto block_494;
}
block_25:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_9 = l_Lake_LeanConfig_plugins___proj;
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = l_Lake_LeanLibConfig_toLeanConfig___proj(x_1);
lean_dec(x_1);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = lean_apply_1(x_12, x_2);
x_14 = lean_apply_1(x_10, x_13);
x_15 = lean_array_get_size(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_19 = lean_box(0);
x_20 = lean_array_size(x_14);
x_21 = 0;
x_22 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__0(x_20, x_21, x_14);
x_23 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lake_Toml_RBDict_insert___redArg(x_18, x_7, x_23, x_8);
return x_24;
}
else
{
lean_dec_ref(x_14);
return x_8;
}
}
block_44:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_28 = l_Lake_LeanConfig_dynlibs___proj;
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = l_Lake_LeanLibConfig_toLeanConfig___proj(x_1);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
lean_inc_ref(x_2);
x_32 = lean_apply_1(x_31, x_2);
x_33 = lean_apply_1(x_29, x_32);
x_34 = lean_array_get_size(x_33);
x_35 = lean_unsigned_to_nat(0u);
x_36 = lean_nat_dec_eq(x_34, x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; size_t x_39; size_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_37 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_38 = lean_box(0);
x_39 = lean_array_size(x_33);
x_40 = 0;
x_41 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__0(x_39, x_40, x_33);
x_42 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lake_Toml_RBDict_insert___redArg(x_37, x_26, x_42, x_27);
x_8 = x_43;
goto block_25;
}
else
{
lean_dec_ref(x_33);
x_8 = x_27;
goto block_25;
}
}
block_59:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = l_Lake_LeanConfig_platformIndependent___proj;
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = l_Lake_LeanLibConfig_toLeanConfig___proj(x_1);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
lean_inc_ref(x_2);
x_51 = lean_apply_1(x_50, x_2);
x_52 = lean_apply_1(x_48, x_51);
if (lean_obj_tag(x_52) == 0)
{
x_27 = x_46;
goto block_44;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(x_55, 0, x_54);
x_56 = lean_unbox(x_53);
lean_dec(x_53);
lean_ctor_set_uint8(x_55, sizeof(void*)*1, x_56);
x_57 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_58 = l_Lake_Toml_RBDict_insert___redArg(x_57, x_45, x_55, x_46);
x_27 = x_58;
goto block_44;
}
}
block_79:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; 
x_62 = l_Lake_LeanConfig_backend___proj;
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 3);
lean_inc(x_64);
x_65 = l_Lake_LeanLibConfig_toLeanConfig___proj(x_1);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
lean_dec_ref(x_65);
lean_inc_ref(x_2);
x_67 = lean_apply_1(x_66, x_2);
lean_inc_ref(x_67);
x_68 = lean_apply_1(x_63, x_67);
x_69 = lean_apply_1(x_64, x_67);
x_70 = lean_unbox(x_68);
x_71 = lean_unbox(x_69);
x_72 = l_Lake_instDecidableEqBackend(x_70, x_71);
if (x_72 == 0)
{
lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_73 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_74 = lean_unbox(x_68);
x_75 = l_Lake_Backend_toString(x_74);
x_76 = lean_box(0);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = l_Lake_Toml_RBDict_insert___redArg(x_73, x_60, x_77, x_61);
x_46 = x_78;
goto block_59;
}
else
{
x_46 = x_61;
goto block_59;
}
}
block_90:
{
lean_object* x_83; lean_object* x_84; size_t x_85; size_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_83 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_84 = lean_box(0);
x_85 = lean_array_size(x_82);
x_86 = 0;
x_87 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_StrPatDescr_toToml_spec__0(x_85, x_86, x_82);
x_88 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_88, 0, x_84);
lean_ctor_set(x_88, 1, x_87);
x_89 = l_Lake_Toml_RBDict_insert___redArg(x_83, x_80, x_88, x_81);
x_61 = x_89;
goto block_79;
}
block_104:
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_92 = l_Lake_LeanConfig_weakLinkArgs___proj;
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 3);
lean_inc(x_94);
x_95 = l_Lake_LeanLibConfig_toLeanConfig___proj(x_1);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
lean_dec_ref(x_95);
lean_inc_ref(x_2);
x_97 = lean_apply_1(x_96, x_2);
lean_inc_ref(x_97);
x_98 = lean_apply_1(x_93, x_97);
x_99 = lean_apply_1(x_94, x_97);
x_100 = lean_array_get_size(x_98);
x_101 = lean_array_get_size(x_99);
x_102 = lean_nat_dec_eq(x_100, x_101);
if (x_102 == 0)
{
lean_dec_ref(x_99);
x_81 = x_91;
x_82 = x_98;
goto block_90;
}
else
{
uint8_t x_103; 
x_103 = l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__1___redArg(x_98, x_99, x_100);
lean_dec_ref(x_99);
if (x_103 == 0)
{
x_81 = x_91;
x_82 = x_98;
goto block_90;
}
else
{
lean_dec_ref(x_98);
x_61 = x_91;
goto block_79;
}
}
}
block_115:
{
lean_object* x_108; lean_object* x_109; size_t x_110; size_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_108 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_109 = lean_box(0);
x_110 = lean_array_size(x_107);
x_111 = 0;
x_112 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_StrPatDescr_toToml_spec__0(x_110, x_111, x_107);
x_113 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_113, 0, x_109);
lean_ctor_set(x_113, 1, x_112);
x_114 = l_Lake_Toml_RBDict_insert___redArg(x_108, x_105, x_113, x_106);
x_91 = x_114;
goto block_104;
}
block_129:
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_117 = l_Lake_LeanConfig_moreLinkArgs___proj;
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 3);
lean_inc(x_119);
x_120 = l_Lake_LeanLibConfig_toLeanConfig___proj(x_1);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
lean_dec_ref(x_120);
lean_inc_ref(x_2);
x_122 = lean_apply_1(x_121, x_2);
lean_inc_ref(x_122);
x_123 = lean_apply_1(x_118, x_122);
x_124 = lean_apply_1(x_119, x_122);
x_125 = lean_array_get_size(x_123);
x_126 = lean_array_get_size(x_124);
x_127 = lean_nat_dec_eq(x_125, x_126);
if (x_127 == 0)
{
lean_dec_ref(x_124);
x_106 = x_116;
x_107 = x_123;
goto block_115;
}
else
{
uint8_t x_128; 
x_128 = l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__1___redArg(x_123, x_124, x_125);
lean_dec_ref(x_124);
if (x_128 == 0)
{
x_106 = x_116;
x_107 = x_123;
goto block_115;
}
else
{
lean_dec_ref(x_123);
x_91 = x_116;
goto block_104;
}
}
}
block_148:
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_132 = l_Lake_LeanConfig_moreLinkLibs___proj;
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = l_Lake_LeanLibConfig_toLeanConfig___proj(x_1);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
lean_dec_ref(x_134);
lean_inc_ref(x_2);
x_136 = lean_apply_1(x_135, x_2);
x_137 = lean_apply_1(x_133, x_136);
x_138 = lean_array_get_size(x_137);
x_139 = lean_unsigned_to_nat(0u);
x_140 = lean_nat_dec_eq(x_138, x_139);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; size_t x_143; size_t x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_141 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_142 = lean_box(0);
x_143 = lean_array_size(x_137);
x_144 = 0;
x_145 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__0(x_143, x_144, x_137);
x_146 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_146, 0, x_142);
lean_ctor_set(x_146, 1, x_145);
x_147 = l_Lake_Toml_RBDict_insert___redArg(x_141, x_130, x_146, x_131);
x_116 = x_147;
goto block_129;
}
else
{
lean_dec_ref(x_137);
x_116 = x_131;
goto block_129;
}
}
block_167:
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_151 = l_Lake_LeanConfig_moreLinkObjs___proj;
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = l_Lake_LeanLibConfig_toLeanConfig___proj(x_1);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
lean_dec_ref(x_153);
lean_inc_ref(x_2);
x_155 = lean_apply_1(x_154, x_2);
x_156 = lean_apply_1(x_152, x_155);
x_157 = lean_array_get_size(x_156);
x_158 = lean_unsigned_to_nat(0u);
x_159 = lean_nat_dec_eq(x_157, x_158);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; size_t x_162; size_t x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_160 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_161 = lean_box(0);
x_162 = lean_array_size(x_156);
x_163 = 0;
x_164 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__2(x_162, x_163, x_156);
x_165 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_165, 0, x_161);
lean_ctor_set(x_165, 1, x_164);
x_166 = l_Lake_Toml_RBDict_insert___redArg(x_160, x_149, x_165, x_150);
x_131 = x_166;
goto block_148;
}
else
{
lean_dec_ref(x_156);
x_131 = x_150;
goto block_148;
}
}
block_178:
{
lean_object* x_171; lean_object* x_172; size_t x_173; size_t x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_171 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_172 = lean_box(0);
x_173 = lean_array_size(x_170);
x_174 = 0;
x_175 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_StrPatDescr_toToml_spec__0(x_173, x_174, x_170);
x_176 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_176, 0, x_172);
lean_ctor_set(x_176, 1, x_175);
x_177 = l_Lake_Toml_RBDict_insert___redArg(x_171, x_168, x_176, x_169);
x_150 = x_177;
goto block_167;
}
block_192:
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; 
x_180 = l_Lake_LeanConfig_weakLeancArgs___proj;
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 3);
lean_inc(x_182);
x_183 = l_Lake_LeanLibConfig_toLeanConfig___proj(x_1);
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
lean_dec_ref(x_183);
lean_inc_ref(x_2);
x_185 = lean_apply_1(x_184, x_2);
lean_inc_ref(x_185);
x_186 = lean_apply_1(x_181, x_185);
x_187 = lean_apply_1(x_182, x_185);
x_188 = lean_array_get_size(x_186);
x_189 = lean_array_get_size(x_187);
x_190 = lean_nat_dec_eq(x_188, x_189);
if (x_190 == 0)
{
lean_dec_ref(x_187);
x_169 = x_179;
x_170 = x_186;
goto block_178;
}
else
{
uint8_t x_191; 
x_191 = l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__1___redArg(x_186, x_187, x_188);
lean_dec_ref(x_187);
if (x_191 == 0)
{
x_169 = x_179;
x_170 = x_186;
goto block_178;
}
else
{
lean_dec_ref(x_186);
x_150 = x_179;
goto block_167;
}
}
}
block_209:
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; 
x_195 = l_Lake_LeanConfig_moreServerOptions___proj;
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = l_Lake_LeanLibConfig_toLeanConfig___proj(x_1);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
lean_dec_ref(x_197);
lean_inc_ref(x_2);
x_199 = lean_apply_1(x_198, x_2);
x_200 = lean_apply_1(x_196, x_199);
x_201 = lean_array_get_size(x_200);
x_202 = lean_unsigned_to_nat(0u);
x_203 = lean_nat_dec_eq(x_201, x_202);
if (x_203 == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_204 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_205 = lean_box(0);
x_206 = l_Lake_Toml_encodeLeanOptions(x_200);
lean_dec_ref(x_200);
x_207 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
x_208 = l_Lake_Toml_RBDict_insert___redArg(x_204, x_193, x_207, x_194);
x_179 = x_208;
goto block_192;
}
else
{
lean_dec_ref(x_200);
x_179 = x_194;
goto block_192;
}
}
block_220:
{
lean_object* x_213; lean_object* x_214; size_t x_215; size_t x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_213 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_214 = lean_box(0);
x_215 = lean_array_size(x_212);
x_216 = 0;
x_217 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_StrPatDescr_toToml_spec__0(x_215, x_216, x_212);
x_218 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_218, 0, x_214);
lean_ctor_set(x_218, 1, x_217);
x_219 = l_Lake_Toml_RBDict_insert___redArg(x_213, x_210, x_218, x_211);
x_194 = x_219;
goto block_209;
}
block_234:
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; 
x_222 = l_Lake_LeanConfig_moreLeancArgs___proj;
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_222, 3);
lean_inc(x_224);
x_225 = l_Lake_LeanLibConfig_toLeanConfig___proj(x_1);
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
lean_dec_ref(x_225);
lean_inc_ref(x_2);
x_227 = lean_apply_1(x_226, x_2);
lean_inc_ref(x_227);
x_228 = lean_apply_1(x_223, x_227);
x_229 = lean_apply_1(x_224, x_227);
x_230 = lean_array_get_size(x_228);
x_231 = lean_array_get_size(x_229);
x_232 = lean_nat_dec_eq(x_230, x_231);
if (x_232 == 0)
{
lean_dec_ref(x_229);
x_211 = x_221;
x_212 = x_228;
goto block_220;
}
else
{
uint8_t x_233; 
x_233 = l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__1___redArg(x_228, x_229, x_230);
lean_dec_ref(x_229);
if (x_233 == 0)
{
x_211 = x_221;
x_212 = x_228;
goto block_220;
}
else
{
lean_dec_ref(x_228);
x_194 = x_221;
goto block_209;
}
}
}
block_245:
{
lean_object* x_238; lean_object* x_239; size_t x_240; size_t x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_238 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_239 = lean_box(0);
x_240 = lean_array_size(x_236);
x_241 = 0;
x_242 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_StrPatDescr_toToml_spec__0(x_240, x_241, x_236);
x_243 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_243, 0, x_239);
lean_ctor_set(x_243, 1, x_242);
x_244 = l_Lake_Toml_RBDict_insert___redArg(x_238, x_235, x_243, x_237);
x_221 = x_244;
goto block_234;
}
block_259:
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; 
x_247 = l_Lake_LeanConfig_weakLeanArgs___proj;
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_247, 3);
lean_inc(x_249);
x_250 = l_Lake_LeanLibConfig_toLeanConfig___proj(x_1);
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
lean_dec_ref(x_250);
lean_inc_ref(x_2);
x_252 = lean_apply_1(x_251, x_2);
lean_inc_ref(x_252);
x_253 = lean_apply_1(x_248, x_252);
x_254 = lean_apply_1(x_249, x_252);
x_255 = lean_array_get_size(x_253);
x_256 = lean_array_get_size(x_254);
x_257 = lean_nat_dec_eq(x_255, x_256);
if (x_257 == 0)
{
lean_dec_ref(x_254);
x_236 = x_253;
x_237 = x_246;
goto block_245;
}
else
{
uint8_t x_258; 
x_258 = l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__1___redArg(x_253, x_254, x_255);
lean_dec_ref(x_254);
if (x_258 == 0)
{
x_236 = x_253;
x_237 = x_246;
goto block_245;
}
else
{
lean_dec_ref(x_253);
x_221 = x_246;
goto block_234;
}
}
}
block_270:
{
lean_object* x_263; lean_object* x_264; size_t x_265; size_t x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_263 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_264 = lean_box(0);
x_265 = lean_array_size(x_262);
x_266 = 0;
x_267 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_StrPatDescr_toToml_spec__0(x_265, x_266, x_262);
x_268 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_268, 0, x_264);
lean_ctor_set(x_268, 1, x_267);
x_269 = l_Lake_Toml_RBDict_insert___redArg(x_263, x_260, x_268, x_261);
x_246 = x_269;
goto block_259;
}
block_284:
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; uint8_t x_282; 
x_272 = l_Lake_LeanConfig_moreLeanArgs___proj;
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_272, 3);
lean_inc(x_274);
x_275 = l_Lake_LeanLibConfig_toLeanConfig___proj(x_1);
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
lean_dec_ref(x_275);
lean_inc_ref(x_2);
x_277 = lean_apply_1(x_276, x_2);
lean_inc_ref(x_277);
x_278 = lean_apply_1(x_273, x_277);
x_279 = lean_apply_1(x_274, x_277);
x_280 = lean_array_get_size(x_278);
x_281 = lean_array_get_size(x_279);
x_282 = lean_nat_dec_eq(x_280, x_281);
if (x_282 == 0)
{
lean_dec_ref(x_279);
x_261 = x_271;
x_262 = x_278;
goto block_270;
}
else
{
uint8_t x_283; 
x_283 = l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__1___redArg(x_278, x_279, x_280);
lean_dec_ref(x_279);
if (x_283 == 0)
{
x_261 = x_271;
x_262 = x_278;
goto block_270;
}
else
{
lean_dec_ref(x_278);
x_246 = x_271;
goto block_259;
}
}
}
block_301:
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; uint8_t x_295; 
x_287 = l_Lake_LeanConfig_leanOptions___proj;
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_288);
x_289 = l_Lake_LeanLibConfig_toLeanConfig___proj(x_1);
x_290 = lean_ctor_get(x_289, 0);
lean_inc(x_290);
lean_dec_ref(x_289);
lean_inc_ref(x_2);
x_291 = lean_apply_1(x_290, x_2);
x_292 = lean_apply_1(x_288, x_291);
x_293 = lean_array_get_size(x_292);
x_294 = lean_unsigned_to_nat(0u);
x_295 = lean_nat_dec_eq(x_293, x_294);
if (x_295 == 0)
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_296 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_297 = lean_box(0);
x_298 = l_Lake_Toml_encodeLeanOptions(x_292);
lean_dec_ref(x_292);
x_299 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_299, 0, x_297);
lean_ctor_set(x_299, 1, x_298);
x_300 = l_Lake_Toml_RBDict_insert___redArg(x_296, x_285, x_299, x_286);
x_271 = x_300;
goto block_284;
}
else
{
lean_dec_ref(x_292);
x_271 = x_286;
goto block_284;
}
}
block_321:
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; uint8_t x_312; uint8_t x_313; uint8_t x_314; 
x_304 = l_Lake_LeanConfig_buildType___proj;
x_305 = lean_ctor_get(x_304, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_304, 3);
lean_inc(x_306);
x_307 = l_Lake_LeanLibConfig_toLeanConfig___proj(x_1);
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
lean_dec_ref(x_307);
lean_inc_ref(x_2);
x_309 = lean_apply_1(x_308, x_2);
lean_inc_ref(x_309);
x_310 = lean_apply_1(x_305, x_309);
x_311 = lean_apply_1(x_306, x_309);
x_312 = lean_unbox(x_310);
x_313 = lean_unbox(x_311);
x_314 = l_Lake_instDecidableEqBuildType(x_312, x_313);
if (x_314 == 0)
{
lean_object* x_315; uint8_t x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_315 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_316 = lean_unbox(x_310);
x_317 = l_Lake_BuildType_toString(x_316);
x_318 = lean_box(0);
x_319 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_319, 0, x_318);
lean_ctor_set(x_319, 1, x_317);
x_320 = l_Lake_Toml_RBDict_insert___redArg(x_315, x_302, x_319, x_303);
x_286 = x_320;
goto block_301;
}
else
{
x_286 = x_303;
goto block_301;
}
}
block_329:
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_325 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_326 = lean_box(0);
x_327 = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(x_327, 0, x_326);
lean_ctor_set_uint8(x_327, sizeof(void*)*1, x_323);
x_328 = l_Lake_Toml_RBDict_insert___redArg(x_325, x_322, x_327, x_324);
x_303 = x_328;
goto block_321;
}
block_341:
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; uint8_t x_336; 
x_331 = l_Lake_LeanLibConfig_allowImportAll___proj(x_1);
x_332 = lean_ctor_get(x_331, 0);
lean_inc(x_332);
x_333 = lean_ctor_get(x_331, 3);
lean_inc(x_333);
lean_dec_ref(x_331);
lean_inc_ref(x_2);
x_334 = lean_apply_1(x_332, x_2);
lean_inc_ref(x_2);
x_335 = lean_apply_1(x_333, x_2);
x_336 = lean_unbox(x_334);
if (x_336 == 0)
{
uint8_t x_337; 
x_337 = lean_unbox(x_335);
if (x_337 == 0)
{
x_303 = x_330;
goto block_321;
}
else
{
uint8_t x_338; 
x_338 = lean_unbox(x_334);
x_323 = x_338;
x_324 = x_330;
goto block_329;
}
}
else
{
uint8_t x_339; 
x_339 = lean_unbox(x_335);
if (x_339 == 0)
{
uint8_t x_340; 
x_340 = lean_unbox(x_334);
x_323 = x_340;
x_324 = x_330;
goto block_329;
}
else
{
x_303 = x_330;
goto block_321;
}
}
}
block_348:
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_345 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_346 = l_Lake_encodeFacets(x_344);
x_347 = l_Lake_Toml_RBDict_insert___redArg(x_345, x_342, x_346, x_343);
x_330 = x_347;
goto block_341;
}
block_359:
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; uint8_t x_357; 
x_350 = l_Lake_LeanLibConfig_defaultFacets___proj(x_1);
x_351 = lean_ctor_get(x_350, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_350, 3);
lean_inc(x_352);
lean_dec_ref(x_350);
lean_inc_ref(x_2);
x_353 = lean_apply_1(x_351, x_2);
lean_inc_ref(x_2);
x_354 = lean_apply_1(x_352, x_2);
x_355 = lean_array_get_size(x_353);
x_356 = lean_array_get_size(x_354);
x_357 = lean_nat_dec_eq(x_355, x_356);
if (x_357 == 0)
{
lean_dec_ref(x_354);
x_343 = x_349;
x_344 = x_353;
goto block_348;
}
else
{
uint8_t x_358; 
x_358 = l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml_spec__0___redArg(x_353, x_354, x_355);
lean_dec_ref(x_354);
if (x_358 == 0)
{
x_343 = x_349;
x_344 = x_353;
goto block_348;
}
else
{
lean_dec_ref(x_353);
x_330 = x_349;
goto block_341;
}
}
}
block_367:
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_363 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_364 = lean_box(0);
x_365 = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(x_365, 0, x_364);
lean_ctor_set_uint8(x_365, sizeof(void*)*1, x_362);
x_366 = l_Lake_Toml_RBDict_insert___redArg(x_363, x_360, x_365, x_361);
x_349 = x_366;
goto block_359;
}
block_379:
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; uint8_t x_374; 
x_369 = l_Lake_LeanLibConfig_precompileModules___proj(x_1);
x_370 = lean_ctor_get(x_369, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_369, 3);
lean_inc(x_371);
lean_dec_ref(x_369);
lean_inc_ref(x_2);
x_372 = lean_apply_1(x_370, x_2);
lean_inc_ref(x_2);
x_373 = lean_apply_1(x_371, x_2);
x_374 = lean_unbox(x_372);
if (x_374 == 0)
{
uint8_t x_375; 
x_375 = lean_unbox(x_373);
if (x_375 == 0)
{
x_349 = x_368;
goto block_359;
}
else
{
uint8_t x_376; 
x_376 = lean_unbox(x_372);
x_361 = x_368;
x_362 = x_376;
goto block_367;
}
}
else
{
uint8_t x_377; 
x_377 = lean_unbox(x_373);
if (x_377 == 0)
{
uint8_t x_378; 
x_378 = lean_unbox(x_372);
x_361 = x_368;
x_362 = x_378;
goto block_367;
}
else
{
x_349 = x_368;
goto block_359;
}
}
}
block_390:
{
lean_object* x_383; lean_object* x_384; size_t x_385; size_t x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_383 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_384 = lean_box(0);
x_385 = lean_array_size(x_382);
x_386 = 0;
x_387 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml_spec__1(x_385, x_386, x_382);
x_388 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_388, 0, x_384);
lean_ctor_set(x_388, 1, x_387);
x_389 = l_Lake_Toml_RBDict_insert___redArg(x_383, x_380, x_388, x_381);
x_368 = x_389;
goto block_379;
}
block_401:
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; uint8_t x_399; 
x_392 = l_Lake_LeanLibConfig_extraDepTargets___proj(x_1);
x_393 = lean_ctor_get(x_392, 0);
lean_inc(x_393);
x_394 = lean_ctor_get(x_392, 3);
lean_inc(x_394);
lean_dec_ref(x_392);
lean_inc_ref(x_2);
x_395 = lean_apply_1(x_393, x_2);
lean_inc_ref(x_2);
x_396 = lean_apply_1(x_394, x_2);
x_397 = lean_array_get_size(x_395);
x_398 = lean_array_get_size(x_396);
x_399 = lean_nat_dec_eq(x_397, x_398);
if (x_399 == 0)
{
lean_dec_ref(x_396);
x_381 = x_391;
x_382 = x_395;
goto block_390;
}
else
{
uint8_t x_400; 
x_400 = l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml_spec__0___redArg(x_395, x_396, x_397);
lean_dec_ref(x_396);
if (x_400 == 0)
{
x_381 = x_391;
x_382 = x_395;
goto block_390;
}
else
{
lean_dec_ref(x_395);
x_368 = x_391;
goto block_379;
}
}
}
block_417:
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; uint8_t x_409; 
x_404 = l_Lake_LeanLibConfig_needs___proj(x_1);
x_405 = lean_ctor_get(x_404, 0);
lean_inc(x_405);
lean_dec_ref(x_404);
lean_inc_ref(x_2);
x_406 = lean_apply_1(x_405, x_2);
x_407 = lean_array_get_size(x_406);
x_408 = lean_unsigned_to_nat(0u);
x_409 = lean_nat_dec_eq(x_407, x_408);
if (x_409 == 0)
{
lean_object* x_410; lean_object* x_411; size_t x_412; size_t x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_410 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_411 = lean_box(0);
x_412 = lean_array_size(x_406);
x_413 = 0;
x_414 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml_spec__2(x_412, x_413, x_406);
x_415 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_415, 0, x_411);
lean_ctor_set(x_415, 1, x_414);
x_416 = l_Lake_Toml_RBDict_insert___redArg(x_410, x_402, x_415, x_403);
x_391 = x_416;
goto block_401;
}
else
{
lean_dec_ref(x_406);
x_391 = x_403;
goto block_401;
}
}
block_425:
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; 
x_421 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_422 = lean_box(0);
x_423 = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(x_423, 0, x_422);
lean_ctor_set_uint8(x_423, sizeof(void*)*1, x_419);
x_424 = l_Lake_Toml_RBDict_insert___redArg(x_421, x_418, x_423, x_420);
x_403 = x_424;
goto block_417;
}
block_437:
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; uint8_t x_432; 
x_427 = l_Lake_LeanLibConfig_libPrefixOnWindows___proj(x_1);
x_428 = lean_ctor_get(x_427, 0);
lean_inc(x_428);
x_429 = lean_ctor_get(x_427, 3);
lean_inc(x_429);
lean_dec_ref(x_427);
lean_inc_ref(x_2);
x_430 = lean_apply_1(x_428, x_2);
lean_inc_ref(x_2);
x_431 = lean_apply_1(x_429, x_2);
x_432 = lean_unbox(x_430);
if (x_432 == 0)
{
uint8_t x_433; 
x_433 = lean_unbox(x_431);
if (x_433 == 0)
{
x_403 = x_426;
goto block_417;
}
else
{
uint8_t x_434; 
x_434 = lean_unbox(x_430);
x_419 = x_434;
x_420 = x_426;
goto block_425;
}
}
else
{
uint8_t x_435; 
x_435 = lean_unbox(x_431);
if (x_435 == 0)
{
uint8_t x_436; 
x_436 = lean_unbox(x_430);
x_419 = x_436;
x_420 = x_426;
goto block_425;
}
else
{
x_403 = x_426;
goto block_417;
}
}
}
block_450:
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; uint8_t x_445; 
x_440 = l_Lake_LeanLibConfig_libName___proj(x_1);
x_441 = lean_ctor_get(x_440, 0);
lean_inc(x_441);
x_442 = lean_ctor_get(x_440, 3);
lean_inc(x_442);
lean_dec_ref(x_440);
lean_inc_ref(x_2);
x_443 = lean_apply_1(x_441, x_2);
lean_inc_ref(x_2);
x_444 = lean_apply_1(x_442, x_2);
x_445 = lean_string_dec_eq(x_443, x_444);
lean_dec_ref(x_444);
if (x_445 == 0)
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; 
x_446 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_447 = lean_box(0);
x_448 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_448, 0, x_447);
lean_ctor_set(x_448, 1, x_443);
x_449 = l_Lake_Toml_RBDict_insert___redArg(x_446, x_438, x_448, x_439);
x_426 = x_449;
goto block_437;
}
else
{
lean_dec_ref(x_443);
x_426 = x_439;
goto block_437;
}
}
block_461:
{
lean_object* x_454; lean_object* x_455; size_t x_456; size_t x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; 
x_454 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_455 = lean_box(0);
x_456 = lean_array_size(x_452);
x_457 = 0;
x_458 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml_spec__3(x_456, x_457, x_452);
x_459 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_459, 0, x_455);
lean_ctor_set(x_459, 1, x_458);
x_460 = l_Lake_Toml_RBDict_insert___redArg(x_454, x_451, x_459, x_453);
x_439 = x_460;
goto block_450;
}
block_472:
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; uint8_t x_470; 
x_463 = l_Lake_LeanLibConfig_globs___proj(x_1);
x_464 = lean_ctor_get(x_463, 0);
lean_inc(x_464);
x_465 = lean_ctor_get(x_463, 3);
lean_inc(x_465);
lean_dec_ref(x_463);
lean_inc_ref(x_2);
x_466 = lean_apply_1(x_464, x_2);
lean_inc_ref(x_2);
x_467 = lean_apply_1(x_465, x_2);
x_468 = lean_array_get_size(x_466);
x_469 = lean_array_get_size(x_467);
x_470 = lean_nat_dec_eq(x_468, x_469);
if (x_470 == 0)
{
lean_dec_ref(x_467);
x_452 = x_466;
x_453 = x_462;
goto block_461;
}
else
{
uint8_t x_471; 
x_471 = l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml_spec__4___redArg(x_466, x_467, x_468);
lean_dec_ref(x_467);
if (x_471 == 0)
{
x_452 = x_466;
x_453 = x_462;
goto block_461;
}
else
{
lean_dec_ref(x_466);
x_439 = x_462;
goto block_450;
}
}
}
block_483:
{
lean_object* x_476; lean_object* x_477; size_t x_478; size_t x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; 
x_476 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_477 = lean_box(0);
x_478 = lean_array_size(x_474);
x_479 = 0;
x_480 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml_spec__1(x_478, x_479, x_474);
x_481 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_481, 0, x_477);
lean_ctor_set(x_481, 1, x_480);
x_482 = l_Lake_Toml_RBDict_insert___redArg(x_476, x_473, x_481, x_475);
x_462 = x_482;
goto block_472;
}
block_494:
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; uint8_t x_492; 
lean_inc(x_1);
x_485 = l_Lake_LeanLibConfig_roots___proj(x_1);
x_486 = lean_ctor_get(x_485, 0);
lean_inc(x_486);
x_487 = lean_ctor_get(x_485, 3);
lean_inc(x_487);
lean_dec_ref(x_485);
lean_inc_ref(x_2);
x_488 = lean_apply_1(x_486, x_2);
lean_inc_ref(x_2);
x_489 = lean_apply_1(x_487, x_2);
x_490 = lean_array_get_size(x_488);
x_491 = lean_array_get_size(x_489);
x_492 = lean_nat_dec_eq(x_490, x_491);
if (x_492 == 0)
{
lean_dec_ref(x_489);
x_474 = x_488;
x_475 = x_484;
goto block_483;
}
else
{
uint8_t x_493; 
x_493 = l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml_spec__0___redArg(x_488, x_489, x_490);
lean_dec_ref(x_489);
if (x_493 == 0)
{
x_474 = x_488;
x_475 = x_484;
goto block_483;
}
else
{
lean_dec_ref(x_488);
x_462 = x_484;
goto block_472;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml_spec__0___redArg(x_1, x_2, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml_spec__4___redArg(x_1, x_2, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml_spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_instToToml___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_box(0);
x_4 = lean_obj_once(&l_Lake_Toml_encodeLeanOptions___closed__0, &l_Lake_Toml_encodeLeanOptions___closed__0_once, _init_l_Lake_Toml_encodeLeanOptions___closed__0);
x_5 = l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml(x_1, x_2, x_4);
x_6 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_instToToml(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_instToToml___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanExeConfig_toToml(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_26; lean_object* x_27; lean_object* x_45; lean_object* x_46; lean_object* x_60; lean_object* x_61; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_91; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_116; lean_object* x_130; lean_object* x_131; lean_object* x_149; lean_object* x_150; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_179; lean_object* x_193; lean_object* x_194; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_221; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_246; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_271; lean_object* x_285; lean_object* x_286; lean_object* x_302; lean_object* x_303; lean_object* x_322; uint8_t x_323; lean_object* x_324; lean_object* x_330; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_353; lean_object* x_364; lean_object* x_365; lean_object* x_380; lean_object* x_381; lean_object* x_393; lean_object* x_394; lean_object* x_408; lean_object* x_409; uint8_t x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; uint8_t x_419; 
x_4 = l_Lake_LeanExeConfig_srcDir___proj(x_1);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 3);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__1));
x_26 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__3));
x_45 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__5));
x_60 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__7));
x_80 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__9));
x_105 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__11));
x_130 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__13));
x_149 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__15));
x_168 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__17));
x_193 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__19));
x_210 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__21));
x_235 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__23));
x_260 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__25));
x_285 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__27));
x_302 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__29));
x_322 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanExeConfig_toToml___closed__1));
x_342 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__7));
x_364 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__9));
x_380 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanExeConfig_toToml___closed__3));
x_393 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanExeConfig_toToml___closed__5));
x_408 = ((lean_object*)(l_Lake_Dependency_toToml___closed__12));
x_409 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_410 = 1;
lean_inc(x_1);
x_411 = l_Lean_Name_toString(x_1, x_410);
x_412 = lean_box(0);
x_413 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_413, 0, x_412);
lean_ctor_set(x_413, 1, x_411);
x_414 = l_Lake_Toml_RBDict_insert___redArg(x_409, x_408, x_413, x_3);
lean_inc_ref(x_2);
x_415 = lean_apply_1(x_5, x_2);
lean_inc_ref(x_2);
x_416 = lean_apply_1(x_6, x_2);
lean_inc_ref(x_415);
x_417 = l_System_FilePath_normalize(x_415);
x_418 = l_System_FilePath_normalize(x_416);
x_419 = lean_string_dec_eq(x_417, x_418);
lean_dec_ref(x_418);
lean_dec_ref(x_417);
if (x_419 == 0)
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; 
x_420 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__19));
x_421 = l_Lake_mkRelPathString(x_415);
x_422 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_422, 0, x_412);
lean_ctor_set(x_422, 1, x_421);
x_423 = l_Lake_Toml_RBDict_insert___redArg(x_409, x_420, x_422, x_414);
x_394 = x_423;
goto block_407;
}
else
{
lean_dec_ref(x_415);
x_394 = x_414;
goto block_407;
}
block_25:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_9 = l_Lake_LeanConfig_plugins___proj;
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = l_Lake_LeanExeConfig_toLeanConfig___proj(x_1);
lean_dec(x_1);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = lean_apply_1(x_12, x_2);
x_14 = lean_apply_1(x_10, x_13);
x_15 = lean_array_get_size(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_19 = lean_box(0);
x_20 = lean_array_size(x_14);
x_21 = 0;
x_22 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__0(x_20, x_21, x_14);
x_23 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lake_Toml_RBDict_insert___redArg(x_18, x_7, x_23, x_8);
return x_24;
}
else
{
lean_dec_ref(x_14);
return x_8;
}
}
block_44:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_28 = l_Lake_LeanConfig_dynlibs___proj;
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = l_Lake_LeanExeConfig_toLeanConfig___proj(x_1);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
lean_inc_ref(x_2);
x_32 = lean_apply_1(x_31, x_2);
x_33 = lean_apply_1(x_29, x_32);
x_34 = lean_array_get_size(x_33);
x_35 = lean_unsigned_to_nat(0u);
x_36 = lean_nat_dec_eq(x_34, x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; size_t x_39; size_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_37 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_38 = lean_box(0);
x_39 = lean_array_size(x_33);
x_40 = 0;
x_41 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__0(x_39, x_40, x_33);
x_42 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lake_Toml_RBDict_insert___redArg(x_37, x_26, x_42, x_27);
x_8 = x_43;
goto block_25;
}
else
{
lean_dec_ref(x_33);
x_8 = x_27;
goto block_25;
}
}
block_59:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = l_Lake_LeanConfig_platformIndependent___proj;
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = l_Lake_LeanExeConfig_toLeanConfig___proj(x_1);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
lean_inc_ref(x_2);
x_51 = lean_apply_1(x_50, x_2);
x_52 = lean_apply_1(x_48, x_51);
if (lean_obj_tag(x_52) == 0)
{
x_27 = x_46;
goto block_44;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(x_55, 0, x_54);
x_56 = lean_unbox(x_53);
lean_dec(x_53);
lean_ctor_set_uint8(x_55, sizeof(void*)*1, x_56);
x_57 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_58 = l_Lake_Toml_RBDict_insert___redArg(x_57, x_45, x_55, x_46);
x_27 = x_58;
goto block_44;
}
}
block_79:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; 
x_62 = l_Lake_LeanConfig_backend___proj;
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 3);
lean_inc(x_64);
x_65 = l_Lake_LeanExeConfig_toLeanConfig___proj(x_1);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
lean_dec_ref(x_65);
lean_inc_ref(x_2);
x_67 = lean_apply_1(x_66, x_2);
lean_inc_ref(x_67);
x_68 = lean_apply_1(x_63, x_67);
x_69 = lean_apply_1(x_64, x_67);
x_70 = lean_unbox(x_68);
x_71 = lean_unbox(x_69);
x_72 = l_Lake_instDecidableEqBackend(x_70, x_71);
if (x_72 == 0)
{
lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_73 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_74 = lean_unbox(x_68);
x_75 = l_Lake_Backend_toString(x_74);
x_76 = lean_box(0);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = l_Lake_Toml_RBDict_insert___redArg(x_73, x_60, x_77, x_61);
x_46 = x_78;
goto block_59;
}
else
{
x_46 = x_61;
goto block_59;
}
}
block_90:
{
lean_object* x_83; lean_object* x_84; size_t x_85; size_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_83 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_84 = lean_box(0);
x_85 = lean_array_size(x_81);
x_86 = 0;
x_87 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_StrPatDescr_toToml_spec__0(x_85, x_86, x_81);
x_88 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_88, 0, x_84);
lean_ctor_set(x_88, 1, x_87);
x_89 = l_Lake_Toml_RBDict_insert___redArg(x_83, x_80, x_88, x_82);
x_61 = x_89;
goto block_79;
}
block_104:
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_92 = l_Lake_LeanConfig_weakLinkArgs___proj;
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 3);
lean_inc(x_94);
x_95 = l_Lake_LeanExeConfig_toLeanConfig___proj(x_1);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
lean_dec_ref(x_95);
lean_inc_ref(x_2);
x_97 = lean_apply_1(x_96, x_2);
lean_inc_ref(x_97);
x_98 = lean_apply_1(x_93, x_97);
x_99 = lean_apply_1(x_94, x_97);
x_100 = lean_array_get_size(x_98);
x_101 = lean_array_get_size(x_99);
x_102 = lean_nat_dec_eq(x_100, x_101);
if (x_102 == 0)
{
lean_dec_ref(x_99);
x_81 = x_98;
x_82 = x_91;
goto block_90;
}
else
{
uint8_t x_103; 
x_103 = l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__1___redArg(x_98, x_99, x_100);
lean_dec_ref(x_99);
if (x_103 == 0)
{
x_81 = x_98;
x_82 = x_91;
goto block_90;
}
else
{
lean_dec_ref(x_98);
x_61 = x_91;
goto block_79;
}
}
}
block_115:
{
lean_object* x_108; lean_object* x_109; size_t x_110; size_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_108 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_109 = lean_box(0);
x_110 = lean_array_size(x_106);
x_111 = 0;
x_112 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_StrPatDescr_toToml_spec__0(x_110, x_111, x_106);
x_113 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_113, 0, x_109);
lean_ctor_set(x_113, 1, x_112);
x_114 = l_Lake_Toml_RBDict_insert___redArg(x_108, x_105, x_113, x_107);
x_91 = x_114;
goto block_104;
}
block_129:
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_117 = l_Lake_LeanConfig_moreLinkArgs___proj;
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 3);
lean_inc(x_119);
x_120 = l_Lake_LeanExeConfig_toLeanConfig___proj(x_1);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
lean_dec_ref(x_120);
lean_inc_ref(x_2);
x_122 = lean_apply_1(x_121, x_2);
lean_inc_ref(x_122);
x_123 = lean_apply_1(x_118, x_122);
x_124 = lean_apply_1(x_119, x_122);
x_125 = lean_array_get_size(x_123);
x_126 = lean_array_get_size(x_124);
x_127 = lean_nat_dec_eq(x_125, x_126);
if (x_127 == 0)
{
lean_dec_ref(x_124);
x_106 = x_123;
x_107 = x_116;
goto block_115;
}
else
{
uint8_t x_128; 
x_128 = l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__1___redArg(x_123, x_124, x_125);
lean_dec_ref(x_124);
if (x_128 == 0)
{
x_106 = x_123;
x_107 = x_116;
goto block_115;
}
else
{
lean_dec_ref(x_123);
x_91 = x_116;
goto block_104;
}
}
}
block_148:
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_132 = l_Lake_LeanConfig_moreLinkLibs___proj;
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = l_Lake_LeanExeConfig_toLeanConfig___proj(x_1);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
lean_dec_ref(x_134);
lean_inc_ref(x_2);
x_136 = lean_apply_1(x_135, x_2);
x_137 = lean_apply_1(x_133, x_136);
x_138 = lean_array_get_size(x_137);
x_139 = lean_unsigned_to_nat(0u);
x_140 = lean_nat_dec_eq(x_138, x_139);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; size_t x_143; size_t x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_141 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_142 = lean_box(0);
x_143 = lean_array_size(x_137);
x_144 = 0;
x_145 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__0(x_143, x_144, x_137);
x_146 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_146, 0, x_142);
lean_ctor_set(x_146, 1, x_145);
x_147 = l_Lake_Toml_RBDict_insert___redArg(x_141, x_130, x_146, x_131);
x_116 = x_147;
goto block_129;
}
else
{
lean_dec_ref(x_137);
x_116 = x_131;
goto block_129;
}
}
block_167:
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_151 = l_Lake_LeanConfig_moreLinkObjs___proj;
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = l_Lake_LeanExeConfig_toLeanConfig___proj(x_1);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
lean_dec_ref(x_153);
lean_inc_ref(x_2);
x_155 = lean_apply_1(x_154, x_2);
x_156 = lean_apply_1(x_152, x_155);
x_157 = lean_array_get_size(x_156);
x_158 = lean_unsigned_to_nat(0u);
x_159 = lean_nat_dec_eq(x_157, x_158);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; size_t x_162; size_t x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_160 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_161 = lean_box(0);
x_162 = lean_array_size(x_156);
x_163 = 0;
x_164 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__2(x_162, x_163, x_156);
x_165 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_165, 0, x_161);
lean_ctor_set(x_165, 1, x_164);
x_166 = l_Lake_Toml_RBDict_insert___redArg(x_160, x_149, x_165, x_150);
x_131 = x_166;
goto block_148;
}
else
{
lean_dec_ref(x_156);
x_131 = x_150;
goto block_148;
}
}
block_178:
{
lean_object* x_171; lean_object* x_172; size_t x_173; size_t x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_171 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_172 = lean_box(0);
x_173 = lean_array_size(x_169);
x_174 = 0;
x_175 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_StrPatDescr_toToml_spec__0(x_173, x_174, x_169);
x_176 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_176, 0, x_172);
lean_ctor_set(x_176, 1, x_175);
x_177 = l_Lake_Toml_RBDict_insert___redArg(x_171, x_168, x_176, x_170);
x_150 = x_177;
goto block_167;
}
block_192:
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; 
x_180 = l_Lake_LeanConfig_weakLeancArgs___proj;
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 3);
lean_inc(x_182);
x_183 = l_Lake_LeanExeConfig_toLeanConfig___proj(x_1);
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
lean_dec_ref(x_183);
lean_inc_ref(x_2);
x_185 = lean_apply_1(x_184, x_2);
lean_inc_ref(x_185);
x_186 = lean_apply_1(x_181, x_185);
x_187 = lean_apply_1(x_182, x_185);
x_188 = lean_array_get_size(x_186);
x_189 = lean_array_get_size(x_187);
x_190 = lean_nat_dec_eq(x_188, x_189);
if (x_190 == 0)
{
lean_dec_ref(x_187);
x_169 = x_186;
x_170 = x_179;
goto block_178;
}
else
{
uint8_t x_191; 
x_191 = l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__1___redArg(x_186, x_187, x_188);
lean_dec_ref(x_187);
if (x_191 == 0)
{
x_169 = x_186;
x_170 = x_179;
goto block_178;
}
else
{
lean_dec_ref(x_186);
x_150 = x_179;
goto block_167;
}
}
}
block_209:
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; 
x_195 = l_Lake_LeanConfig_moreServerOptions___proj;
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = l_Lake_LeanExeConfig_toLeanConfig___proj(x_1);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
lean_dec_ref(x_197);
lean_inc_ref(x_2);
x_199 = lean_apply_1(x_198, x_2);
x_200 = lean_apply_1(x_196, x_199);
x_201 = lean_array_get_size(x_200);
x_202 = lean_unsigned_to_nat(0u);
x_203 = lean_nat_dec_eq(x_201, x_202);
if (x_203 == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_204 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_205 = lean_box(0);
x_206 = l_Lake_Toml_encodeLeanOptions(x_200);
lean_dec_ref(x_200);
x_207 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
x_208 = l_Lake_Toml_RBDict_insert___redArg(x_204, x_193, x_207, x_194);
x_179 = x_208;
goto block_192;
}
else
{
lean_dec_ref(x_200);
x_179 = x_194;
goto block_192;
}
}
block_220:
{
lean_object* x_213; lean_object* x_214; size_t x_215; size_t x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_213 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_214 = lean_box(0);
x_215 = lean_array_size(x_211);
x_216 = 0;
x_217 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_StrPatDescr_toToml_spec__0(x_215, x_216, x_211);
x_218 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_218, 0, x_214);
lean_ctor_set(x_218, 1, x_217);
x_219 = l_Lake_Toml_RBDict_insert___redArg(x_213, x_210, x_218, x_212);
x_194 = x_219;
goto block_209;
}
block_234:
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; 
x_222 = l_Lake_LeanConfig_moreLeancArgs___proj;
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_222, 3);
lean_inc(x_224);
x_225 = l_Lake_LeanExeConfig_toLeanConfig___proj(x_1);
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
lean_dec_ref(x_225);
lean_inc_ref(x_2);
x_227 = lean_apply_1(x_226, x_2);
lean_inc_ref(x_227);
x_228 = lean_apply_1(x_223, x_227);
x_229 = lean_apply_1(x_224, x_227);
x_230 = lean_array_get_size(x_228);
x_231 = lean_array_get_size(x_229);
x_232 = lean_nat_dec_eq(x_230, x_231);
if (x_232 == 0)
{
lean_dec_ref(x_229);
x_211 = x_228;
x_212 = x_221;
goto block_220;
}
else
{
uint8_t x_233; 
x_233 = l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__1___redArg(x_228, x_229, x_230);
lean_dec_ref(x_229);
if (x_233 == 0)
{
x_211 = x_228;
x_212 = x_221;
goto block_220;
}
else
{
lean_dec_ref(x_228);
x_194 = x_221;
goto block_209;
}
}
}
block_245:
{
lean_object* x_238; lean_object* x_239; size_t x_240; size_t x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_238 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_239 = lean_box(0);
x_240 = lean_array_size(x_237);
x_241 = 0;
x_242 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_StrPatDescr_toToml_spec__0(x_240, x_241, x_237);
x_243 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_243, 0, x_239);
lean_ctor_set(x_243, 1, x_242);
x_244 = l_Lake_Toml_RBDict_insert___redArg(x_238, x_235, x_243, x_236);
x_221 = x_244;
goto block_234;
}
block_259:
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; 
x_247 = l_Lake_LeanConfig_weakLeanArgs___proj;
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_247, 3);
lean_inc(x_249);
x_250 = l_Lake_LeanExeConfig_toLeanConfig___proj(x_1);
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
lean_dec_ref(x_250);
lean_inc_ref(x_2);
x_252 = lean_apply_1(x_251, x_2);
lean_inc_ref(x_252);
x_253 = lean_apply_1(x_248, x_252);
x_254 = lean_apply_1(x_249, x_252);
x_255 = lean_array_get_size(x_253);
x_256 = lean_array_get_size(x_254);
x_257 = lean_nat_dec_eq(x_255, x_256);
if (x_257 == 0)
{
lean_dec_ref(x_254);
x_236 = x_246;
x_237 = x_253;
goto block_245;
}
else
{
uint8_t x_258; 
x_258 = l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__1___redArg(x_253, x_254, x_255);
lean_dec_ref(x_254);
if (x_258 == 0)
{
x_236 = x_246;
x_237 = x_253;
goto block_245;
}
else
{
lean_dec_ref(x_253);
x_221 = x_246;
goto block_234;
}
}
}
block_270:
{
lean_object* x_263; lean_object* x_264; size_t x_265; size_t x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_263 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_264 = lean_box(0);
x_265 = lean_array_size(x_261);
x_266 = 0;
x_267 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_StrPatDescr_toToml_spec__0(x_265, x_266, x_261);
x_268 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_268, 0, x_264);
lean_ctor_set(x_268, 1, x_267);
x_269 = l_Lake_Toml_RBDict_insert___redArg(x_263, x_260, x_268, x_262);
x_246 = x_269;
goto block_259;
}
block_284:
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; uint8_t x_282; 
x_272 = l_Lake_LeanConfig_moreLeanArgs___proj;
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_272, 3);
lean_inc(x_274);
x_275 = l_Lake_LeanExeConfig_toLeanConfig___proj(x_1);
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
lean_dec_ref(x_275);
lean_inc_ref(x_2);
x_277 = lean_apply_1(x_276, x_2);
lean_inc_ref(x_277);
x_278 = lean_apply_1(x_273, x_277);
x_279 = lean_apply_1(x_274, x_277);
x_280 = lean_array_get_size(x_278);
x_281 = lean_array_get_size(x_279);
x_282 = lean_nat_dec_eq(x_280, x_281);
if (x_282 == 0)
{
lean_dec_ref(x_279);
x_261 = x_278;
x_262 = x_271;
goto block_270;
}
else
{
uint8_t x_283; 
x_283 = l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__1___redArg(x_278, x_279, x_280);
lean_dec_ref(x_279);
if (x_283 == 0)
{
x_261 = x_278;
x_262 = x_271;
goto block_270;
}
else
{
lean_dec_ref(x_278);
x_246 = x_271;
goto block_259;
}
}
}
block_301:
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; uint8_t x_295; 
x_287 = l_Lake_LeanConfig_leanOptions___proj;
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_288);
x_289 = l_Lake_LeanExeConfig_toLeanConfig___proj(x_1);
x_290 = lean_ctor_get(x_289, 0);
lean_inc(x_290);
lean_dec_ref(x_289);
lean_inc_ref(x_2);
x_291 = lean_apply_1(x_290, x_2);
x_292 = lean_apply_1(x_288, x_291);
x_293 = lean_array_get_size(x_292);
x_294 = lean_unsigned_to_nat(0u);
x_295 = lean_nat_dec_eq(x_293, x_294);
if (x_295 == 0)
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_296 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_297 = lean_box(0);
x_298 = l_Lake_Toml_encodeLeanOptions(x_292);
lean_dec_ref(x_292);
x_299 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_299, 0, x_297);
lean_ctor_set(x_299, 1, x_298);
x_300 = l_Lake_Toml_RBDict_insert___redArg(x_296, x_285, x_299, x_286);
x_271 = x_300;
goto block_284;
}
else
{
lean_dec_ref(x_292);
x_271 = x_286;
goto block_284;
}
}
block_321:
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; uint8_t x_312; uint8_t x_313; uint8_t x_314; 
x_304 = l_Lake_LeanConfig_buildType___proj;
x_305 = lean_ctor_get(x_304, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_304, 3);
lean_inc(x_306);
x_307 = l_Lake_LeanExeConfig_toLeanConfig___proj(x_1);
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
lean_dec_ref(x_307);
lean_inc_ref(x_2);
x_309 = lean_apply_1(x_308, x_2);
lean_inc_ref(x_309);
x_310 = lean_apply_1(x_305, x_309);
x_311 = lean_apply_1(x_306, x_309);
x_312 = lean_unbox(x_310);
x_313 = lean_unbox(x_311);
x_314 = l_Lake_instDecidableEqBuildType(x_312, x_313);
if (x_314 == 0)
{
lean_object* x_315; uint8_t x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_315 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_316 = lean_unbox(x_310);
x_317 = l_Lake_BuildType_toString(x_316);
x_318 = lean_box(0);
x_319 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_319, 0, x_318);
lean_ctor_set(x_319, 1, x_317);
x_320 = l_Lake_Toml_RBDict_insert___redArg(x_315, x_302, x_319, x_303);
x_286 = x_320;
goto block_301;
}
else
{
x_286 = x_303;
goto block_301;
}
}
block_329:
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_325 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_326 = lean_box(0);
x_327 = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(x_327, 0, x_326);
lean_ctor_set_uint8(x_327, sizeof(void*)*1, x_323);
x_328 = l_Lake_Toml_RBDict_insert___redArg(x_325, x_322, x_327, x_324);
x_303 = x_328;
goto block_321;
}
block_341:
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; uint8_t x_336; 
x_331 = l_Lake_LeanExeConfig_supportInterpreter___proj(x_1);
x_332 = lean_ctor_get(x_331, 0);
lean_inc(x_332);
x_333 = lean_ctor_get(x_331, 3);
lean_inc(x_333);
lean_dec_ref(x_331);
lean_inc_ref(x_2);
x_334 = lean_apply_1(x_332, x_2);
lean_inc_ref(x_2);
x_335 = lean_apply_1(x_333, x_2);
x_336 = lean_unbox(x_334);
if (x_336 == 0)
{
uint8_t x_337; 
x_337 = lean_unbox(x_335);
if (x_337 == 0)
{
x_303 = x_330;
goto block_321;
}
else
{
uint8_t x_338; 
x_338 = lean_unbox(x_334);
x_323 = x_338;
x_324 = x_330;
goto block_329;
}
}
else
{
uint8_t x_339; 
x_339 = lean_unbox(x_335);
if (x_339 == 0)
{
uint8_t x_340; 
x_340 = lean_unbox(x_334);
x_323 = x_340;
x_324 = x_330;
goto block_329;
}
else
{
x_303 = x_330;
goto block_321;
}
}
}
block_352:
{
lean_object* x_345; lean_object* x_346; size_t x_347; size_t x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; 
x_345 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_346 = lean_box(0);
x_347 = lean_array_size(x_344);
x_348 = 0;
x_349 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml_spec__1(x_347, x_348, x_344);
x_350 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_350, 0, x_346);
lean_ctor_set(x_350, 1, x_349);
x_351 = l_Lake_Toml_RBDict_insert___redArg(x_345, x_342, x_350, x_343);
x_330 = x_351;
goto block_341;
}
block_363:
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; uint8_t x_361; 
x_354 = l_Lake_LeanExeConfig_extraDepTargets___proj(x_1);
x_355 = lean_ctor_get(x_354, 0);
lean_inc(x_355);
x_356 = lean_ctor_get(x_354, 3);
lean_inc(x_356);
lean_dec_ref(x_354);
lean_inc_ref(x_2);
x_357 = lean_apply_1(x_355, x_2);
lean_inc_ref(x_2);
x_358 = lean_apply_1(x_356, x_2);
x_359 = lean_array_get_size(x_357);
x_360 = lean_array_get_size(x_358);
x_361 = lean_nat_dec_eq(x_359, x_360);
if (x_361 == 0)
{
lean_dec_ref(x_358);
x_343 = x_353;
x_344 = x_357;
goto block_352;
}
else
{
uint8_t x_362; 
x_362 = l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml_spec__0___redArg(x_357, x_358, x_359);
lean_dec_ref(x_358);
if (x_362 == 0)
{
x_343 = x_353;
x_344 = x_357;
goto block_352;
}
else
{
lean_dec_ref(x_357);
x_330 = x_353;
goto block_341;
}
}
}
block_379:
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; uint8_t x_371; 
x_366 = l_Lake_LeanExeConfig_needs___proj(x_1);
x_367 = lean_ctor_get(x_366, 0);
lean_inc(x_367);
lean_dec_ref(x_366);
lean_inc_ref(x_2);
x_368 = lean_apply_1(x_367, x_2);
x_369 = lean_array_get_size(x_368);
x_370 = lean_unsigned_to_nat(0u);
x_371 = lean_nat_dec_eq(x_369, x_370);
if (x_371 == 0)
{
lean_object* x_372; lean_object* x_373; size_t x_374; size_t x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_372 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_373 = lean_box(0);
x_374 = lean_array_size(x_368);
x_375 = 0;
x_376 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml_spec__2(x_374, x_375, x_368);
x_377 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_377, 0, x_373);
lean_ctor_set(x_377, 1, x_376);
x_378 = l_Lake_Toml_RBDict_insert___redArg(x_372, x_364, x_377, x_365);
x_353 = x_378;
goto block_363;
}
else
{
lean_dec_ref(x_368);
x_353 = x_365;
goto block_363;
}
}
block_392:
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; uint8_t x_387; 
lean_inc(x_1);
x_382 = l_Lake_LeanExeConfig_exeName___proj(x_1);
x_383 = lean_ctor_get(x_382, 0);
lean_inc(x_383);
x_384 = lean_ctor_get(x_382, 3);
lean_inc(x_384);
lean_dec_ref(x_382);
lean_inc_ref(x_2);
x_385 = lean_apply_1(x_383, x_2);
lean_inc_ref(x_2);
x_386 = lean_apply_1(x_384, x_2);
x_387 = lean_string_dec_eq(x_385, x_386);
lean_dec_ref(x_386);
if (x_387 == 0)
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_388 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_389 = lean_box(0);
x_390 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_390, 0, x_389);
lean_ctor_set(x_390, 1, x_385);
x_391 = l_Lake_Toml_RBDict_insert___redArg(x_388, x_380, x_390, x_381);
x_365 = x_391;
goto block_379;
}
else
{
lean_dec_ref(x_385);
x_365 = x_381;
goto block_379;
}
}
block_407:
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; uint8_t x_400; 
lean_inc(x_1);
x_395 = l_Lake_LeanExeConfig_root___proj(x_1);
x_396 = lean_ctor_get(x_395, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_395, 3);
lean_inc(x_397);
lean_dec_ref(x_395);
lean_inc_ref(x_2);
x_398 = lean_apply_1(x_396, x_2);
lean_inc_ref(x_2);
x_399 = lean_apply_1(x_397, x_2);
x_400 = lean_name_eq(x_398, x_399);
lean_dec(x_399);
if (x_400 == 0)
{
lean_object* x_401; uint8_t x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; 
x_401 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_402 = 1;
x_403 = l_Lean_Name_toString(x_398, x_402);
x_404 = lean_box(0);
x_405 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_405, 0, x_404);
lean_ctor_set(x_405, 1, x_403);
x_406 = l_Lake_Toml_RBDict_insert___redArg(x_401, x_393, x_405, x_394);
x_381 = x_406;
goto block_392;
}
else
{
lean_dec(x_398);
x_381 = x_394;
goto block_392;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanExeConfig_instToToml___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_box(0);
x_4 = lean_obj_once(&l_Lake_Toml_encodeLeanOptions___closed__0, &l_Lake_Toml_encodeLeanOptions___closed__0_once, _init_l_Lake_Toml_encodeLeanOptions___closed__0);
x_5 = l___private_Lake_CLI_Translate_Toml_0__Lake_LeanExeConfig_toToml(x_1, x_2, x_4);
x_6 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_LeanExeConfig_instToToml(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanExeConfig_instToToml___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_InputFileConfig_toToml(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_17; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_4 = 1;
lean_inc(x_1);
x_5 = l_Lean_Name_toString(x_1, x_4);
lean_inc(x_1);
x_6 = l_Lake_InputFileConfig_path___proj(x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 3);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_InputFileConfig_toToml___closed__1));
x_29 = ((lean_object*)(l_Lake_Dependency_toToml___closed__12));
x_30 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_5);
x_33 = l_Lake_Toml_RBDict_insert___redArg(x_30, x_29, x_32, x_3);
lean_inc_ref(x_2);
x_34 = lean_apply_1(x_7, x_2);
lean_inc_ref(x_2);
x_35 = lean_apply_1(x_8, x_2);
lean_inc_ref(x_34);
x_36 = l_System_FilePath_normalize(x_34);
x_37 = l_System_FilePath_normalize(x_35);
x_38 = lean_string_dec_eq(x_36, x_37);
lean_dec_ref(x_37);
lean_dec_ref(x_36);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = ((lean_object*)(l_Lake_PathPatDescr_toToml_x3f___closed__1));
x_40 = l_Lake_mkRelPathString(x_34);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_31);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lake_Toml_RBDict_insert___redArg(x_30, x_39, x_41, x_33);
x_17 = x_42;
goto block_28;
}
else
{
lean_dec_ref(x_34);
x_17 = x_33;
goto block_28;
}
block_16:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_11);
x_15 = l_Lake_Toml_RBDict_insert___redArg(x_12, x_9, x_14, x_10);
return x_15;
}
block_28:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = l_Lake_InputFileConfig_text___proj(x_1);
lean_dec(x_1);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 3);
lean_inc(x_20);
lean_dec_ref(x_18);
lean_inc_ref(x_2);
x_21 = lean_apply_1(x_19, x_2);
x_22 = lean_apply_1(x_20, x_2);
x_23 = lean_unbox(x_21);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = lean_unbox(x_22);
if (x_24 == 0)
{
return x_17;
}
else
{
uint8_t x_25; 
x_25 = lean_unbox(x_21);
x_10 = x_17;
x_11 = x_25;
goto block_16;
}
}
else
{
uint8_t x_26; 
x_26 = lean_unbox(x_22);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = lean_unbox(x_21);
x_10 = x_17;
x_11 = x_27;
goto block_16;
}
else
{
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_InputFileConfig_instToToml___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_box(0);
x_4 = lean_obj_once(&l_Lake_Toml_encodeLeanOptions___closed__0, &l_Lake_Toml_encodeLeanOptions___closed__0_once, _init_l_Lake_Toml_encodeLeanOptions___closed__0);
x_5 = l___private_Lake_CLI_Translate_Toml_0__Lake_InputFileConfig_toToml(x_1, x_2, x_4);
x_6 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_InputFileConfig_instToToml(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lake_CLI_Translate_Toml_0__Lake_InputFileConfig_instToToml___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00__private_Lake_CLI_Translate_Toml_0__Lake_InputDirConfig_toToml_spec__0_spec__0___redArg(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
lean_dec_ref(x_1);
x_3 = l_Lake_Pattern_toToml_x3f___at___00__private_Lake_CLI_Translate_Toml_0__Lake_InputDirConfig_toToml_spec__0___redArg(x_2);
if (lean_obj_tag(x_3) == 0)
{
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_17; 
x_4 = lean_ctor_get(x_3, 0);
x_17 = !lean_is_exclusive(x_3);
if (x_17 == 0)
{
x_5 = x_3;
x_6 = x_17;
goto block_16;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = ((lean_object*)(l_Lake_PatternDescr_toToml_x3f___redArg___closed__1));
x_8 = lean_box(0);
x_9 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_10 = lean_obj_once(&l_Lake_Toml_encodeLeanOptions___closed__0, &l_Lake_Toml_encodeLeanOptions___closed__0_once, _init_l_Lake_Toml_encodeLeanOptions___closed__0);
x_11 = l_Lake_Toml_RBDict_insert___redArg(x_9, x_7, x_4, x_10);
x_12 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
if (x_6 == 0)
{
lean_ctor_set(x_5, 0, x_12);
x_13 = x_5;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
}
case 1:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_18);
lean_dec_ref(x_1);
x_19 = l_Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00__private_Lake_CLI_Translate_Toml_0__Lake_InputDirConfig_toToml_spec__0_spec__0_spec__1___redArg(x_18);
lean_dec_ref(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_box(0);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_35; 
x_21 = lean_ctor_get(x_19, 0);
x_35 = !lean_is_exclusive(x_19);
if (x_35 == 0)
{
x_22 = x_19;
x_23 = x_35;
goto block_34;
}
else
{
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_box(0);
x_23 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = ((lean_object*)(l_Lake_PatternDescr_toToml_x3f___redArg___closed__3));
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_21);
x_27 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_28 = lean_obj_once(&l_Lake_Toml_encodeLeanOptions___closed__0, &l_Lake_Toml_encodeLeanOptions___closed__0_once, _init_l_Lake_Toml_encodeLeanOptions___closed__0);
x_29 = l_Lake_Toml_RBDict_insert___redArg(x_27, x_24, x_26, x_28);
x_30 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_29);
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_30);
x_31 = x_22;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_30);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
}
}
case 2:
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_36);
lean_dec_ref(x_1);
x_37 = l_Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00__private_Lake_CLI_Translate_Toml_0__Lake_InputDirConfig_toToml_spec__0_spec__0_spec__1___redArg(x_36);
lean_dec_ref(x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_box(0);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_53; 
x_39 = lean_ctor_get(x_37, 0);
x_53 = !lean_is_exclusive(x_37);
if (x_53 == 0)
{
x_40 = x_37;
x_41 = x_53;
goto block_52;
}
else
{
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_box(0);
x_41 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_42 = ((lean_object*)(l_Lake_PatternDescr_toToml_x3f___redArg___closed__5));
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_39);
x_45 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_46 = lean_obj_once(&l_Lake_Toml_encodeLeanOptions___closed__0, &l_Lake_Toml_encodeLeanOptions___closed__0_once, _init_l_Lake_Toml_encodeLeanOptions___closed__0);
x_47 = l_Lake_Toml_RBDict_insert___redArg(x_45, x_42, x_44, x_46);
x_48 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_48, 0, x_43);
lean_ctor_set(x_48, 1, x_47);
if (x_41 == 0)
{
lean_ctor_set(x_40, 0, x_48);
x_49 = x_40;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_48);
x_49 = x_51;
goto block_50;
}
block_50:
{
return x_49;
}
}
}
}
default: 
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_1, 0);
lean_inc(x_54);
lean_dec_ref(x_1);
x_55 = l_Lake_PathPatDescr_toToml_x3f(x_54);
return x_55;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_toToml_x3f___at___00__private_Lake_CLI_Translate_Toml_0__Lake_InputDirConfig_toToml_spec__0___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
lean_dec_ref(x_1);
switch (lean_obj_tag(x_2)) {
case 0:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_15; 
x_15 = lean_box(0);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
lean_dec_ref(x_3);
x_17 = l_Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00__private_Lake_CLI_Translate_Toml_0__Lake_InputDirConfig_toToml_spec__0_spec__0___redArg(x_16);
return x_17;
}
}
case 1:
{
lean_object* x_18; 
lean_dec(x_3);
x_18 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_2, 1);
x_20 = ((lean_object*)(l_Lake_Pattern_toToml_x3f___redArg___closed__2));
x_21 = lean_string_dec_eq(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = ((lean_object*)(l_Lake_Pattern_toToml_x3f___redArg___closed__3));
x_23 = lean_string_dec_eq(x_19, x_22);
if (x_23 == 0)
{
goto block_14;
}
else
{
lean_object* x_24; 
lean_dec_ref(x_2);
x_24 = ((lean_object*)(l_Lake_Pattern_toToml_x3f___redArg___closed__6));
return x_24;
}
}
else
{
lean_object* x_25; 
lean_dec_ref(x_2);
x_25 = lean_box(0);
return x_25;
}
}
else
{
goto block_14;
}
}
default: 
{
lean_dec(x_3);
goto block_14;
}
}
block_14:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = lean_box(0);
x_5 = ((lean_object*)(l_Lake_Pattern_toToml_x3f___redArg___closed__1));
x_6 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_7 = lean_obj_once(&l_Lake_Toml_encodeLeanOptions___closed__0, &l_Lake_Toml_encodeLeanOptions___closed__0_once, _init_l_Lake_Toml_encodeLeanOptions___closed__0);
x_8 = 1;
x_9 = l_Lean_Name_toString(x_2, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lake_Toml_RBDict_insert___redArg(x_6, x_5, x_10, x_7);
x_12 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00__private_Lake_CLI_Translate_Toml_0__Lake_InputDirConfig_toToml_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
if (lean_obj_tag(x_4) == 0)
{
x_5 = x_4;
goto block_9;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec_ref(x_4);
x_12 = lean_array_uget_borrowed(x_1, x_2);
lean_inc(x_12);
x_13 = l_Lake_Pattern_toToml_x3f___at___00__private_Lake_CLI_Translate_Toml_0__Lake_InputDirConfig_toToml_spec__0___redArg(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
lean_dec(x_11);
x_14 = lean_box(0);
x_5 = x_14;
goto block_9;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_23; 
x_15 = lean_ctor_get(x_13, 0);
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
x_16 = x_13;
x_17 = x_23;
goto block_22;
}
else
{
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_array_push(x_11, x_15);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_18);
x_19 = x_16;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
x_5 = x_19;
goto block_9;
}
}
}
}
}
else
{
return x_4;
}
block_9:
{
size_t x_6; size_t x_7; 
x_6 = 1;
x_7 = lean_usize_add(x_2, x_6);
x_2 = x_7;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00__private_Lake_CLI_Translate_Toml_0__Lake_InputDirConfig_toToml_spec__0_spec__0_spec__1___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = ((lean_object*)(l_Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00Lake_PathPatDescr_toToml_x3f_spec__0_spec__0_spec__1___redArg___closed__1));
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
if (x_5 == 0)
{
return x_3;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_4, x_4);
if (x_6 == 0)
{
if (x_5 == 0)
{
return x_3;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00__private_Lake_CLI_Translate_Toml_0__Lake_InputDirConfig_toToml_spec__0_spec__0_spec__1_spec__2___redArg(x_1, x_7, x_8, x_3);
return x_9;
}
}
else
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = 0;
x_11 = lean_usize_of_nat(x_4);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00__private_Lake_CLI_Translate_Toml_0__Lake_InputDirConfig_toToml_spec__0_spec__0_spec__1_spec__2___redArg(x_1, x_10, x_11, x_3);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00__private_Lake_CLI_Translate_Toml_0__Lake_InputDirConfig_toToml_spec__0_spec__0_spec__1___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00__private_Lake_CLI_Translate_Toml_0__Lake_InputDirConfig_toToml_spec__0_spec__0_spec__1___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00__private_Lake_CLI_Translate_Toml_0__Lake_InputDirConfig_toToml_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00__private_Lake_CLI_Translate_Toml_0__Lake_InputDirConfig_toToml_spec__0_spec__0_spec__1_spec__2___redArg(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_InputDirConfig_toToml(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_27; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_4 = 1;
lean_inc(x_1);
x_5 = l_Lean_Name_toString(x_1, x_4);
lean_inc(x_1);
x_6 = l_Lake_InputDirConfig_path___proj(x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 3);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_InputDirConfig_toToml___closed__1));
x_19 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_InputFileConfig_toToml___closed__1));
x_39 = ((lean_object*)(l_Lake_Dependency_toToml___closed__12));
x_40 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_5);
x_43 = l_Lake_Toml_RBDict_insert___redArg(x_40, x_39, x_42, x_3);
lean_inc_ref(x_2);
x_44 = lean_apply_1(x_7, x_2);
lean_inc_ref(x_2);
x_45 = lean_apply_1(x_8, x_2);
lean_inc_ref(x_44);
x_46 = l_System_FilePath_normalize(x_44);
x_47 = l_System_FilePath_normalize(x_45);
x_48 = lean_string_dec_eq(x_46, x_47);
lean_dec_ref(x_47);
lean_dec_ref(x_46);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = ((lean_object*)(l_Lake_PathPatDescr_toToml_x3f___closed__1));
x_50 = l_Lake_mkRelPathString(x_44);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_41);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lake_Toml_RBDict_insert___redArg(x_40, x_49, x_51, x_43);
x_27 = x_52;
goto block_38;
}
else
{
lean_dec_ref(x_44);
x_27 = x_43;
goto block_38;
}
block_18:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lake_InputDirConfig_filter___proj(x_1);
lean_dec(x_1);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = lean_apply_1(x_12, x_2);
x_14 = l_Lake_Pattern_toToml_x3f___at___00__private_Lake_CLI_Translate_Toml_0__Lake_InputDirConfig_toToml_spec__0___redArg(x_13);
if (lean_obj_tag(x_14) == 1)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_17 = l_Lake_Toml_RBDict_insert___redArg(x_16, x_9, x_15, x_10);
return x_17;
}
else
{
lean_dec(x_14);
return x_10;
}
}
block_26:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_21);
x_25 = l_Lake_Toml_RBDict_insert___redArg(x_22, x_19, x_24, x_20);
x_10 = x_25;
goto block_18;
}
block_38:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_28 = l_Lake_InputDirConfig_text___proj(x_1);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 3);
lean_inc(x_30);
lean_dec_ref(x_28);
lean_inc_ref(x_2);
x_31 = lean_apply_1(x_29, x_2);
lean_inc_ref(x_2);
x_32 = lean_apply_1(x_30, x_2);
x_33 = lean_unbox(x_31);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = lean_unbox(x_32);
if (x_34 == 0)
{
x_10 = x_27;
goto block_18;
}
else
{
uint8_t x_35; 
x_35 = lean_unbox(x_31);
x_20 = x_27;
x_21 = x_35;
goto block_26;
}
}
else
{
uint8_t x_36; 
x_36 = lean_unbox(x_32);
if (x_36 == 0)
{
uint8_t x_37; 
x_37 = lean_unbox(x_31);
x_20 = x_27;
x_21 = x_37;
goto block_26;
}
else
{
x_10 = x_27;
goto block_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_toToml_x3f___at___00__private_Lake_CLI_Translate_Toml_0__Lake_InputDirConfig_toToml_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Pattern_toToml_x3f___at___00__private_Lake_CLI_Translate_Toml_0__Lake_InputDirConfig_toToml_spec__0___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00__private_Lake_CLI_Translate_Toml_0__Lake_InputDirConfig_toToml_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00__private_Lake_CLI_Translate_Toml_0__Lake_InputDirConfig_toToml_spec__0_spec__0___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00__private_Lake_CLI_Translate_Toml_0__Lake_InputDirConfig_toToml_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00__private_Lake_CLI_Translate_Toml_0__Lake_InputDirConfig_toToml_spec__0_spec__0_spec__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00__private_Lake_CLI_Translate_Toml_0__Lake_InputDirConfig_toToml_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00__private_Lake_CLI_Translate_Toml_0__Lake_InputDirConfig_toToml_spec__0_spec__0_spec__1(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00__private_Lake_CLI_Translate_Toml_0__Lake_InputDirConfig_toToml_spec__0_spec__0_spec__1_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00__private_Lake_CLI_Translate_Toml_0__Lake_InputDirConfig_toToml_spec__0_spec__0_spec__1_spec__2___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00__private_Lake_CLI_Translate_Toml_0__Lake_InputDirConfig_toToml_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_encodeArray_x3f___at___00Lake_PatternDescr_toToml_x3f___at___00Lake_Pattern_toToml_x3f___at___00__private_Lake_CLI_Translate_Toml_0__Lake_InputDirConfig_toToml_spec__0_spec__0_spec__1_spec__2(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_InputDirConfig_instToToml___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_box(0);
x_4 = lean_obj_once(&l_Lake_Toml_encodeLeanOptions___closed__0, &l_Lake_Toml_encodeLeanOptions___closed__0_once, _init_l_Lake_Toml_encodeLeanOptions___closed__0);
x_5 = l___private_Lake_CLI_Translate_Toml_0__Lake_InputDirConfig_toToml(x_1, x_2, x_4);
x_6 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_InputDirConfig_instToToml(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lake_CLI_Translate_Toml_0__Lake_InputDirConfig_instToToml___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_WorkspaceConfig_toToml(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_3 = l_Lake_WorkspaceConfig_packagesDir___proj;
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 3);
lean_inc(x_5);
lean_inc_ref(x_1);
x_6 = lean_apply_1(x_4, x_1);
x_7 = lean_apply_1(x_5, x_1);
lean_inc_ref(x_6);
x_8 = l_System_FilePath_normalize(x_6);
x_9 = l_System_FilePath_normalize(x_7);
x_10 = lean_string_dec_eq(x_8, x_9);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_WorkspaceConfig_toToml___closed__1));
x_12 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_13 = l_Lake_mkRelPathString(x_6);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Lake_Toml_RBDict_insert___redArg(x_12, x_11, x_15, x_2);
return x_16;
}
else
{
lean_dec_ref(x_6);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_WorkspaceConfig_instToToml___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_box(0);
x_3 = lean_obj_once(&l_Lake_Toml_encodeLeanOptions___closed__0, &l_Lake_Toml_encodeLeanOptions___closed__0_once, _init_l_Lake_Toml_encodeLeanOptions___closed__0);
x_4 = l___private_Lake_CLI_Translate_Toml_0__Lake_WorkspaceConfig_toToml(x_1, x_3);
x_5 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 1)
{
lean_dec(x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_3, x_6);
lean_dec(x_3);
x_8 = lean_array_fget_borrowed(x_1, x_7);
x_9 = lean_array_fget_borrowed(x_2, x_7);
lean_inc(x_8);
x_10 = l_System_FilePath_normalize(x_8);
lean_inc(x_9);
x_11 = l_System_FilePath_normalize(x_9);
x_12 = lean_string_dec_eq(x_10, x_11);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
if (x_12 == 0)
{
lean_dec(x_7);
return x_12;
}
else
{
x_3 = x_7;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml_spec__1___redArg(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lake_mkRelPathString(x_5);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_13 = lean_array_uset(x_7, x_2, x_10);
x_2 = x_12;
x_3 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_27; lean_object* x_28; lean_object* x_46; lean_object* x_47; lean_object* x_61; lean_object* x_62; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_92; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_117; lean_object* x_131; lean_object* x_132; lean_object* x_150; lean_object* x_151; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_180; lean_object* x_194; lean_object* x_195; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_222; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_247; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_272; lean_object* x_286; lean_object* x_287; lean_object* x_303; lean_object* x_304; lean_object* x_323; lean_object* x_324; lean_object* x_342; uint8_t x_343; lean_object* x_344; lean_object* x_350; lean_object* x_362; lean_object* x_363; uint8_t x_364; lean_object* x_370; lean_object* x_382; lean_object* x_383; lean_object* x_394; lean_object* x_395; lean_object* x_406; uint8_t x_407; lean_object* x_408; lean_object* x_414; lean_object* x_426; lean_object* x_427; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_453; lean_object* x_464; lean_object* x_465; lean_object* x_477; lean_object* x_478; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_501; lean_object* x_512; lean_object* x_513; lean_object* x_525; lean_object* x_526; lean_object* x_535; lean_object* x_536; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_560; lean_object* x_571; lean_object* x_572; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_595; lean_object* x_606; lean_object* x_607; lean_object* x_619; uint8_t x_620; lean_object* x_621; lean_object* x_627; lean_object* x_639; lean_object* x_640; lean_object* x_650; lean_object* x_651; lean_object* x_661; lean_object* x_662; lean_object* x_677; lean_object* x_678; lean_object* x_693; lean_object* x_694; lean_object* x_709; lean_object* x_710; lean_object* x_725; lean_object* x_726; lean_object* x_741; lean_object* x_742; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_768; lean_object* x_779; uint8_t x_780; lean_object* x_781; lean_object* x_787; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_810; lean_object* x_821; lean_object* x_822; lean_object* x_833; lean_object* x_834; lean_object* x_835; uint8_t x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_846; uint8_t x_847; 
x_5 = l_Lake_PackageConfig_bootstrap___proj(x_1, x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 3);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__1));
x_27 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__3));
x_46 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__5));
x_61 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__7));
x_81 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__9));
x_106 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__11));
x_131 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__13));
x_150 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__15));
x_169 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__17));
x_194 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__19));
x_211 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__21));
x_236 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__23));
x_261 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__25));
x_286 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__27));
x_303 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml___closed__29));
x_323 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_WorkspaceConfig_toToml___closed__1));
x_342 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__1));
x_362 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__11));
x_382 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__1));
x_394 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__3));
x_406 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__5));
x_426 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__7));
x_442 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__9));
x_464 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__11));
x_477 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__13));
x_490 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__15));
x_512 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__17));
x_525 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__19));
x_535 = ((lean_object*)(l_Lake_Dependency_toToml___closed__9));
x_549 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__21));
x_571 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__23));
x_584 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__25));
x_606 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__27));
x_619 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__29));
x_639 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__31));
x_650 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__33));
x_661 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__35));
x_677 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__37));
x_693 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__39));
x_709 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__41));
x_725 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__43));
x_741 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__19));
x_757 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__45));
x_779 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__5));
x_799 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml___closed__7));
x_821 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__47));
x_833 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___closed__49));
x_834 = ((lean_object*)(l_Lake_Dependency_toToml___closed__12));
x_835 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_836 = 1;
lean_inc(x_2);
x_837 = l_Lean_Name_toString(x_2, x_836);
x_838 = lean_box(0);
x_839 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_839, 0, x_838);
lean_ctor_set(x_839, 1, x_837);
x_840 = l_Lake_Toml_RBDict_insert___redArg(x_835, x_834, x_839, x_4);
lean_inc_ref(x_3);
x_841 = lean_apply_1(x_6, x_3);
lean_inc_ref(x_3);
x_846 = lean_apply_1(x_7, x_3);
x_847 = lean_unbox(x_841);
if (x_847 == 0)
{
uint8_t x_848; 
x_848 = lean_unbox(x_846);
if (x_848 == 0)
{
x_822 = x_840;
goto block_832;
}
else
{
goto block_845;
}
}
else
{
uint8_t x_849; 
x_849 = lean_unbox(x_846);
if (x_849 == 0)
{
goto block_845;
}
else
{
x_822 = x_840;
goto block_832;
}
}
block_26:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_10 = l_Lake_LeanConfig_plugins___proj;
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = l_Lake_PackageConfig_toLeanConfig___proj(x_1, x_2);
lean_dec(x_2);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_apply_1(x_13, x_3);
x_15 = lean_apply_1(x_11, x_14);
x_16 = lean_array_get_size(x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_20 = lean_box(0);
x_21 = lean_array_size(x_15);
x_22 = 0;
x_23 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__0(x_21, x_22, x_15);
x_24 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lake_Toml_RBDict_insert___redArg(x_19, x_8, x_24, x_9);
return x_25;
}
else
{
lean_dec_ref(x_15);
return x_9;
}
}
block_45:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_29 = l_Lake_LeanConfig_dynlibs___proj;
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = l_Lake_PackageConfig_toLeanConfig___proj(x_1, x_2);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
lean_inc_ref(x_3);
x_33 = lean_apply_1(x_32, x_3);
x_34 = lean_apply_1(x_30, x_33);
x_35 = lean_array_get_size(x_34);
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_nat_dec_eq(x_35, x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_39 = lean_box(0);
x_40 = lean_array_size(x_34);
x_41 = 0;
x_42 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__0(x_40, x_41, x_34);
x_43 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_43, 0, x_39);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lake_Toml_RBDict_insert___redArg(x_38, x_27, x_43, x_28);
x_9 = x_44;
goto block_26;
}
else
{
lean_dec_ref(x_34);
x_9 = x_28;
goto block_26;
}
}
block_60:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = l_Lake_LeanConfig_platformIndependent___proj;
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = l_Lake_PackageConfig_toLeanConfig___proj(x_1, x_2);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec_ref(x_50);
lean_inc_ref(x_3);
x_52 = lean_apply_1(x_51, x_3);
x_53 = lean_apply_1(x_49, x_52);
if (lean_obj_tag(x_53) == 0)
{
x_28 = x_47;
goto block_45;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec_ref(x_53);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(x_56, 0, x_55);
x_57 = lean_unbox(x_54);
lean_dec(x_54);
lean_ctor_set_uint8(x_56, sizeof(void*)*1, x_57);
x_58 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_59 = l_Lake_Toml_RBDict_insert___redArg(x_58, x_46, x_56, x_47);
x_28 = x_59;
goto block_45;
}
}
block_80:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; 
x_63 = l_Lake_LeanConfig_backend___proj;
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 3);
lean_inc(x_65);
x_66 = l_Lake_PackageConfig_toLeanConfig___proj(x_1, x_2);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
lean_dec_ref(x_66);
lean_inc_ref(x_3);
x_68 = lean_apply_1(x_67, x_3);
lean_inc_ref(x_68);
x_69 = lean_apply_1(x_64, x_68);
x_70 = lean_apply_1(x_65, x_68);
x_71 = lean_unbox(x_69);
x_72 = lean_unbox(x_70);
x_73 = l_Lake_instDecidableEqBackend(x_71, x_72);
if (x_73 == 0)
{
lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_74 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_75 = lean_unbox(x_69);
x_76 = l_Lake_Backend_toString(x_75);
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
x_79 = l_Lake_Toml_RBDict_insert___redArg(x_74, x_61, x_78, x_62);
x_47 = x_79;
goto block_60;
}
else
{
x_47 = x_62;
goto block_60;
}
}
block_91:
{
lean_object* x_84; lean_object* x_85; size_t x_86; size_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_84 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_85 = lean_box(0);
x_86 = lean_array_size(x_83);
x_87 = 0;
x_88 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_StrPatDescr_toToml_spec__0(x_86, x_87, x_83);
x_89 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_89, 0, x_85);
lean_ctor_set(x_89, 1, x_88);
x_90 = l_Lake_Toml_RBDict_insert___redArg(x_84, x_81, x_89, x_82);
x_62 = x_90;
goto block_80;
}
block_105:
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_93 = l_Lake_LeanConfig_weakLinkArgs___proj;
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 3);
lean_inc(x_95);
x_96 = l_Lake_PackageConfig_toLeanConfig___proj(x_1, x_2);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
lean_dec_ref(x_96);
lean_inc_ref(x_3);
x_98 = lean_apply_1(x_97, x_3);
lean_inc_ref(x_98);
x_99 = lean_apply_1(x_94, x_98);
x_100 = lean_apply_1(x_95, x_98);
x_101 = lean_array_get_size(x_99);
x_102 = lean_array_get_size(x_100);
x_103 = lean_nat_dec_eq(x_101, x_102);
if (x_103 == 0)
{
lean_dec_ref(x_100);
x_82 = x_92;
x_83 = x_99;
goto block_91;
}
else
{
uint8_t x_104; 
x_104 = l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__1___redArg(x_99, x_100, x_101);
lean_dec_ref(x_100);
if (x_104 == 0)
{
x_82 = x_92;
x_83 = x_99;
goto block_91;
}
else
{
lean_dec_ref(x_99);
x_62 = x_92;
goto block_80;
}
}
}
block_116:
{
lean_object* x_109; lean_object* x_110; size_t x_111; size_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_109 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_110 = lean_box(0);
x_111 = lean_array_size(x_108);
x_112 = 0;
x_113 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_StrPatDescr_toToml_spec__0(x_111, x_112, x_108);
x_114 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_114, 0, x_110);
lean_ctor_set(x_114, 1, x_113);
x_115 = l_Lake_Toml_RBDict_insert___redArg(x_109, x_106, x_114, x_107);
x_92 = x_115;
goto block_105;
}
block_130:
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_118 = l_Lake_LeanConfig_moreLinkArgs___proj;
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 3);
lean_inc(x_120);
x_121 = l_Lake_PackageConfig_toLeanConfig___proj(x_1, x_2);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
lean_dec_ref(x_121);
lean_inc_ref(x_3);
x_123 = lean_apply_1(x_122, x_3);
lean_inc_ref(x_123);
x_124 = lean_apply_1(x_119, x_123);
x_125 = lean_apply_1(x_120, x_123);
x_126 = lean_array_get_size(x_124);
x_127 = lean_array_get_size(x_125);
x_128 = lean_nat_dec_eq(x_126, x_127);
if (x_128 == 0)
{
lean_dec_ref(x_125);
x_107 = x_117;
x_108 = x_124;
goto block_116;
}
else
{
uint8_t x_129; 
x_129 = l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__1___redArg(x_124, x_125, x_126);
lean_dec_ref(x_125);
if (x_129 == 0)
{
x_107 = x_117;
x_108 = x_124;
goto block_116;
}
else
{
lean_dec_ref(x_124);
x_92 = x_117;
goto block_105;
}
}
}
block_149:
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; 
x_133 = l_Lake_LeanConfig_moreLinkLibs___proj;
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = l_Lake_PackageConfig_toLeanConfig___proj(x_1, x_2);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
lean_dec_ref(x_135);
lean_inc_ref(x_3);
x_137 = lean_apply_1(x_136, x_3);
x_138 = lean_apply_1(x_134, x_137);
x_139 = lean_array_get_size(x_138);
x_140 = lean_unsigned_to_nat(0u);
x_141 = lean_nat_dec_eq(x_139, x_140);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; size_t x_144; size_t x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_142 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_143 = lean_box(0);
x_144 = lean_array_size(x_138);
x_145 = 0;
x_146 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__0(x_144, x_145, x_138);
x_147 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_147, 0, x_143);
lean_ctor_set(x_147, 1, x_146);
x_148 = l_Lake_Toml_RBDict_insert___redArg(x_142, x_131, x_147, x_132);
x_117 = x_148;
goto block_130;
}
else
{
lean_dec_ref(x_138);
x_117 = x_132;
goto block_130;
}
}
block_168:
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; 
x_152 = l_Lake_LeanConfig_moreLinkObjs___proj;
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = l_Lake_PackageConfig_toLeanConfig___proj(x_1, x_2);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
lean_dec_ref(x_154);
lean_inc_ref(x_3);
x_156 = lean_apply_1(x_155, x_3);
x_157 = lean_apply_1(x_153, x_156);
x_158 = lean_array_get_size(x_157);
x_159 = lean_unsigned_to_nat(0u);
x_160 = lean_nat_dec_eq(x_158, x_159);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; size_t x_163; size_t x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_161 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_162 = lean_box(0);
x_163 = lean_array_size(x_157);
x_164 = 0;
x_165 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__2(x_163, x_164, x_157);
x_166 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_166, 0, x_162);
lean_ctor_set(x_166, 1, x_165);
x_167 = l_Lake_Toml_RBDict_insert___redArg(x_161, x_150, x_166, x_151);
x_132 = x_167;
goto block_149;
}
else
{
lean_dec_ref(x_157);
x_132 = x_151;
goto block_149;
}
}
block_179:
{
lean_object* x_172; lean_object* x_173; size_t x_174; size_t x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_172 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_173 = lean_box(0);
x_174 = lean_array_size(x_170);
x_175 = 0;
x_176 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_StrPatDescr_toToml_spec__0(x_174, x_175, x_170);
x_177 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_177, 0, x_173);
lean_ctor_set(x_177, 1, x_176);
x_178 = l_Lake_Toml_RBDict_insert___redArg(x_172, x_169, x_177, x_171);
x_151 = x_178;
goto block_168;
}
block_193:
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; 
x_181 = l_Lake_LeanConfig_weakLeancArgs___proj;
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 3);
lean_inc(x_183);
x_184 = l_Lake_PackageConfig_toLeanConfig___proj(x_1, x_2);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
lean_dec_ref(x_184);
lean_inc_ref(x_3);
x_186 = lean_apply_1(x_185, x_3);
lean_inc_ref(x_186);
x_187 = lean_apply_1(x_182, x_186);
x_188 = lean_apply_1(x_183, x_186);
x_189 = lean_array_get_size(x_187);
x_190 = lean_array_get_size(x_188);
x_191 = lean_nat_dec_eq(x_189, x_190);
if (x_191 == 0)
{
lean_dec_ref(x_188);
x_170 = x_187;
x_171 = x_180;
goto block_179;
}
else
{
uint8_t x_192; 
x_192 = l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__1___redArg(x_187, x_188, x_189);
lean_dec_ref(x_188);
if (x_192 == 0)
{
x_170 = x_187;
x_171 = x_180;
goto block_179;
}
else
{
lean_dec_ref(x_187);
x_151 = x_180;
goto block_168;
}
}
}
block_210:
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; 
x_196 = l_Lake_LeanConfig_moreServerOptions___proj;
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = l_Lake_PackageConfig_toLeanConfig___proj(x_1, x_2);
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
lean_dec_ref(x_198);
lean_inc_ref(x_3);
x_200 = lean_apply_1(x_199, x_3);
x_201 = lean_apply_1(x_197, x_200);
x_202 = lean_array_get_size(x_201);
x_203 = lean_unsigned_to_nat(0u);
x_204 = lean_nat_dec_eq(x_202, x_203);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_205 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_206 = lean_box(0);
x_207 = l_Lake_Toml_encodeLeanOptions(x_201);
lean_dec_ref(x_201);
x_208 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
x_209 = l_Lake_Toml_RBDict_insert___redArg(x_205, x_194, x_208, x_195);
x_180 = x_209;
goto block_193;
}
else
{
lean_dec_ref(x_201);
x_180 = x_195;
goto block_193;
}
}
block_221:
{
lean_object* x_214; lean_object* x_215; size_t x_216; size_t x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_214 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_215 = lean_box(0);
x_216 = lean_array_size(x_213);
x_217 = 0;
x_218 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_StrPatDescr_toToml_spec__0(x_216, x_217, x_213);
x_219 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_219, 0, x_215);
lean_ctor_set(x_219, 1, x_218);
x_220 = l_Lake_Toml_RBDict_insert___redArg(x_214, x_211, x_219, x_212);
x_195 = x_220;
goto block_210;
}
block_235:
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; 
x_223 = l_Lake_LeanConfig_moreLeancArgs___proj;
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_223, 3);
lean_inc(x_225);
x_226 = l_Lake_PackageConfig_toLeanConfig___proj(x_1, x_2);
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
lean_dec_ref(x_226);
lean_inc_ref(x_3);
x_228 = lean_apply_1(x_227, x_3);
lean_inc_ref(x_228);
x_229 = lean_apply_1(x_224, x_228);
x_230 = lean_apply_1(x_225, x_228);
x_231 = lean_array_get_size(x_229);
x_232 = lean_array_get_size(x_230);
x_233 = lean_nat_dec_eq(x_231, x_232);
if (x_233 == 0)
{
lean_dec_ref(x_230);
x_212 = x_222;
x_213 = x_229;
goto block_221;
}
else
{
uint8_t x_234; 
x_234 = l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__1___redArg(x_229, x_230, x_231);
lean_dec_ref(x_230);
if (x_234 == 0)
{
x_212 = x_222;
x_213 = x_229;
goto block_221;
}
else
{
lean_dec_ref(x_229);
x_195 = x_222;
goto block_210;
}
}
}
block_246:
{
lean_object* x_239; lean_object* x_240; size_t x_241; size_t x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_239 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_240 = lean_box(0);
x_241 = lean_array_size(x_238);
x_242 = 0;
x_243 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_StrPatDescr_toToml_spec__0(x_241, x_242, x_238);
x_244 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_244, 0, x_240);
lean_ctor_set(x_244, 1, x_243);
x_245 = l_Lake_Toml_RBDict_insert___redArg(x_239, x_236, x_244, x_237);
x_222 = x_245;
goto block_235;
}
block_260:
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; 
x_248 = l_Lake_LeanConfig_weakLeanArgs___proj;
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_248, 3);
lean_inc(x_250);
x_251 = l_Lake_PackageConfig_toLeanConfig___proj(x_1, x_2);
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
lean_dec_ref(x_251);
lean_inc_ref(x_3);
x_253 = lean_apply_1(x_252, x_3);
lean_inc_ref(x_253);
x_254 = lean_apply_1(x_249, x_253);
x_255 = lean_apply_1(x_250, x_253);
x_256 = lean_array_get_size(x_254);
x_257 = lean_array_get_size(x_255);
x_258 = lean_nat_dec_eq(x_256, x_257);
if (x_258 == 0)
{
lean_dec_ref(x_255);
x_237 = x_247;
x_238 = x_254;
goto block_246;
}
else
{
uint8_t x_259; 
x_259 = l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__1___redArg(x_254, x_255, x_256);
lean_dec_ref(x_255);
if (x_259 == 0)
{
x_237 = x_247;
x_238 = x_254;
goto block_246;
}
else
{
lean_dec_ref(x_254);
x_222 = x_247;
goto block_235;
}
}
}
block_271:
{
lean_object* x_264; lean_object* x_265; size_t x_266; size_t x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_264 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_265 = lean_box(0);
x_266 = lean_array_size(x_263);
x_267 = 0;
x_268 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_StrPatDescr_toToml_spec__0(x_266, x_267, x_263);
x_269 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_269, 0, x_265);
lean_ctor_set(x_269, 1, x_268);
x_270 = l_Lake_Toml_RBDict_insert___redArg(x_264, x_261, x_269, x_262);
x_247 = x_270;
goto block_260;
}
block_285:
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; uint8_t x_283; 
x_273 = l_Lake_LeanConfig_moreLeanArgs___proj;
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_273, 3);
lean_inc(x_275);
x_276 = l_Lake_PackageConfig_toLeanConfig___proj(x_1, x_2);
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
lean_dec_ref(x_276);
lean_inc_ref(x_3);
x_278 = lean_apply_1(x_277, x_3);
lean_inc_ref(x_278);
x_279 = lean_apply_1(x_274, x_278);
x_280 = lean_apply_1(x_275, x_278);
x_281 = lean_array_get_size(x_279);
x_282 = lean_array_get_size(x_280);
x_283 = lean_nat_dec_eq(x_281, x_282);
if (x_283 == 0)
{
lean_dec_ref(x_280);
x_262 = x_272;
x_263 = x_279;
goto block_271;
}
else
{
uint8_t x_284; 
x_284 = l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__1___redArg(x_279, x_280, x_281);
lean_dec_ref(x_280);
if (x_284 == 0)
{
x_262 = x_272;
x_263 = x_279;
goto block_271;
}
else
{
lean_dec_ref(x_279);
x_247 = x_272;
goto block_260;
}
}
}
block_302:
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; uint8_t x_296; 
x_288 = l_Lake_LeanConfig_leanOptions___proj;
x_289 = lean_ctor_get(x_288, 0);
lean_inc(x_289);
x_290 = l_Lake_PackageConfig_toLeanConfig___proj(x_1, x_2);
x_291 = lean_ctor_get(x_290, 0);
lean_inc(x_291);
lean_dec_ref(x_290);
lean_inc_ref(x_3);
x_292 = lean_apply_1(x_291, x_3);
x_293 = lean_apply_1(x_289, x_292);
x_294 = lean_array_get_size(x_293);
x_295 = lean_unsigned_to_nat(0u);
x_296 = lean_nat_dec_eq(x_294, x_295);
if (x_296 == 0)
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_297 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_298 = lean_box(0);
x_299 = l_Lake_Toml_encodeLeanOptions(x_293);
lean_dec_ref(x_293);
x_300 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_300, 0, x_298);
lean_ctor_set(x_300, 1, x_299);
x_301 = l_Lake_Toml_RBDict_insert___redArg(x_297, x_286, x_300, x_287);
x_272 = x_301;
goto block_285;
}
else
{
lean_dec_ref(x_293);
x_272 = x_287;
goto block_285;
}
}
block_322:
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; uint8_t x_313; uint8_t x_314; uint8_t x_315; 
x_305 = l_Lake_LeanConfig_buildType___proj;
x_306 = lean_ctor_get(x_305, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_305, 3);
lean_inc(x_307);
x_308 = l_Lake_PackageConfig_toLeanConfig___proj(x_1, x_2);
x_309 = lean_ctor_get(x_308, 0);
lean_inc(x_309);
lean_dec_ref(x_308);
lean_inc_ref(x_3);
x_310 = lean_apply_1(x_309, x_3);
lean_inc_ref(x_310);
x_311 = lean_apply_1(x_306, x_310);
x_312 = lean_apply_1(x_307, x_310);
x_313 = lean_unbox(x_311);
x_314 = lean_unbox(x_312);
x_315 = l_Lake_instDecidableEqBuildType(x_313, x_314);
if (x_315 == 0)
{
lean_object* x_316; uint8_t x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_316 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_317 = lean_unbox(x_311);
x_318 = l_Lake_BuildType_toString(x_317);
x_319 = lean_box(0);
x_320 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_320, 0, x_319);
lean_ctor_set(x_320, 1, x_318);
x_321 = l_Lake_Toml_RBDict_insert___redArg(x_316, x_303, x_320, x_304);
x_287 = x_321;
goto block_302;
}
else
{
x_287 = x_304;
goto block_302;
}
}
block_341:
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; uint8_t x_335; 
x_325 = l_Lake_WorkspaceConfig_packagesDir___proj;
x_326 = lean_ctor_get(x_325, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_325, 3);
lean_inc(x_327);
x_328 = l_Lake_PackageConfig_toWorkspaceConfig___proj(x_1, x_2);
x_329 = lean_ctor_get(x_328, 0);
lean_inc(x_329);
lean_dec_ref(x_328);
lean_inc_ref(x_3);
x_330 = lean_apply_1(x_329, x_3);
lean_inc_ref(x_330);
x_331 = lean_apply_1(x_326, x_330);
x_332 = lean_apply_1(x_327, x_330);
lean_inc_ref(x_331);
x_333 = l_System_FilePath_normalize(x_331);
x_334 = l_System_FilePath_normalize(x_332);
x_335 = lean_string_dec_eq(x_333, x_334);
lean_dec_ref(x_334);
lean_dec_ref(x_333);
if (x_335 == 0)
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_336 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_337 = l_Lake_mkRelPathString(x_331);
x_338 = lean_box(0);
x_339 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_339, 0, x_338);
lean_ctor_set(x_339, 1, x_337);
x_340 = l_Lake_Toml_RBDict_insert___redArg(x_336, x_323, x_339, x_324);
x_304 = x_340;
goto block_322;
}
else
{
lean_dec_ref(x_331);
x_304 = x_324;
goto block_322;
}
}
block_349:
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_345 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_346 = lean_box(0);
x_347 = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(x_347, 0, x_346);
lean_ctor_set_uint8(x_347, sizeof(void*)*1, x_343);
x_348 = l_Lake_Toml_RBDict_insert___redArg(x_345, x_342, x_347, x_344);
x_324 = x_348;
goto block_341;
}
block_361:
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; uint8_t x_356; 
x_351 = l_Lake_PackageConfig_allowImportAll___proj(x_1, x_2);
x_352 = lean_ctor_get(x_351, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_351, 3);
lean_inc(x_353);
lean_dec_ref(x_351);
lean_inc_ref(x_3);
x_354 = lean_apply_1(x_352, x_3);
lean_inc_ref(x_3);
x_355 = lean_apply_1(x_353, x_3);
x_356 = lean_unbox(x_354);
if (x_356 == 0)
{
uint8_t x_357; 
x_357 = lean_unbox(x_355);
if (x_357 == 0)
{
x_324 = x_350;
goto block_341;
}
else
{
uint8_t x_358; 
x_358 = lean_unbox(x_354);
x_343 = x_358;
x_344 = x_350;
goto block_349;
}
}
else
{
uint8_t x_359; 
x_359 = lean_unbox(x_355);
if (x_359 == 0)
{
uint8_t x_360; 
x_360 = lean_unbox(x_354);
x_343 = x_360;
x_344 = x_350;
goto block_349;
}
else
{
x_324 = x_350;
goto block_341;
}
}
}
block_369:
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_365 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_366 = lean_box(0);
x_367 = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(x_367, 0, x_366);
lean_ctor_set_uint8(x_367, sizeof(void*)*1, x_364);
x_368 = l_Lake_Toml_RBDict_insert___redArg(x_365, x_362, x_367, x_363);
x_350 = x_368;
goto block_361;
}
block_381:
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; uint8_t x_376; 
x_371 = l_Lake_PackageConfig_libPrefixOnWindows___proj(x_1, x_2);
x_372 = lean_ctor_get(x_371, 0);
lean_inc(x_372);
x_373 = lean_ctor_get(x_371, 3);
lean_inc(x_373);
lean_dec_ref(x_371);
lean_inc_ref(x_3);
x_374 = lean_apply_1(x_372, x_3);
lean_inc_ref(x_3);
x_375 = lean_apply_1(x_373, x_3);
x_376 = lean_unbox(x_374);
if (x_376 == 0)
{
uint8_t x_377; 
x_377 = lean_unbox(x_375);
if (x_377 == 0)
{
x_350 = x_370;
goto block_361;
}
else
{
uint8_t x_378; 
x_378 = lean_unbox(x_374);
x_363 = x_370;
x_364 = x_378;
goto block_369;
}
}
else
{
uint8_t x_379; 
x_379 = lean_unbox(x_375);
if (x_379 == 0)
{
uint8_t x_380; 
x_380 = lean_unbox(x_374);
x_363 = x_370;
x_364 = x_380;
goto block_369;
}
else
{
x_350 = x_370;
goto block_361;
}
}
}
block_393:
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; 
x_384 = l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj(x_1, x_2);
x_385 = lean_ctor_get(x_384, 0);
lean_inc(x_385);
lean_dec_ref(x_384);
lean_inc_ref(x_3);
x_386 = lean_apply_1(x_385, x_3);
if (lean_obj_tag(x_386) == 0)
{
x_370 = x_383;
goto block_381;
}
else
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; uint8_t x_390; lean_object* x_391; lean_object* x_392; 
x_387 = lean_ctor_get(x_386, 0);
lean_inc(x_387);
lean_dec_ref(x_386);
x_388 = lean_box(0);
x_389 = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(x_389, 0, x_388);
x_390 = lean_unbox(x_387);
lean_dec(x_387);
lean_ctor_set_uint8(x_389, sizeof(void*)*1, x_390);
x_391 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_392 = l_Lake_Toml_RBDict_insert___redArg(x_391, x_382, x_389, x_383);
x_370 = x_392;
goto block_381;
}
}
block_405:
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_396 = l_Lake_PackageConfig_enableArtifactCache_x3f___proj(x_1, x_2);
x_397 = lean_ctor_get(x_396, 0);
lean_inc(x_397);
lean_dec_ref(x_396);
lean_inc_ref(x_3);
x_398 = lean_apply_1(x_397, x_3);
if (lean_obj_tag(x_398) == 0)
{
x_383 = x_395;
goto block_393;
}
else
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; uint8_t x_402; lean_object* x_403; lean_object* x_404; 
x_399 = lean_ctor_get(x_398, 0);
lean_inc(x_399);
lean_dec_ref(x_398);
x_400 = lean_box(0);
x_401 = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(x_401, 0, x_400);
x_402 = lean_unbox(x_399);
lean_dec(x_399);
lean_ctor_set_uint8(x_401, sizeof(void*)*1, x_402);
x_403 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_404 = l_Lake_Toml_RBDict_insert___redArg(x_403, x_394, x_401, x_395);
x_383 = x_404;
goto block_393;
}
}
block_413:
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; 
x_409 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_410 = lean_box(0);
x_411 = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(x_411, 0, x_410);
lean_ctor_set_uint8(x_411, sizeof(void*)*1, x_407);
x_412 = l_Lake_Toml_RBDict_insert___redArg(x_409, x_406, x_411, x_408);
x_395 = x_412;
goto block_405;
}
block_425:
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; uint8_t x_420; 
x_415 = l_Lake_PackageConfig_reservoir___proj(x_1, x_2);
x_416 = lean_ctor_get(x_415, 0);
lean_inc(x_416);
x_417 = lean_ctor_get(x_415, 3);
lean_inc(x_417);
lean_dec_ref(x_415);
lean_inc_ref(x_3);
x_418 = lean_apply_1(x_416, x_3);
lean_inc_ref(x_3);
x_419 = lean_apply_1(x_417, x_3);
x_420 = lean_unbox(x_418);
if (x_420 == 0)
{
uint8_t x_421; 
x_421 = lean_unbox(x_419);
if (x_421 == 0)
{
x_395 = x_414;
goto block_405;
}
else
{
uint8_t x_422; 
x_422 = lean_unbox(x_418);
x_407 = x_422;
x_408 = x_414;
goto block_413;
}
}
else
{
uint8_t x_423; 
x_423 = lean_unbox(x_419);
if (x_423 == 0)
{
uint8_t x_424; 
x_424 = lean_unbox(x_418);
x_407 = x_424;
x_408 = x_414;
goto block_413;
}
else
{
x_395 = x_414;
goto block_405;
}
}
}
block_441:
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; uint8_t x_435; 
x_428 = l_Lake_PackageConfig_readmeFile___proj(x_1, x_2);
x_429 = lean_ctor_get(x_428, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_428, 3);
lean_inc(x_430);
lean_dec_ref(x_428);
lean_inc_ref(x_3);
x_431 = lean_apply_1(x_429, x_3);
lean_inc_ref(x_3);
x_432 = lean_apply_1(x_430, x_3);
lean_inc_ref(x_431);
x_433 = l_System_FilePath_normalize(x_431);
x_434 = l_System_FilePath_normalize(x_432);
x_435 = lean_string_dec_eq(x_433, x_434);
lean_dec_ref(x_434);
lean_dec_ref(x_433);
if (x_435 == 0)
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; 
x_436 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_437 = l_Lake_mkRelPathString(x_431);
x_438 = lean_box(0);
x_439 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_439, 0, x_438);
lean_ctor_set(x_439, 1, x_437);
x_440 = l_Lake_Toml_RBDict_insert___redArg(x_436, x_426, x_439, x_427);
x_414 = x_440;
goto block_425;
}
else
{
lean_dec_ref(x_431);
x_414 = x_427;
goto block_425;
}
}
block_452:
{
lean_object* x_445; lean_object* x_446; size_t x_447; size_t x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_445 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_446 = lean_box(0);
x_447 = lean_array_size(x_443);
x_448 = 0;
x_449 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml_spec__0(x_447, x_448, x_443);
x_450 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_450, 0, x_446);
lean_ctor_set(x_450, 1, x_449);
x_451 = l_Lake_Toml_RBDict_insert___redArg(x_445, x_442, x_450, x_444);
x_427 = x_451;
goto block_441;
}
block_463:
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; uint8_t x_461; 
x_454 = l_Lake_PackageConfig_licenseFiles___proj(x_1, x_2);
x_455 = lean_ctor_get(x_454, 0);
lean_inc(x_455);
x_456 = lean_ctor_get(x_454, 3);
lean_inc(x_456);
lean_dec_ref(x_454);
lean_inc_ref(x_3);
x_457 = lean_apply_1(x_455, x_3);
lean_inc_ref(x_3);
x_458 = lean_apply_1(x_456, x_3);
x_459 = lean_array_get_size(x_457);
x_460 = lean_array_get_size(x_458);
x_461 = lean_nat_dec_eq(x_459, x_460);
if (x_461 == 0)
{
lean_dec_ref(x_458);
x_443 = x_457;
x_444 = x_453;
goto block_452;
}
else
{
uint8_t x_462; 
x_462 = l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml_spec__1___redArg(x_457, x_458, x_459);
lean_dec_ref(x_458);
if (x_462 == 0)
{
x_443 = x_457;
x_444 = x_453;
goto block_452;
}
else
{
lean_dec_ref(x_457);
x_427 = x_453;
goto block_441;
}
}
}
block_476:
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; uint8_t x_471; 
x_466 = l_Lake_PackageConfig_license___proj(x_1, x_2);
x_467 = lean_ctor_get(x_466, 0);
lean_inc(x_467);
x_468 = lean_ctor_get(x_466, 3);
lean_inc(x_468);
lean_dec_ref(x_466);
lean_inc_ref(x_3);
x_469 = lean_apply_1(x_467, x_3);
lean_inc_ref(x_3);
x_470 = lean_apply_1(x_468, x_3);
x_471 = lean_string_dec_eq(x_469, x_470);
lean_dec_ref(x_470);
if (x_471 == 0)
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; 
x_472 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_473 = lean_box(0);
x_474 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_474, 0, x_473);
lean_ctor_set(x_474, 1, x_469);
x_475 = l_Lake_Toml_RBDict_insert___redArg(x_472, x_464, x_474, x_465);
x_453 = x_475;
goto block_463;
}
else
{
lean_dec_ref(x_469);
x_453 = x_465;
goto block_463;
}
}
block_489:
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; uint8_t x_484; 
x_479 = l_Lake_PackageConfig_homepage___proj(x_1, x_2);
x_480 = lean_ctor_get(x_479, 0);
lean_inc(x_480);
x_481 = lean_ctor_get(x_479, 3);
lean_inc(x_481);
lean_dec_ref(x_479);
lean_inc_ref(x_3);
x_482 = lean_apply_1(x_480, x_3);
lean_inc_ref(x_3);
x_483 = lean_apply_1(x_481, x_3);
x_484 = lean_string_dec_eq(x_482, x_483);
lean_dec_ref(x_483);
if (x_484 == 0)
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; 
x_485 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_486 = lean_box(0);
x_487 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_487, 0, x_486);
lean_ctor_set(x_487, 1, x_482);
x_488 = l_Lake_Toml_RBDict_insert___redArg(x_485, x_477, x_487, x_478);
x_465 = x_488;
goto block_476;
}
else
{
lean_dec_ref(x_482);
x_465 = x_478;
goto block_476;
}
}
block_500:
{
lean_object* x_493; lean_object* x_494; size_t x_495; size_t x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; 
x_493 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_494 = lean_box(0);
x_495 = lean_array_size(x_492);
x_496 = 0;
x_497 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_StrPatDescr_toToml_spec__0(x_495, x_496, x_492);
x_498 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_498, 0, x_494);
lean_ctor_set(x_498, 1, x_497);
x_499 = l_Lake_Toml_RBDict_insert___redArg(x_493, x_490, x_498, x_491);
x_478 = x_499;
goto block_489;
}
block_511:
{
lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; uint8_t x_509; 
x_502 = l_Lake_PackageConfig_keywords___proj(x_1, x_2);
x_503 = lean_ctor_get(x_502, 0);
lean_inc(x_503);
x_504 = lean_ctor_get(x_502, 3);
lean_inc(x_504);
lean_dec_ref(x_502);
lean_inc_ref(x_3);
x_505 = lean_apply_1(x_503, x_3);
lean_inc_ref(x_3);
x_506 = lean_apply_1(x_504, x_3);
x_507 = lean_array_get_size(x_505);
x_508 = lean_array_get_size(x_506);
x_509 = lean_nat_dec_eq(x_507, x_508);
if (x_509 == 0)
{
lean_dec_ref(x_506);
x_491 = x_501;
x_492 = x_505;
goto block_500;
}
else
{
uint8_t x_510; 
x_510 = l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__1___redArg(x_505, x_506, x_507);
lean_dec_ref(x_506);
if (x_510 == 0)
{
x_491 = x_501;
x_492 = x_505;
goto block_500;
}
else
{
lean_dec_ref(x_505);
x_478 = x_501;
goto block_489;
}
}
}
block_524:
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; uint8_t x_519; 
x_514 = l_Lake_PackageConfig_description___proj(x_1, x_2);
x_515 = lean_ctor_get(x_514, 0);
lean_inc(x_515);
x_516 = lean_ctor_get(x_514, 3);
lean_inc(x_516);
lean_dec_ref(x_514);
lean_inc_ref(x_3);
x_517 = lean_apply_1(x_515, x_3);
lean_inc_ref(x_3);
x_518 = lean_apply_1(x_516, x_3);
x_519 = lean_string_dec_eq(x_517, x_518);
lean_dec_ref(x_518);
if (x_519 == 0)
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; 
x_520 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_521 = lean_box(0);
x_522 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_522, 0, x_521);
lean_ctor_set(x_522, 1, x_517);
x_523 = l_Lake_Toml_RBDict_insert___redArg(x_520, x_512, x_522, x_513);
x_501 = x_523;
goto block_511;
}
else
{
lean_dec_ref(x_517);
x_501 = x_513;
goto block_511;
}
}
block_534:
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; 
x_527 = l_Lake_PackageConfig_versionTags___proj(x_1, x_2);
x_528 = lean_ctor_get(x_527, 0);
lean_inc(x_528);
lean_dec_ref(x_527);
lean_inc_ref(x_3);
x_529 = lean_apply_1(x_528, x_3);
x_530 = l_Lake_Pattern_toToml_x3f___at___00Lake_PathPatDescr_toToml_x3f_spec__0___redArg(x_529);
if (lean_obj_tag(x_530) == 1)
{
lean_object* x_531; lean_object* x_532; lean_object* x_533; 
x_531 = lean_ctor_get(x_530, 0);
lean_inc(x_531);
lean_dec_ref(x_530);
x_532 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_533 = l_Lake_Toml_RBDict_insert___redArg(x_532, x_525, x_531, x_526);
x_513 = x_533;
goto block_524;
}
else
{
lean_dec(x_530);
x_513 = x_526;
goto block_524;
}
}
block_548:
{
lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; uint8_t x_542; 
x_537 = l_Lake_PackageConfig_version___proj(x_1, x_2);
x_538 = lean_ctor_get(x_537, 0);
lean_inc(x_538);
x_539 = lean_ctor_get(x_537, 3);
lean_inc(x_539);
lean_dec_ref(x_537);
lean_inc_ref(x_3);
x_540 = lean_apply_1(x_538, x_3);
lean_inc_ref(x_3);
x_541 = lean_apply_1(x_539, x_3);
x_542 = l_Lake_instDecidableEqStdVer_decEq(x_540, x_541);
lean_dec_ref(x_541);
if (x_542 == 0)
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; 
x_543 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_544 = l_Lake_StdVer_toString(x_540);
x_545 = lean_box(0);
x_546 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_546, 0, x_545);
lean_ctor_set(x_546, 1, x_544);
x_547 = l_Lake_Toml_RBDict_insert___redArg(x_543, x_535, x_546, x_536);
x_526 = x_547;
goto block_534;
}
else
{
lean_dec_ref(x_540);
x_526 = x_536;
goto block_534;
}
}
block_559:
{
lean_object* x_552; lean_object* x_553; size_t x_554; size_t x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; 
x_552 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_553 = lean_box(0);
x_554 = lean_array_size(x_551);
x_555 = 0;
x_556 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_StrPatDescr_toToml_spec__0(x_554, x_555, x_551);
x_557 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_557, 0, x_553);
lean_ctor_set(x_557, 1, x_556);
x_558 = l_Lake_Toml_RBDict_insert___redArg(x_552, x_549, x_557, x_550);
x_536 = x_558;
goto block_548;
}
block_570:
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; uint8_t x_568; 
x_561 = l_Lake_PackageConfig_lintDriverArgs___proj(x_1, x_2);
x_562 = lean_ctor_get(x_561, 0);
lean_inc(x_562);
x_563 = lean_ctor_get(x_561, 3);
lean_inc(x_563);
lean_dec_ref(x_561);
lean_inc_ref(x_3);
x_564 = lean_apply_1(x_562, x_3);
lean_inc_ref(x_3);
x_565 = lean_apply_1(x_563, x_3);
x_566 = lean_array_get_size(x_564);
x_567 = lean_array_get_size(x_565);
x_568 = lean_nat_dec_eq(x_566, x_567);
if (x_568 == 0)
{
lean_dec_ref(x_565);
x_550 = x_560;
x_551 = x_564;
goto block_559;
}
else
{
uint8_t x_569; 
x_569 = l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__1___redArg(x_564, x_565, x_566);
lean_dec_ref(x_565);
if (x_569 == 0)
{
x_550 = x_560;
x_551 = x_564;
goto block_559;
}
else
{
lean_dec_ref(x_564);
x_536 = x_560;
goto block_548;
}
}
}
block_583:
{
lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; uint8_t x_578; 
x_573 = l_Lake_PackageConfig_lintDriver___proj(x_1, x_2);
x_574 = lean_ctor_get(x_573, 0);
lean_inc(x_574);
x_575 = lean_ctor_get(x_573, 3);
lean_inc(x_575);
lean_dec_ref(x_573);
lean_inc_ref(x_3);
x_576 = lean_apply_1(x_574, x_3);
lean_inc_ref(x_3);
x_577 = lean_apply_1(x_575, x_3);
x_578 = lean_string_dec_eq(x_576, x_577);
lean_dec_ref(x_577);
if (x_578 == 0)
{
lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; 
x_579 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_580 = lean_box(0);
x_581 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_581, 0, x_580);
lean_ctor_set(x_581, 1, x_576);
x_582 = l_Lake_Toml_RBDict_insert___redArg(x_579, x_571, x_581, x_572);
x_560 = x_582;
goto block_570;
}
else
{
lean_dec_ref(x_576);
x_560 = x_572;
goto block_570;
}
}
block_594:
{
lean_object* x_587; lean_object* x_588; size_t x_589; size_t x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; 
x_587 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_588 = lean_box(0);
x_589 = lean_array_size(x_585);
x_590 = 0;
x_591 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_StrPatDescr_toToml_spec__0(x_589, x_590, x_585);
x_592 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_592, 0, x_588);
lean_ctor_set(x_592, 1, x_591);
x_593 = l_Lake_Toml_RBDict_insert___redArg(x_587, x_584, x_592, x_586);
x_572 = x_593;
goto block_583;
}
block_605:
{
lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; uint8_t x_603; 
x_596 = l_Lake_PackageConfig_testDriverArgs___proj(x_1, x_2);
x_597 = lean_ctor_get(x_596, 0);
lean_inc(x_597);
x_598 = lean_ctor_get(x_596, 3);
lean_inc(x_598);
lean_dec_ref(x_596);
lean_inc_ref(x_3);
x_599 = lean_apply_1(x_597, x_3);
lean_inc_ref(x_3);
x_600 = lean_apply_1(x_598, x_3);
x_601 = lean_array_get_size(x_599);
x_602 = lean_array_get_size(x_600);
x_603 = lean_nat_dec_eq(x_601, x_602);
if (x_603 == 0)
{
lean_dec_ref(x_600);
x_585 = x_599;
x_586 = x_595;
goto block_594;
}
else
{
uint8_t x_604; 
x_604 = l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__1___redArg(x_599, x_600, x_601);
lean_dec_ref(x_600);
if (x_604 == 0)
{
x_585 = x_599;
x_586 = x_595;
goto block_594;
}
else
{
lean_dec_ref(x_599);
x_572 = x_595;
goto block_583;
}
}
}
block_618:
{
lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; uint8_t x_613; 
x_608 = l_Lake_PackageConfig_testDriver___proj(x_1, x_2);
x_609 = lean_ctor_get(x_608, 0);
lean_inc(x_609);
x_610 = lean_ctor_get(x_608, 3);
lean_inc(x_610);
lean_dec_ref(x_608);
lean_inc_ref(x_3);
x_611 = lean_apply_1(x_609, x_3);
lean_inc_ref(x_3);
x_612 = lean_apply_1(x_610, x_3);
x_613 = lean_string_dec_eq(x_611, x_612);
lean_dec_ref(x_612);
if (x_613 == 0)
{
lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; 
x_614 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_615 = lean_box(0);
x_616 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_616, 0, x_615);
lean_ctor_set(x_616, 1, x_611);
x_617 = l_Lake_Toml_RBDict_insert___redArg(x_614, x_606, x_616, x_607);
x_595 = x_617;
goto block_605;
}
else
{
lean_dec_ref(x_611);
x_595 = x_607;
goto block_605;
}
}
block_626:
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; 
x_622 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_623 = lean_box(0);
x_624 = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(x_624, 0, x_623);
lean_ctor_set_uint8(x_624, sizeof(void*)*1, x_620);
x_625 = l_Lake_Toml_RBDict_insert___redArg(x_622, x_619, x_624, x_621);
x_607 = x_625;
goto block_618;
}
block_638:
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; uint8_t x_633; 
x_628 = l_Lake_PackageConfig_preferReleaseBuild___proj(x_1, x_2);
x_629 = lean_ctor_get(x_628, 0);
lean_inc(x_629);
x_630 = lean_ctor_get(x_628, 3);
lean_inc(x_630);
lean_dec_ref(x_628);
lean_inc_ref(x_3);
x_631 = lean_apply_1(x_629, x_3);
lean_inc_ref(x_3);
x_632 = lean_apply_1(x_630, x_3);
x_633 = lean_unbox(x_631);
if (x_633 == 0)
{
uint8_t x_634; 
x_634 = lean_unbox(x_632);
if (x_634 == 0)
{
x_607 = x_627;
goto block_618;
}
else
{
uint8_t x_635; 
x_635 = lean_unbox(x_631);
x_620 = x_635;
x_621 = x_627;
goto block_626;
}
}
else
{
uint8_t x_636; 
x_636 = lean_unbox(x_632);
if (x_636 == 0)
{
uint8_t x_637; 
x_637 = lean_unbox(x_631);
x_620 = x_637;
x_621 = x_627;
goto block_626;
}
else
{
x_607 = x_627;
goto block_618;
}
}
}
block_649:
{
lean_object* x_641; lean_object* x_642; lean_object* x_643; 
x_641 = l_Lake_PackageConfig_buildArchive___proj(x_1, x_2);
x_642 = lean_ctor_get(x_641, 0);
lean_inc(x_642);
lean_dec_ref(x_641);
lean_inc_ref(x_3);
x_643 = lean_apply_1(x_642, x_3);
if (lean_obj_tag(x_643) == 0)
{
x_627 = x_640;
goto block_638;
}
else
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; 
x_644 = lean_ctor_get(x_643, 0);
lean_inc(x_644);
lean_dec_ref(x_643);
x_645 = lean_box(0);
x_646 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_646, 0, x_645);
lean_ctor_set(x_646, 1, x_644);
x_647 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_648 = l_Lake_Toml_RBDict_insert___redArg(x_647, x_639, x_646, x_640);
x_627 = x_648;
goto block_638;
}
}
block_660:
{
lean_object* x_652; lean_object* x_653; lean_object* x_654; 
x_652 = l_Lake_PackageConfig_releaseRepo___proj(x_1, x_2);
x_653 = lean_ctor_get(x_652, 0);
lean_inc(x_653);
lean_dec_ref(x_652);
lean_inc_ref(x_3);
x_654 = lean_apply_1(x_653, x_3);
if (lean_obj_tag(x_654) == 0)
{
x_640 = x_651;
goto block_649;
}
else
{
lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; 
x_655 = lean_ctor_get(x_654, 0);
lean_inc(x_655);
lean_dec_ref(x_654);
x_656 = lean_box(0);
x_657 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_657, 0, x_656);
lean_ctor_set(x_657, 1, x_655);
x_658 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_659 = l_Lake_Toml_RBDict_insert___redArg(x_658, x_650, x_657, x_651);
x_640 = x_659;
goto block_649;
}
}
block_676:
{
lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; uint8_t x_670; 
x_663 = l_Lake_PackageConfig_irDir___proj(x_1, x_2);
x_664 = lean_ctor_get(x_663, 0);
lean_inc(x_664);
x_665 = lean_ctor_get(x_663, 3);
lean_inc(x_665);
lean_dec_ref(x_663);
lean_inc_ref(x_3);
x_666 = lean_apply_1(x_664, x_3);
lean_inc_ref(x_3);
x_667 = lean_apply_1(x_665, x_3);
lean_inc_ref(x_666);
x_668 = l_System_FilePath_normalize(x_666);
x_669 = l_System_FilePath_normalize(x_667);
x_670 = lean_string_dec_eq(x_668, x_669);
lean_dec_ref(x_669);
lean_dec_ref(x_668);
if (x_670 == 0)
{
lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; 
x_671 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_672 = l_Lake_mkRelPathString(x_666);
x_673 = lean_box(0);
x_674 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_674, 0, x_673);
lean_ctor_set(x_674, 1, x_672);
x_675 = l_Lake_Toml_RBDict_insert___redArg(x_671, x_661, x_674, x_662);
x_651 = x_675;
goto block_660;
}
else
{
lean_dec_ref(x_666);
x_651 = x_662;
goto block_660;
}
}
block_692:
{
lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; uint8_t x_686; 
x_679 = l_Lake_PackageConfig_binDir___proj(x_1, x_2);
x_680 = lean_ctor_get(x_679, 0);
lean_inc(x_680);
x_681 = lean_ctor_get(x_679, 3);
lean_inc(x_681);
lean_dec_ref(x_679);
lean_inc_ref(x_3);
x_682 = lean_apply_1(x_680, x_3);
lean_inc_ref(x_3);
x_683 = lean_apply_1(x_681, x_3);
lean_inc_ref(x_682);
x_684 = l_System_FilePath_normalize(x_682);
x_685 = l_System_FilePath_normalize(x_683);
x_686 = lean_string_dec_eq(x_684, x_685);
lean_dec_ref(x_685);
lean_dec_ref(x_684);
if (x_686 == 0)
{
lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; 
x_687 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_688 = l_Lake_mkRelPathString(x_682);
x_689 = lean_box(0);
x_690 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_690, 0, x_689);
lean_ctor_set(x_690, 1, x_688);
x_691 = l_Lake_Toml_RBDict_insert___redArg(x_687, x_677, x_690, x_678);
x_662 = x_691;
goto block_676;
}
else
{
lean_dec_ref(x_682);
x_662 = x_678;
goto block_676;
}
}
block_708:
{
lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; uint8_t x_702; 
x_695 = l_Lake_PackageConfig_nativeLibDir___proj(x_1, x_2);
x_696 = lean_ctor_get(x_695, 0);
lean_inc(x_696);
x_697 = lean_ctor_get(x_695, 3);
lean_inc(x_697);
lean_dec_ref(x_695);
lean_inc_ref(x_3);
x_698 = lean_apply_1(x_696, x_3);
lean_inc_ref(x_3);
x_699 = lean_apply_1(x_697, x_3);
lean_inc_ref(x_698);
x_700 = l_System_FilePath_normalize(x_698);
x_701 = l_System_FilePath_normalize(x_699);
x_702 = lean_string_dec_eq(x_700, x_701);
lean_dec_ref(x_701);
lean_dec_ref(x_700);
if (x_702 == 0)
{
lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; 
x_703 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_704 = l_Lake_mkRelPathString(x_698);
x_705 = lean_box(0);
x_706 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_706, 0, x_705);
lean_ctor_set(x_706, 1, x_704);
x_707 = l_Lake_Toml_RBDict_insert___redArg(x_703, x_693, x_706, x_694);
x_678 = x_707;
goto block_692;
}
else
{
lean_dec_ref(x_698);
x_678 = x_694;
goto block_692;
}
}
block_724:
{
lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; uint8_t x_718; 
x_711 = l_Lake_PackageConfig_leanLibDir___proj(x_1, x_2);
x_712 = lean_ctor_get(x_711, 0);
lean_inc(x_712);
x_713 = lean_ctor_get(x_711, 3);
lean_inc(x_713);
lean_dec_ref(x_711);
lean_inc_ref(x_3);
x_714 = lean_apply_1(x_712, x_3);
lean_inc_ref(x_3);
x_715 = lean_apply_1(x_713, x_3);
lean_inc_ref(x_714);
x_716 = l_System_FilePath_normalize(x_714);
x_717 = l_System_FilePath_normalize(x_715);
x_718 = lean_string_dec_eq(x_716, x_717);
lean_dec_ref(x_717);
lean_dec_ref(x_716);
if (x_718 == 0)
{
lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; 
x_719 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_720 = l_Lake_mkRelPathString(x_714);
x_721 = lean_box(0);
x_722 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_722, 0, x_721);
lean_ctor_set(x_722, 1, x_720);
x_723 = l_Lake_Toml_RBDict_insert___redArg(x_719, x_709, x_722, x_710);
x_694 = x_723;
goto block_708;
}
else
{
lean_dec_ref(x_714);
x_694 = x_710;
goto block_708;
}
}
block_740:
{
lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; uint8_t x_734; 
x_727 = l_Lake_PackageConfig_buildDir___proj(x_1, x_2);
x_728 = lean_ctor_get(x_727, 0);
lean_inc(x_728);
x_729 = lean_ctor_get(x_727, 3);
lean_inc(x_729);
lean_dec_ref(x_727);
lean_inc_ref(x_3);
x_730 = lean_apply_1(x_728, x_3);
lean_inc_ref(x_3);
x_731 = lean_apply_1(x_729, x_3);
lean_inc_ref(x_730);
x_732 = l_System_FilePath_normalize(x_730);
x_733 = l_System_FilePath_normalize(x_731);
x_734 = lean_string_dec_eq(x_732, x_733);
lean_dec_ref(x_733);
lean_dec_ref(x_732);
if (x_734 == 0)
{
lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; 
x_735 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_736 = l_Lake_mkRelPathString(x_730);
x_737 = lean_box(0);
x_738 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_738, 0, x_737);
lean_ctor_set(x_738, 1, x_736);
x_739 = l_Lake_Toml_RBDict_insert___redArg(x_735, x_725, x_738, x_726);
x_710 = x_739;
goto block_724;
}
else
{
lean_dec_ref(x_730);
x_710 = x_726;
goto block_724;
}
}
block_756:
{
lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; uint8_t x_750; 
x_743 = l_Lake_PackageConfig_srcDir___proj(x_1, x_2);
x_744 = lean_ctor_get(x_743, 0);
lean_inc(x_744);
x_745 = lean_ctor_get(x_743, 3);
lean_inc(x_745);
lean_dec_ref(x_743);
lean_inc_ref(x_3);
x_746 = lean_apply_1(x_744, x_3);
lean_inc_ref(x_3);
x_747 = lean_apply_1(x_745, x_3);
lean_inc_ref(x_746);
x_748 = l_System_FilePath_normalize(x_746);
x_749 = l_System_FilePath_normalize(x_747);
x_750 = lean_string_dec_eq(x_748, x_749);
lean_dec_ref(x_749);
lean_dec_ref(x_748);
if (x_750 == 0)
{
lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; 
x_751 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_752 = l_Lake_mkRelPathString(x_746);
x_753 = lean_box(0);
x_754 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_754, 0, x_753);
lean_ctor_set(x_754, 1, x_752);
x_755 = l_Lake_Toml_RBDict_insert___redArg(x_751, x_741, x_754, x_742);
x_726 = x_755;
goto block_740;
}
else
{
lean_dec_ref(x_746);
x_726 = x_742;
goto block_740;
}
}
block_767:
{
lean_object* x_760; lean_object* x_761; size_t x_762; size_t x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; 
x_760 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_761 = lean_box(0);
x_762 = lean_array_size(x_759);
x_763 = 0;
x_764 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_StrPatDescr_toToml_spec__0(x_762, x_763, x_759);
x_765 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_765, 0, x_761);
lean_ctor_set(x_765, 1, x_764);
x_766 = l_Lake_Toml_RBDict_insert___redArg(x_760, x_757, x_765, x_758);
x_742 = x_766;
goto block_756;
}
block_778:
{
lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; uint8_t x_776; 
x_769 = l_Lake_PackageConfig_moreGlobalServerArgs___proj(x_1, x_2);
x_770 = lean_ctor_get(x_769, 0);
lean_inc(x_770);
x_771 = lean_ctor_get(x_769, 3);
lean_inc(x_771);
lean_dec_ref(x_769);
lean_inc_ref(x_3);
x_772 = lean_apply_1(x_770, x_3);
lean_inc_ref(x_3);
x_773 = lean_apply_1(x_771, x_3);
x_774 = lean_array_get_size(x_772);
x_775 = lean_array_get_size(x_773);
x_776 = lean_nat_dec_eq(x_774, x_775);
if (x_776 == 0)
{
lean_dec_ref(x_773);
x_758 = x_768;
x_759 = x_772;
goto block_767;
}
else
{
uint8_t x_777; 
x_777 = l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanConfig_toToml_spec__1___redArg(x_772, x_773, x_774);
lean_dec_ref(x_773);
if (x_777 == 0)
{
x_758 = x_768;
x_759 = x_772;
goto block_767;
}
else
{
lean_dec_ref(x_772);
x_742 = x_768;
goto block_756;
}
}
}
block_786:
{
lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; 
x_782 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_783 = lean_box(0);
x_784 = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(x_784, 0, x_783);
lean_ctor_set_uint8(x_784, sizeof(void*)*1, x_780);
x_785 = l_Lake_Toml_RBDict_insert___redArg(x_782, x_779, x_784, x_781);
x_768 = x_785;
goto block_778;
}
block_798:
{
lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; uint8_t x_793; 
x_788 = l_Lake_PackageConfig_precompileModules___proj(x_1, x_2);
x_789 = lean_ctor_get(x_788, 0);
lean_inc(x_789);
x_790 = lean_ctor_get(x_788, 3);
lean_inc(x_790);
lean_dec_ref(x_788);
lean_inc_ref(x_3);
x_791 = lean_apply_1(x_789, x_3);
lean_inc_ref(x_3);
x_792 = lean_apply_1(x_790, x_3);
x_793 = lean_unbox(x_791);
if (x_793 == 0)
{
uint8_t x_794; 
x_794 = lean_unbox(x_792);
if (x_794 == 0)
{
x_768 = x_787;
goto block_778;
}
else
{
uint8_t x_795; 
x_795 = lean_unbox(x_791);
x_780 = x_795;
x_781 = x_787;
goto block_786;
}
}
else
{
uint8_t x_796; 
x_796 = lean_unbox(x_792);
if (x_796 == 0)
{
uint8_t x_797; 
x_797 = lean_unbox(x_791);
x_780 = x_797;
x_781 = x_787;
goto block_786;
}
else
{
x_768 = x_787;
goto block_778;
}
}
}
block_809:
{
lean_object* x_802; lean_object* x_803; size_t x_804; size_t x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; 
x_802 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_803 = lean_box(0);
x_804 = lean_array_size(x_800);
x_805 = 0;
x_806 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml_spec__1(x_804, x_805, x_800);
x_807 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_807, 0, x_803);
lean_ctor_set(x_807, 1, x_806);
x_808 = l_Lake_Toml_RBDict_insert___redArg(x_802, x_799, x_807, x_801);
x_787 = x_808;
goto block_798;
}
block_820:
{
lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; uint8_t x_818; 
x_811 = l_Lake_PackageConfig_extraDepTargets___proj(x_1, x_2);
x_812 = lean_ctor_get(x_811, 0);
lean_inc(x_812);
x_813 = lean_ctor_get(x_811, 3);
lean_inc(x_813);
lean_dec_ref(x_811);
lean_inc_ref(x_3);
x_814 = lean_apply_1(x_812, x_3);
lean_inc_ref(x_3);
x_815 = lean_apply_1(x_813, x_3);
x_816 = lean_array_get_size(x_814);
x_817 = lean_array_get_size(x_815);
x_818 = lean_nat_dec_eq(x_816, x_817);
if (x_818 == 0)
{
lean_dec_ref(x_815);
x_800 = x_814;
x_801 = x_810;
goto block_809;
}
else
{
uint8_t x_819; 
x_819 = l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml_spec__0___redArg(x_814, x_815, x_816);
lean_dec_ref(x_815);
if (x_819 == 0)
{
x_800 = x_814;
x_801 = x_810;
goto block_809;
}
else
{
lean_dec_ref(x_814);
x_787 = x_810;
goto block_798;
}
}
}
block_832:
{
lean_object* x_823; lean_object* x_824; lean_object* x_825; 
x_823 = l_Lake_PackageConfig_manifestFile___proj(x_1, x_2);
x_824 = lean_ctor_get(x_823, 0);
lean_inc(x_824);
lean_dec_ref(x_823);
lean_inc_ref(x_3);
x_825 = lean_apply_1(x_824, x_3);
if (lean_obj_tag(x_825) == 0)
{
x_810 = x_822;
goto block_820;
}
else
{
lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; 
x_826 = lean_ctor_get(x_825, 0);
lean_inc(x_826);
lean_dec_ref(x_825);
x_827 = l_Lake_mkRelPathString(x_826);
x_828 = lean_box(0);
x_829 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_829, 0, x_828);
lean_ctor_set(x_829, 1, x_827);
x_830 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_831 = l_Lake_Toml_RBDict_insert___redArg(x_830, x_821, x_829, x_822);
x_810 = x_831;
goto block_820;
}
}
block_845:
{
lean_object* x_842; uint8_t x_843; lean_object* x_844; 
x_842 = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(x_842, 0, x_838);
x_843 = lean_unbox(x_841);
lean_ctor_set_uint8(x_842, sizeof(void*)*1, x_843);
x_844 = l_Lake_Toml_RBDict_insert___redArg(x_835, x_833, x_842, x_840);
x_822 = x_844;
goto block_832;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml_spec__1___redArg(x_1, x_2, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_isEqvAux___at___00__private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_instToToml___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_box(0);
x_5 = lean_obj_once(&l_Lake_Toml_encodeLeanOptions___closed__0, &l_Lake_Toml_encodeLeanOptions___closed__0_once, _init_l_Lake_Toml_encodeLeanOptions___closed__0);
x_6 = l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml(x_1, x_2, x_3, x_5);
x_7 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_instToToml___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_instToToml___lam__0(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_instToToml(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_instToToml___lam__0___boxed), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_Package_mkTomlTargets___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 3);
lean_inc(x_6);
lean_dec_ref(x_3);
x_7 = lean_name_eq(x_5, x_1);
lean_dec(x_5);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_2);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_apply_2(x_2, x_4, x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_Package_mkTomlTargets___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_CLI_Translate_Toml_0__Lake_Package_mkTomlTargets___lam__0(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_Toml_0__Lake_Package_mkTomlTargets(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 13);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_alloc_closure((void*)(l___private_Lake_CLI_Translate_Toml_0__Lake_Package_mkTomlTargets___lam__0___boxed), 3, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_3);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get_size(x_4);
x_8 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_Package_mkTomlTargets___closed__9));
x_9 = l_Array_filterMapM___redArg(x_8, x_5, x_4, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__0_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_array_uget_borrowed(x_1, x_2);
x_12 = lean_ctor_get(x_11, 1);
x_13 = lean_ctor_get(x_11, 2);
x_14 = lean_ctor_get(x_11, 3);
x_15 = l_Lake_InputDir_keyword;
x_16 = lean_name_eq(x_13, x_15);
if (x_16 == 0)
{
x_5 = x_4;
goto block_9;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_obj_once(&l_Lake_Toml_encodeLeanOptions___closed__0, &l_Lake_Toml_encodeLeanOptions___closed__0_once, _init_l_Lake_Toml_encodeLeanOptions___closed__0);
lean_inc(x_14);
lean_inc(x_12);
x_18 = l___private_Lake_CLI_Translate_Toml_0__Lake_InputDirConfig_toToml(x_12, x_14, x_17);
x_19 = lean_array_push(x_4, x_18);
x_5 = x_19;
goto block_9;
}
}
else
{
return x_4;
}
block_9:
{
size_t x_6; size_t x_7; 
x_6 = 1;
x_7 = lean_usize_add(x_2, x_6);
x_2 = x_7;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__0_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__0___closed__0));
x_5 = lean_nat_dec_lt(x_2, x_3);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_le(x_3, x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_2, x_6);
if (x_8 == 0)
{
return x_4;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_usize_of_nat(x_2);
x_10 = lean_usize_of_nat(x_6);
x_11 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__0_spec__0(x_1, x_9, x_10, x_4);
return x_11;
}
}
else
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_usize_of_nat(x_2);
x_13 = lean_usize_of_nat(x_3);
x_14 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__0_spec__0(x_1, x_12, x_13, x_4);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__2_spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_array_uget_borrowed(x_1, x_2);
x_12 = lean_ctor_get(x_11, 1);
x_13 = lean_ctor_get(x_11, 2);
x_14 = lean_ctor_get(x_11, 3);
x_15 = l_Lake_InputFile_keyword;
x_16 = lean_name_eq(x_13, x_15);
if (x_16 == 0)
{
x_5 = x_4;
goto block_9;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_obj_once(&l_Lake_Toml_encodeLeanOptions___closed__0, &l_Lake_Toml_encodeLeanOptions___closed__0_once, _init_l_Lake_Toml_encodeLeanOptions___closed__0);
lean_inc(x_14);
lean_inc(x_12);
x_18 = l___private_Lake_CLI_Translate_Toml_0__Lake_InputFileConfig_toToml(x_12, x_14, x_17);
x_19 = lean_array_push(x_4, x_18);
x_5 = x_19;
goto block_9;
}
}
else
{
return x_4;
}
block_9:
{
size_t x_6; size_t x_7; 
x_6 = 1;
x_7 = lean_usize_add(x_2, x_6);
x_2 = x_7;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__2_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__2_spec__3(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__0___closed__0));
x_5 = lean_nat_dec_lt(x_2, x_3);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_le(x_3, x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_2, x_6);
if (x_8 == 0)
{
return x_4;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_usize_of_nat(x_2);
x_10 = lean_usize_of_nat(x_6);
x_11 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__2_spec__3(x_1, x_9, x_10, x_4);
return x_11;
}
}
else
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_usize_of_nat(x_2);
x_13 = lean_usize_of_nat(x_3);
x_14 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__2_spec__3(x_1, x_12, x_13, x_4);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__2(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__4_spec__7(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_array_uget_borrowed(x_1, x_2);
x_12 = lean_ctor_get(x_11, 1);
x_13 = lean_ctor_get(x_11, 2);
x_14 = lean_ctor_get(x_11, 3);
x_15 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__4_spec__7___closed__1));
x_16 = lean_name_eq(x_13, x_15);
if (x_16 == 0)
{
x_5 = x_4;
goto block_9;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_obj_once(&l_Lake_Toml_encodeLeanOptions___closed__0, &l_Lake_Toml_encodeLeanOptions___closed__0_once, _init_l_Lake_Toml_encodeLeanOptions___closed__0);
lean_inc(x_14);
lean_inc(x_12);
x_18 = l___private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml(x_12, x_14, x_17);
x_19 = lean_array_push(x_4, x_18);
x_5 = x_19;
goto block_9;
}
}
else
{
return x_4;
}
block_9:
{
size_t x_6; size_t x_7; 
x_6 = 1;
x_7 = lean_usize_add(x_2, x_6);
x_2 = x_7;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__4_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__4_spec__7(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__0___closed__0));
x_5 = lean_nat_dec_lt(x_2, x_3);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_le(x_3, x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_2, x_6);
if (x_8 == 0)
{
return x_4;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_usize_of_nat(x_2);
x_10 = lean_usize_of_nat(x_6);
x_11 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__4_spec__7(x_1, x_9, x_10, x_4);
return x_11;
}
}
else
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_usize_of_nat(x_2);
x_13 = lean_usize_of_nat(x_3);
x_14 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__4_spec__7(x_1, x_12, x_13, x_4);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__4(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_mkTomlConfig_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_5 = lean_box(0);
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_6);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_8, x_2, x_9);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_mkTomlConfig_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_mkTomlConfig_spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_mkTomlConfig_spec__5(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_box(0);
x_9 = lean_obj_once(&l_Lake_Toml_encodeLeanOptions___closed__0, &l_Lake_Toml_encodeLeanOptions___closed__0_once, _init_l_Lake_Toml_encodeLeanOptions___closed__0);
x_10 = l_Lake_Dependency_toToml(x_5, x_9);
x_11 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_14 = lean_array_uset(x_7, x_2, x_11);
x_2 = x_13;
x_3 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_mkTomlConfig_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_mkTomlConfig_spec__5(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__3_spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_array_uget_borrowed(x_1, x_2);
x_12 = lean_ctor_get(x_11, 1);
x_13 = lean_ctor_get(x_11, 2);
x_14 = lean_ctor_get(x_11, 3);
x_15 = l_Lake_LeanExe_keyword;
x_16 = lean_name_eq(x_13, x_15);
if (x_16 == 0)
{
x_5 = x_4;
goto block_9;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_obj_once(&l_Lake_Toml_encodeLeanOptions___closed__0, &l_Lake_Toml_encodeLeanOptions___closed__0_once, _init_l_Lake_Toml_encodeLeanOptions___closed__0);
lean_inc(x_14);
lean_inc(x_12);
x_18 = l___private_Lake_CLI_Translate_Toml_0__Lake_LeanExeConfig_toToml(x_12, x_14, x_17);
x_19 = lean_array_push(x_4, x_18);
x_5 = x_19;
goto block_9;
}
}
else
{
return x_4;
}
block_9:
{
size_t x_6; size_t x_7; 
x_6 = 1;
x_7 = lean_usize_add(x_2, x_6);
x_2 = x_7;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__3_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__3_spec__5(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__0___closed__0));
x_5 = lean_nat_dec_lt(x_2, x_3);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_le(x_3, x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_2, x_6);
if (x_8 == 0)
{
return x_4;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_usize_of_nat(x_2);
x_10 = lean_usize_of_nat(x_6);
x_11 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__3_spec__5(x_1, x_9, x_10, x_4);
return x_11;
}
}
else
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_usize_of_nat(x_2);
x_13 = lean_usize_of_nat(x_3);
x_14 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__3_spec__5(x_1, x_12, x_13, x_4);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__3(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_mkTomlConfig(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_41; lean_object* x_42; uint8_t x_43; uint8_t x_125; 
x_3 = lean_ctor_get(x_1, 6);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 3);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 12);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_1, 13);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_1, 15);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_1, 20);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_1, 21);
lean_inc_ref(x_10);
lean_dec_ref(x_1);
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get_uint8(x_3, sizeof(void*)*27);
x_14 = lean_ctor_get(x_3, 2);
x_15 = lean_ctor_get(x_3, 3);
x_16 = lean_ctor_get_uint8(x_3, sizeof(void*)*27 + 1);
x_17 = lean_ctor_get(x_3, 4);
x_18 = lean_ctor_get(x_3, 5);
x_19 = lean_ctor_get(x_3, 6);
x_20 = lean_ctor_get(x_3, 7);
x_21 = lean_ctor_get(x_3, 8);
x_22 = lean_ctor_get(x_3, 9);
x_23 = lean_ctor_get(x_3, 10);
x_24 = lean_ctor_get(x_3, 11);
x_25 = lean_ctor_get(x_3, 12);
x_26 = lean_ctor_get_uint8(x_3, sizeof(void*)*27 + 2);
x_27 = lean_ctor_get(x_3, 14);
x_28 = lean_ctor_get(x_3, 16);
x_29 = lean_ctor_get(x_3, 17);
x_30 = lean_ctor_get(x_3, 18);
x_31 = lean_ctor_get(x_3, 19);
x_32 = lean_ctor_get(x_3, 20);
x_33 = lean_ctor_get(x_3, 21);
x_34 = lean_ctor_get(x_3, 22);
x_35 = lean_ctor_get(x_3, 23);
x_36 = lean_ctor_get(x_3, 24);
x_37 = lean_ctor_get_uint8(x_3, sizeof(void*)*27 + 3);
x_38 = lean_ctor_get(x_3, 25);
x_39 = lean_ctor_get(x_3, 26);
x_40 = lean_ctor_get_uint8(x_3, sizeof(void*)*27 + 4);
x_41 = lean_ctor_get_uint8(x_3, sizeof(void*)*27 + 5);
x_125 = !lean_is_exclusive(x_3);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_3, 15);
lean_dec(x_126);
x_127 = lean_ctor_get(x_3, 13);
lean_dec(x_127);
x_42 = x_3;
x_43 = x_125;
goto block_124;
}
else
{
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_42 = lean_box(0);
x_43 = x_125;
goto block_124;
}
block_124:
{
lean_object* x_44; 
if (x_43 == 0)
{
lean_ctor_set(x_42, 15, x_10);
lean_ctor_set(x_42, 13, x_9);
x_44 = x_42;
goto block_122;
}
else
{
lean_object* x_123; 
x_123 = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(x_123, 0, x_11);
lean_ctor_set(x_123, 1, x_12);
lean_ctor_set(x_123, 2, x_14);
lean_ctor_set(x_123, 3, x_15);
lean_ctor_set(x_123, 4, x_17);
lean_ctor_set(x_123, 5, x_18);
lean_ctor_set(x_123, 6, x_19);
lean_ctor_set(x_123, 7, x_20);
lean_ctor_set(x_123, 8, x_21);
lean_ctor_set(x_123, 9, x_22);
lean_ctor_set(x_123, 10, x_23);
lean_ctor_set(x_123, 11, x_24);
lean_ctor_set(x_123, 12, x_25);
lean_ctor_set(x_123, 13, x_9);
lean_ctor_set(x_123, 14, x_27);
lean_ctor_set(x_123, 15, x_10);
lean_ctor_set(x_123, 16, x_28);
lean_ctor_set(x_123, 17, x_29);
lean_ctor_set(x_123, 18, x_30);
lean_ctor_set(x_123, 19, x_31);
lean_ctor_set(x_123, 20, x_32);
lean_ctor_set(x_123, 21, x_33);
lean_ctor_set(x_123, 22, x_34);
lean_ctor_set(x_123, 23, x_35);
lean_ctor_set(x_123, 24, x_36);
lean_ctor_set(x_123, 25, x_38);
lean_ctor_set(x_123, 26, x_39);
lean_ctor_set_uint8(x_123, sizeof(void*)*27, x_13);
lean_ctor_set_uint8(x_123, sizeof(void*)*27 + 1, x_16);
lean_ctor_set_uint8(x_123, sizeof(void*)*27 + 2, x_26);
lean_ctor_set_uint8(x_123, sizeof(void*)*27 + 3, x_37);
lean_ctor_set_uint8(x_123, sizeof(void*)*27 + 4, x_40);
lean_ctor_set_uint8(x_123, sizeof(void*)*27 + 5, x_41);
x_44 = x_123;
goto block_122;
}
block_122:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_99; lean_object* x_100; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_45 = l_Lake_InputDir_keyword;
x_46 = lean_unsigned_to_nat(0u);
x_47 = lean_array_get_size(x_7);
x_48 = l_Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__0(x_7, x_46, x_47);
x_60 = l_Lake_InputFile_keyword;
x_61 = l_Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__2(x_7, x_46, x_47);
x_73 = l_Lake_LeanExe_keyword;
x_74 = l_Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__3(x_7, x_46, x_47);
x_86 = l_Lake_LeanLib_keyword;
x_87 = l_Array_filterMapM___at___00Lake_Package_mkTomlConfig_spec__4(x_7, x_46, x_47);
lean_dec_ref(x_7);
x_99 = ((lean_object*)(l_Lake_Package_mkTomlConfig___closed__1));
x_111 = l___private_Lake_CLI_Translate_Toml_0__Lake_PackageConfig_toToml(x_4, x_5, x_44, x_2);
lean_dec(x_4);
x_112 = lean_array_get_size(x_8);
x_113 = lean_nat_dec_eq(x_112, x_46);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; size_t x_117; size_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_114 = ((lean_object*)(l_Lake_Package_mkTomlConfig___closed__3));
x_115 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_116 = lean_box(0);
x_117 = lean_array_size(x_8);
x_118 = 0;
x_119 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_Toml_0__Lake_LeanLibConfig_toToml_spec__1(x_117, x_118, x_8);
x_120 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_120, 0, x_116);
lean_ctor_set(x_120, 1, x_119);
x_121 = l_Lake_Toml_RBDict_insert___redArg(x_115, x_114, x_120, x_111);
x_100 = x_121;
goto block_110;
}
else
{
lean_dec_ref(x_8);
x_100 = x_111;
goto block_110;
}
block_59:
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_array_get_size(x_48);
x_51 = lean_nat_dec_eq(x_50, x_46);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; size_t x_54; size_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_52 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_53 = lean_box(0);
x_54 = lean_array_size(x_48);
x_55 = 0;
x_56 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_mkTomlConfig_spec__1(x_54, x_55, x_48);
x_57 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_57, 0, x_53);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lake_Toml_RBDict_insert___redArg(x_52, x_45, x_57, x_49);
return x_58;
}
else
{
lean_dec_ref(x_48);
return x_49;
}
}
block_72:
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_array_get_size(x_61);
x_64 = lean_nat_dec_eq(x_63, x_46);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; size_t x_67; size_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_65 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_66 = lean_box(0);
x_67 = lean_array_size(x_61);
x_68 = 0;
x_69 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_mkTomlConfig_spec__1(x_67, x_68, x_61);
x_70 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_70, 0, x_66);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_Lake_Toml_RBDict_insert___redArg(x_65, x_60, x_70, x_62);
x_49 = x_71;
goto block_59;
}
else
{
lean_dec_ref(x_61);
x_49 = x_62;
goto block_59;
}
}
block_85:
{
lean_object* x_76; uint8_t x_77; 
x_76 = lean_array_get_size(x_74);
x_77 = lean_nat_dec_eq(x_76, x_46);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; size_t x_80; size_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_78 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_79 = lean_box(0);
x_80 = lean_array_size(x_74);
x_81 = 0;
x_82 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_mkTomlConfig_spec__1(x_80, x_81, x_74);
x_83 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_83, 0, x_79);
lean_ctor_set(x_83, 1, x_82);
x_84 = l_Lake_Toml_RBDict_insert___redArg(x_78, x_73, x_83, x_75);
x_62 = x_84;
goto block_72;
}
else
{
lean_dec_ref(x_74);
x_62 = x_75;
goto block_72;
}
}
block_98:
{
lean_object* x_89; uint8_t x_90; 
x_89 = lean_array_get_size(x_87);
x_90 = lean_nat_dec_eq(x_89, x_46);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; size_t x_93; size_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_91 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_92 = lean_box(0);
x_93 = lean_array_size(x_87);
x_94 = 0;
x_95 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_mkTomlConfig_spec__1(x_93, x_94, x_87);
x_96 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_96, 0, x_92);
lean_ctor_set(x_96, 1, x_95);
x_97 = l_Lake_Toml_RBDict_insert___redArg(x_91, x_86, x_96, x_88);
x_75 = x_97;
goto block_85;
}
else
{
lean_dec_ref(x_87);
x_75 = x_88;
goto block_85;
}
}
block_110:
{
lean_object* x_101; uint8_t x_102; 
x_101 = lean_array_get_size(x_6);
x_102 = lean_nat_dec_eq(x_101, x_46);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; size_t x_105; size_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_103 = ((lean_object*)(l___private_Lake_CLI_Translate_Toml_0__Lake_instInsertFieldOfEncodeFieldOfBEqOfConfigField___redArg___lam__0___closed__0));
x_104 = lean_box(0);
x_105 = lean_array_size(x_6);
x_106 = 0;
x_107 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_mkTomlConfig_spec__5(x_105, x_106, x_6);
x_108 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_108, 0, x_104);
lean_ctor_set(x_108, 1, x_107);
x_109 = l_Lake_Toml_RBDict_insert___redArg(x_103, x_99, x_108, x_100);
x_88 = x_109;
goto block_98;
}
else
{
lean_dec_ref(x_6);
x_88 = x_100;
goto block_98;
}
}
}
}
}
}
lean_object* runtime_initialize_Lake_Toml_Encode(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Package(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_CLI_Translate_Toml(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lake_Toml_Encode(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Package(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lake_Config_LeanLibConfig(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_LeanExeConfig(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_InputFileConfig(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_PackageConfig(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_CLI_Translate_Toml(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lake_Config_LeanLibConfig(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_LeanExeConfig(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_InputFileConfig(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_PackageConfig(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Toml_Encode(uint8_t builtin);
lean_object* initialize_Lake_Config_Package(uint8_t builtin);
lean_object* initialize_Lake_Config_LeanLibConfig(uint8_t builtin);
lean_object* initialize_Lake_Config_LeanExeConfig(uint8_t builtin);
lean_object* initialize_Lake_Config_InputFileConfig(uint8_t builtin);
lean_object* initialize_Lake_Config_PackageConfig(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_CLI_Translate_Toml(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Toml_Encode(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Package(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_LeanLibConfig(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_LeanExeConfig(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_InputFileConfig(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_PackageConfig(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_CLI_Translate_Toml(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_CLI_Translate_Toml(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_CLI_Translate_Toml(builtin);
}
#ifdef __cplusplus
}
#endif
